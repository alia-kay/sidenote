"""
Sidenote - a local MCP server for the Claude desktop app (Windows 11).

What it does:
  - Reads the text of Windows Live Captions (Win+Ctrl+L) in the background
  - Keeps a timestamped rolling transcript and auto-saves it to
    Documents\\Sidenote
  - Shows a small always-on-top overlay with Claude's latest suggestion,
    the tail of the live transcript, and a box to type questions
  - Live mode: Claude waits for questions typed in the overlay and
    answers there, so you never need to switch to the Claude app

Requirements:
  Windows:  pip install mcp uiautomation
  macOS:    pip install mcp pyobjc-framework-ApplicationServices pyobjc-framework-Cocoa
"""

import asyncio
import atexit
import datetime
import difflib
import logging
import os
import queue
import re
import sys
import threading
import time
from collections import deque
from multiprocessing.connection import Client, Listener

import tkinter as tk
import contextlib

IS_MAC = sys.platform == "darwin"
if IS_MAC:
    auto = None
else:
    import uiautomation as auto
try:  # mcp 2.x
    from mcp.server.mcpserver import MCPServer as FastMCP
except ImportError:  # mcp 1.x
    from mcp.server.fastmcp import FastMCP

# stdout is reserved for the MCP protocol: all logging goes to stderr
logging.basicConfig(stream=sys.stderr, level=logging.INFO,
                    format="%(asctime)s [sidenote] %(message)s")
log = logging.getLogger("sidenote")

POLL_SECONDS = 0.5
SAVE_DIR = os.path.join(os.path.expanduser("~"), "Documents", "Sidenote")
# Own-mic transcription on Mac (when the source is macOS Live Captions, which
# hears the others but not the user). Uses Claude's microphone permission.
MAC_MIC_ENABLED = True
CAPTIONS_WINDOW_CLASS = "LiveCaptionsDesktopWindow"
CAPTIONS_TEXT_ID = "CaptionsTextBlock"
WAIT_DEFAULT_SECONDS = 50       # how long one wait_for_question call listens
HISTORY_WAIT_SECONDS = 50       # ...when nothing is recording
WAIT_MAX_SECONDS = 55           # Claude's tool calls time out after about 60 s: stay below
HISTORY_IDLE_SECONDS = 15 * 60  # no question this long on Home/History -> IDLE
ENDED_GRACE_SECONDS = 15 * 60  # after End meeting, stay ready this long for a new one
CUE_DELAY_SECONDS = 4          # wait this long after a cue phrase (sentence may continue)
MIN_SCAN_GAP_SECONDS = 30      # at most one scan every 30 s
REGULAR_SCAN_SECONDS = 150     # safety-net scan when lots was said without cue phrases
PAUSED_AFTER_SECONDS = 120      # no wait call for this long = Sidenote paused
AUTOFILL_AFTER_SECONDS = 180    # auto title/agenda: once, after 3 min...
AUTOFILL_MIN_LINES = 30         # ...and 30 spoken lines (questions/answers not counted)
AUTOFILL_MIN_WORDS = 100        # ...or 100 spoken words (Live Captions lines run long)
REPEAT_WINDOW_SECONDS = 10      # skip a line that repeats (or is the tail of) one this recent
REPEAT_LONG_SECONDS = 60        # ...or this recent, when the repeat is 4+ words long
REPEAT_LONG_WORDS = 4
STALE_WORDS = 8                 # 8+ words found inside a line from the last...
STALE_SECONDS = 600             # ...10 min = old caption text read again: skip it
REVISION_MIN_WORDS = 6          # a 6+ word line that is...
REVISION_SIMILARITY = 0.8       # ...80% the same as one from the last...
REVISION_SECONDS = 20           # ...20 s is a corrected re-send: replace that line
REPLAY_MIN_WORDS = 6            # a 6+ word line already captured this meeting = replay
REPLAY_RUN_SECONDS = 5          # shorter repeats count as replay this soon after one
NOTE_PREFIXES = ("YOU ASKED:", "CLAUDE:", "MEETING ENDED")   # transcript lines nobody said

SENTENCE_SPLIT = re.compile(r"(?<=[.!?])\s+")

# Phrases that usually mean an action item, an agenda topic or an open question.
# Specific phrases only (everyday words like "will" or "should" fire far too often).
CUE_WORDS = re.compile(
    r"\b(need to|needs to|i'll|we'll|you'll|he'll|she'll|they'll|i will|we will|"
    r"let's|action items?|to-?do|follow[- ]?up|next steps?|deadline|due date|"
    r"by (monday|tuesday|wednesday|thursday|friday|tomorrow|next week|end of \w+)|"
    r"book a|schedule a|send (you|the|it|over)|take care of|assign|owner|responsible for|"
    r"agenda|on the list|let's discuss|we should discuss)\b|\b[A-Z][A-Z0-9]{1,9}-\d+\b",
    re.IGNORECASE)
TICKET_KEY = re.compile(r"\b([A-Z][A-Z0-9]{1,9}-\d{1,6})\b")


LC_NAME = "macOS Live Captions" if IS_MAC else "Windows Live Captions"
LC_SHORT = "Mac captions" if IS_MAC else "Windows captions"
LC_HINT = ("turn on Live Captions in System Settings > Accessibility" if IS_MAC
           else "press Win+Ctrl+L")


def uia_thread():
    """Windows needs UI Automation set up per thread; macOS needs nothing."""
    return auto.UIAutomationInitializerInThread() if auto else contextlib.nullcontext()


def norm(text):
    """Lowercase letters/digits only, so caption revisions compare equal."""
    return re.sub(r"[^\w]", "", text.lower())


# ---------------------------------------------------------------------------
# Transcript store
# ---------------------------------------------------------------------------
def safe_filename(text):
    text = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "", text).strip().rstrip(".")
    return re.sub(r"\s+", " ", text)[:80]


def parse_list(value, commas=True):
    """Accept a list, or text with one item per line / separated by ; or commas.
    commas=False (agenda items): split only on new lines and semicolons, so
    'vision, strategy, design' stays one item."""
    if isinstance(value, (list, tuple)):
        items = value
    else:
        text = str(value or "")
        if "\n" in text or ";" in text or not commas:
            items = re.split(r"\n|;", text)
        else:
            items = text.split(",")
    out = []
    for item in items:
        item = re.sub(r"^\s*(?:[-*\u2022]|\d+[.)])\s*", "", str(item)).strip()
        if item:
            out.append(item)
    return out


# ---------------------------------------------------------------------------
# Profile: what the user told us once (kept across meetings, never asked twice)
# ---------------------------------------------------------------------------
PROFILE_FILE = os.path.join(SAVE_DIR, "profile.json")
NAME_RANK = {"claude": 1, "meet": 2, "typed": 3}   # a better source may replace a name


class Profile:
    """Documents/Sidenote/profile.json: the user's name and role. Goals stay per
    meeting. Prepared for more fields later (e.g. a calendar account)."""

    def __init__(self):
        self.lock = threading.Lock()
        self.data = {"name": "", "name_source": "", "role": "", "name_asked": False}
        try:
            import json
            with open(PROFILE_FILE, encoding="utf-8") as f:
                self.data.update({k: v for k, v in json.load(f).items() if k in self.data})
        except Exception:
            pass

    def _save(self):
        try:
            import json
            os.makedirs(SAVE_DIR, exist_ok=True)
            tmp = PROFILE_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.data, f, indent=2, ensure_ascii=False)
            os.replace(tmp, PROFILE_FILE)
        except OSError as e:
            log.warning("Could not save profile: %s", e)

    @property
    def name(self):
        return self.data["name"]

    @property
    def role(self):
        return self.data["role"]

    def set_role(self, role):
        role = (role or "").strip()
        with self.lock:
            if role != self.data["role"]:
                self.data["role"] = role
                self._save()

    def set_name(self, name, source):
        """Save the user's name unless a more reliable source already set it.
        Returns True if the name changed. An empty typed name clears it."""
        name = " ".join(str(name or "").split()).strip(" .,:;")
        if name.lower() in SELF_WORDS | TEAM_WORDS | UNKNOWN_WORDS:
            name = ""
        with self.lock:
            if not name:
                if source == "typed" and self.data["name"]:
                    self.data.update(name="", name_source="")
                    self._save()
                    return True
                return False
            if name == self.data["name"]:
                return False
            if self.data["name"] and \
                    NAME_RANK.get(source, 0) < NAME_RANK.get(self.data["name_source"], 0):
                return False
            self.data.update(name=name, name_source=source)
            self._save()
        log.info("User's name set from %s", source)
        return True

    def mark_asked(self):
        with self.lock:
            if not self.data["name_asked"]:
                self.data["name_asked"] = True
                self._save()


# The user's own display name in Google Meet, when a label shows it
# ("Iman Kay (You)" in the people list, "Google Account: Iman Kay (...)").
MEET_SELF_LABELS = (re.compile(r"^(?:My video|\u041c\u043e\u0435 \u0432\u0438\u0434\u0435\u043e|Mon flux vid\u00e9o|"
                               r"Mi v\u00eddeo|Mi video|Mein Video|Il mio video|Meu v\u00eddeo),\s*([^,]{2,60}?)\s*,"),
                    re.compile(r"^(.{2,40}?)\s*\((?:Host, |Co-host, )?(?:You|you|me|Me)\)$"),
                    re.compile(r"^Google Account:\s*([^(\n]{2,40}?)\s*(?:\(|$)"))


SELF_ALIASES = set()   # the user's name as the meeting app shows it ('Alia Kayeshka')


def note_meet_label(label):
    """Called for each element while a reader walks a meeting window (best
    effort). The user's display name there becomes an alias for the user, so
    their caption lines count as theirs even if Sidenote calls them 'Alia'."""
    if not label or len(label) > 200:
        return
    for pattern in MEET_SELF_LABELS:
        m = pattern.match(label)
        if m and "@" not in m.group(1):
            name = " ".join(m.group(1).split())
            if name not in SELF_ALIASES:
                SELF_ALIASES.add(name)
                log.info("User's name in the meeting app noted")
            if profile.data["name_source"] not in ("typed", "meet"):
                set_user_name(name, "meet")
            return


def os_full_name():
    """The account's full name, only as a pre-filled guess for the name question."""
    try:
        if IS_MAC:
            import subprocess
            return subprocess.run(["id", "-F"], capture_output=True, text=True,
                                  timeout=2).stdout.strip()
        import ctypes
        size = ctypes.c_ulong(0)
        ctypes.windll.secur32.GetUserNameExW(3, None, ctypes.byref(size))   # 3 = display name
        buf = ctypes.create_unicode_buffer(size.value or 256)
        if ctypes.windll.secur32.GetUserNameExW(3, buf, ctypes.byref(size)):
            return buf.value.strip()
    except Exception:
        pass
    return ""


# Owners are always names: "you"/"me" become the user's name, team-wide items
# become "Team", and "someone" means unknown (shown as "Owner: ?").
SELF_WORDS = {"you", "me", "i", "myself", "yourself", "user", "the user", "my", "mine"}
TEAM_WORDS = {"team", "the team", "everyone", "everybody", "all", "we", "us",
              "all of us", "whole team", "the whole team", "both"}
UNKNOWN_WORDS = {"someone", "somebody", "anyone", "anybody", "tbd", "unknown", "?",
                 "n/a", "na", "none", "unassigned", "owner"}
SELF = "@me"          # stored owner for the user while their name is unknown

# Finding a task's owner in the transcript (Transcript.guess_owner)
OWNER_STOPWORDS = {
    "the", "and", "for", "you", "can", "will", "with", "this", "that", "please", "could",
    "would", "okay", "ok", "so", "yeah", "right", "hey", "hi", "alright", "also", "then",
    "now", "well", "yes", "no", "maybe", "just", "let", "need", "needs", "should", "have",
    "has", "our", "your", "their", "from", "into", "about", "what", "when", "who", "how",
    "why", "there", "here", "all", "are", "was", "were", "its", "it's", "we", "they",
    "them", "him", "her", "his", "she", "he", "i'll", "me", "my", "make", "sure", "do",
    "does", "did", "get", "got", "and", "but", "if", "or", "guys", "everyone", "team"}
# "Leon, can you check staging" / "Leon can you..."  (names are capitalized)
ADDRESSED = re.compile(r"(?:^|[.!?]\s+)(?:(?:[Oo]k(?:ay)?|[Ss]o|[Aa]nd|[Hh]ey|[Hh]i|[Rr]ight|"
                       r"[Yy]eah|[Aa]lright)[, ]+)?([A-Z][a-zA-Z'\-]{1,20}),?\s+"
                       r"(?:can|could|would|will|please|do)\s+you\b")
# "Can you check staging, Leon?"
ADDRESSED_END = re.compile(r"\b(?:[Cc]an|[Cc]ould|[Ww]ould|[Ww]ill) you\b[^.?!]*,\s*"
                           r"([A-Z][a-zA-Z'\-]{1,20})\s*[?.!]*\s*$")
# "I'll check staging" / "Let me take that" (the speaker owns it)
COMMITMENT = re.compile(r"\b(?:i'll|i will|i can|i'm going to|i am going to|let me|"
                        r"i'll take|i can take|leave it with me)\b", re.I)


def normalize_owner(owner):
    o = " ".join(str(owner or "").split()).strip(" .,:;")
    low = o.lower().rstrip("?").strip()
    if low in SELF_WORDS:
        return profile.name or SELF
    if low in TEAM_WORDS:
        return "Team"
    if low in UNKNOWN_WORDS or not low:
        return ""
    if profile.name and low == profile.name.lower():
        return profile.name
    return o


def owner_text(owner):
    """Owner as shown/saved: a name, or '' when unknown."""
    if owner == SELF:
        return profile.name or ""
    return owner


def _same_person(a, b):
    """'Aliaksandra Kayeshka' and 'Alia Kayeshka': same surname, and one first
    name starts with the other (at least 4 letters). Apps show the same person
    with a full or a short first name."""
    wa, wb = a.lower().split(), b.lower().split()
    if a.lower() == b.lower():
        return True
    if len(wa) < 2 or len(wb) < 2 or wa[-1] != wb[-1]:
        return False
    fa, fb = wa[0], wb[0]
    short, long_ = sorted((fa, fb), key=len)
    return len(short) >= 4 and long_.startswith(short)


def speaker_name(label):
    """Transcript speaker label with the user's own 'You' (or their display name
    in the meeting app) replaced by the name Sidenote uses for them."""
    if not profile.name or not label:
        return label
    if label in ("You", "you", "Me") or label in SELF_ALIASES:
        return profile.name
    if " " in label and any(_same_person(label, n) for n in SELF_ALIASES | {profile.name}):
        return profile.name
    return label


def display_line(line):
    """A transcript line with 'You: ...' (or the user's display name in the
    meeting app) shown as '<name>: ...'."""
    if profile.name:
        speaker, sep, rest = line.partition(": ")
        if sep and speaker_name(speaker) != speaker:
            return f"{profile.name}: {rest}"
    return line


# Real dates instead of "today" / "tomorrow" in what is saved
WEEKDAY_NAMES = ["monday", "tuesday", "wednesday", "thursday", "friday",
                 "saturday", "sunday"]


def fmt_day(d):
    """'Mon 9 Nov' (portable: no %-d)."""
    return f"{d:%a} {d.day} {d:%b}"


def real_dates(text, base, due=False):
    """Replace relative days with real dates, counted from the meeting's date.
    Free text: today, tonight, tomorrow, yesterday. Due dates (due=True) also:
    weekdays ('Friday', 'this Friday'), 'end of week', 'next week', 'end of
    month'. 'Next Friday' is left as said (it is ambiguous)."""
    if not text:
        return text
    if isinstance(base, datetime.datetime):
        base = base.date()
    one = datetime.timedelta(days=1)
    rules = [
        (r"\bday after tomorrow\b", lambda m: fmt_day(base + 2 * one)),
        (r"\b(?:today|tonight|this (?:morning|afternoon|evening))\b",
         lambda m: fmt_day(base)),
        (r"\btomorrow\b", lambda m: fmt_day(base + one)),
        (r"\byesterday\b", lambda m: fmt_day(base - one)),
    ]
    if due:
        def weekday(m):
            target = WEEKDAY_NAMES.index(m.group(1).lower())
            return fmt_day(base + ((target - base.weekday()) % 7) * one)
        friday = base + ((4 - base.weekday()) % 7) * one
        monday = base + (7 - base.weekday()) * one
        nxt = (base.replace(day=28) + 4 * one).replace(day=1)
        rules += [
            (r"\b(?:the )?end of (?:the |this )?week\b", lambda m: fmt_day(friday)),
            (r"\bnext week\b", lambda m: "week of " + fmt_day(monday)),
            (r"\b(?:the )?end of (?:the |this )?month\b", lambda m: fmt_day(nxt - one)),
            (r"(?<!next )\b(?:this |on |by )?(" + "|".join(WEEKDAY_NAMES) + r")\b", weekday),
            (r"^\s*(?:eod|end of (?:the )?day)\s*$", lambda m: fmt_day(base) + " EOD"),
        ]
    for pattern, repl in rules:
        text = re.sub(pattern, repl, text, flags=re.I)
    return text


EMPTY_CONTEXT = {"title": "", "subject": "", "role": "", "goals": "",
                 "participants": [], "agenda": [], "recap": "",
                 "by_person": "",    # recap: one block per person
                 "decisions": "",    # recap: decisions made
                 "open_debates": "", # recap: open questions and unresolved debates
                 "agenda_done": [],  # agenda items already covered (their text)
                 "actions": [],      # [{"text", "owner", "due", "done"}]
                 "questions": [],    # [{"text", "done"}]
                 "context": []}      # [{"title", "source", "detail", "url"}]


# Jira/Confluence context list (merged from sidenote_context_patch.py)
MAX_CONTEXT_ITEMS = 12      # hard cap per meeting, enforced in add_context
PRELOAD_MAX = 6             # items to add at the start of the meeting
MAX_PER_TOPIC = 2           # mid-meeting adds per new topic


def _same(a, b):
    return norm(a) == norm(b) or (len(norm(a)) > 12 and norm(a) in norm(b)) or \
        (len(norm(b)) > 12 and norm(b) in norm(a))


class Transcript:
    def __init__(self):
        self.lock = threading.Lock()
        self.status = "Waiting for captions"
        self.source = ""                  # "Google Meet" or "Windows Live Captions"
        self.source_note = ""             # e.g. why we switched source
        self.file_path = None
        self._reset()
        threading.Thread(target=self._writer_loop, daemon=True).start()

    def _reset(self):
        self.context = {k: (list(v) if isinstance(v, list) else v)
                        for k, v in EMPTY_CONTEXT.items()}
        self.context["role"] = profile.role   # the role carries over between meetings
        self.speakers = []                # names heard in Meet captions (not 'You')
        self.captured = set()             # (speaker, words) of every line this meeting
        self.replay_skipped = 0           # lines skipped because captions replayed them
        self._replay_at = None            # last time a replayed line was skipped
        self.ended_at = None              # set when the user ends the meeting
        self.cue_at = 0.0                 # last time a cue phrase was said
        self.others_recent = deque(maxlen=40)   # (time, key) of recent 'Others' lines
        self.tickets_seen = []            # ticket keys mentioned (e.g. ESP-142)
        self.tickets_new = []             # mentioned but not looked up yet
        self.context_dirty = True         # title/agenda changed: refresh context
        self.sources = getattr(self, "sources", None)   # kept across meetings
        self._last_key = ""
        self.skip_visible = True          # next read only marks on-screen captions as seen
        self.entries = []                 # list of (datetime, sentence)
        self.recent = deque(maxlen=400)   # normalized recent sentences
        self.recent_words = deque(maxlen=300)  # [datetime, speaker, words, entry index]
        self.last_final = None            # last sentence committed (raw)
        self.pending = ""                 # sentence still being spoken
        self.started = datetime.datetime.now()
        self.meeting_id = new_meeting_id(self.started)
        self.item_status = {}             # open question id -> status (answered/open)
        self.file_path = None             # chosen on first save
        self.dirty = False

    def new_meeting(self, title=""):
        self.save_now()                   # make sure the previous file is complete
        try:
            live.scanned_upto = 0
            live.quiet_rounds = 0
            live.last_scan = 0.0
            live.autofill_sent = False
        except NameError:
            pass
        with self.lock:
            self._reset()
            if title and title.lower() != "meeting":
                self.context["title"] = title.strip()
        return "New meeting started."

    # --- meeting info ----------------------------------------------------
    def update_context(self, title=None, subject=None, role=None, goals=None,
                       participants=None, agenda=None, recap=None):
        with self.lock:
            c = self.context
            for key, val in (("title", title), ("subject", subject), ("role", role),
                             ("goals", goals), ("recap", recap)):
                if val is not None and str(val).strip():
                    c[key] = str(val).strip()
            if role is not None and str(role).strip():
                profile.set_role(role)        # remembered for the next meetings
            if participants is not None and parse_list(participants):
                c["participants"] = parse_list(participants)
            if agenda is not None and parse_list(agenda, commas=False):
                c["agenda"] = parse_list(agenda, commas=False)
            if (title and str(title).strip()) or (agenda and parse_list(agenda, commas=False)):
                self.context_dirty = True
        self.save_now()

    def add_agenda_items(self, items):
        """Add agenda topics, skipping anything already on the agenda (even reworded)."""
        added = []
        with self.lock:
            for item in parse_list(items, commas=False):
                if not any(_same(item, a) for a in self.context["agenda"]):
                    self.context["agenda"].append(item)
                    added.append(item)
            if added:
                self.context_dirty = True
        self.save_now()
        return added

    def add_participants(self, names):
        new = parse_list(names)
        with self.lock:
            for name in new:
                if name not in self.context["participants"]:
                    self.context["participants"].append(name)
        self.save_now()
        return new

    def add_action(self, text, owner="", due=""):
        """Save an action item. The owner is always a name (see normalize_owner);
        when none is given, Sidenote looks for one in the transcript, and marks
        a weak guess as unsure ('Leon?'). Relative due dates become real dates."""
        text = text.strip()
        if not text:
            return False
        owner, sure = normalize_owner(owner), True
        if not owner:
            owner, sure = self.guess_owner(text)
        due = real_dates(due.strip(), self.started, due=True)
        when, _ = self._best_match(text)          # takes the lock itself: call it before
        with self.lock:
            for a in self.context["actions"]:
                if _same(a["text"], text):
                    if owner and (not a["owner"] or not a.get("sure", True)) and sure:
                        a["owner"], a["sure"] = owner, True
                    if due and not a["due"]:
                        a["due"] = due
                    self.dirty = True
                    return False
            self.context["actions"].append({
                "id": f"a{len(self.context['actions']) + 1}", "text": text, "owner": owner,
                "sure": sure, "due": due, "done": False, "created_in": self.meeting_id,
                "source_time": (when or datetime.datetime.now()).strftime("%H:%M:%S"),
                "closed_at": "", "closed_by": "", "close_evidence": ""})
            self.dirty = True
        return True

    def set_owner(self, index, owner):
        """The user picked an owner in the window."""
        with self.lock:
            items = self.context["actions"]
            if not 0 <= index < len(items):
                return False
            items[index]["owner"] = normalize_owner(owner)
            items[index]["sure"] = True
            self.dirty = True
        return True

    def apply_user_name(self):
        """The user's name became known: fill it in where we had to wait for it."""
        if not profile.name:
            return
        with self.lock:
            for a in self.context["actions"]:
                if a["owner"] == SELF:
                    a["owner"] = profile.name
            self.dirty = True

    def people(self):
        """Everyone in the meeting: participants, names heard in Meet, and the
        user (by name). Used for the owner picker and the recap's BY PERSON."""
        out = []
        for name in ([profile.name] if profile.name else []) + \
                list(self.context["participants"]) + list(self.speakers):
            name = speaker_name(name)
            if name and name not in ("Others", "You") and \
                    not any(name.lower() == n.lower() for n in out):
                out.append(name)
        return out

    def guess_owner(self, task):
        """Find who owns a task from the transcript, in this order: the speaker
        who committed ('I'll do X'), the person addressed ('Leon, can you...'),
        a known person named in that line (unsure). Returns (owner, sure)."""
        _, best = self._best_match(task)
        if not best:
            return "", True
        with self.lock:
            people = [p for p in self.people()]
        speaker, sep, said = best.partition(": ")
        if not sep or len(speaker) > 40:
            speaker, said = "", best
        speaker = speaker_name(speaker)
        m = ADDRESSED.search(said) or ADDRESSED_END.search(said)
        if m and m.group(1).lower() not in OWNER_STOPWORDS:
            name = m.group(1)                  # 'Dana' -> 'Dana Lee' when we know her
            full = [p for p in people if p.split()[0].lower() == name.lower()]
            return (full[0] if len(full) == 1 else name), True
        if COMMITMENT.search(said) and speaker and speaker != "Others":
            return normalize_owner(speaker if speaker not in ("You", "Me") else "me"), True
        for person in people:
            first = person.split()[0]
            if re.search(r"\b" + re.escape(first) + r"\b", said, re.I):
                return person, False
        return "", True

    def _best_match(self, task):
        """(time, line) of the transcript line that best matches a task, or (None, None)."""
        words = {w for w in re.findall(r"[a-z0-9']+", task.lower())
                 if len(w) > 2 and w not in OWNER_STOPWORDS}
        if not words:
            return None, None
        with self.lock:
            lines = [(t, s) for t, s in self.entries[-80:] if not s.startswith(NOTE_PREFIXES)]
        best, best_score = (None, None), 0
        for t, line in lines:                    # latest best match wins
            spoken = set(re.findall(r"[a-z0-9']+", line.lower()))
            score = len(words & spoken)
            if score >= min(2, len(words)) and score >= best_score:
                best, best_score = (t, line), score
        return best

    def add_question(self, text):
        text = text.strip()
        if not text:
            return False
        with self.lock:
            if any(_same(q["text"], text) for q in self.context["questions"]):
                return False
            self.context["questions"].append(
                {"id": f"t{len(self.context['questions']) + 1}", "text": text, "done": False})
            self.dirty = True
        return True

    def set_done(self, kind, index, done=True):
        with self.lock:
            if kind == "agenda":
                agenda = self.context["agenda"]
                if not 0 <= index < len(agenda):
                    return False
                item, covered = agenda[index], self.context["agenda_done"]
                if done and item not in covered:
                    covered.append(item)
                if not done and item in covered:
                    covered.remove(item)
                self.dirty = True
                return True
            items = self.context[kind]
            if 0 <= index < len(items):
                items[index]["done"] = done
                if kind == "actions":                 # ticked by the user in the window
                    items[index].update(
                        closed_at=datetime.datetime.now().isoformat(timespec="seconds")
                        if done else "", closed_by="user" if done else "", close_evidence="")
                self.dirty = True
                return True
        return False

    def update_item(self, kind, item_id, status, by, evidence=""):
        """update_item for the meeting being recorded (kept in memory, then saved)."""
        now = datetime.datetime.now().isoformat(timespec="seconds")
        with self.lock:
            if kind == "action":
                for a in self.context["actions"]:
                    if a.get("id") == item_id:
                        a["done"] = status == "done"
                        a.update(closed_at=now if a["done"] else "",
                                 closed_by=by if a["done"] else "",
                                 close_evidence=evidence if a["done"] and by == "claude" else "")
                        self.dirty = True
                        return a["text"]
                return None
            for q in self.context["questions"]:
                if q.get("id") == item_id:
                    q["done"] = status == "answered"
                    self.dirty = True
                    return q["text"]
            lines = [l for l in self.context["open_debates"].splitlines() if l.strip()]
            for i, line in enumerate(lines, 1):
                if f"q{i}" == item_id:
                    self.item_status[item_id] = status
                    self.dirty = True
                    return re.sub(r"^\s*-\s*", "", line).strip()
        return None

    def add_context(self, title, source="", detail="", url=""):
        """Returns 'added', 'updated' (already listed, by title or link),
        'full' (MAX_CONTEXT_ITEMS reached) or 'empty' (no title)."""
        title = title.strip()
        url = url.strip()
        if not title:
            return "empty"
        with self.lock:
            for c in self.context["context"]:
                if _same(c["title"], title) or (url and c["url"].strip().lower() == url.lower()):
                    if detail:
                        c["detail"] = detail.strip()
                    if url and not c["url"]:
                        c["url"] = url
                    self.dirty = True
                    return "updated"
            if len(self.context["context"]) >= MAX_CONTEXT_ITEMS:
                return "full"
            self.context["context"].append({"title": title, "source": source.strip(),
                                            "detail": detail.strip(), "url": url})
            self.dirty = True
        return "added"

    def context_slots_left(self):
        return MAX_CONTEXT_ITEMS - len(self.context["context"])

    def display_title(self):
        c = self.context
        return c["title"] or c["subject"] or ""

    # --- captions --------------------------------------------------------
    def end_meeting(self):
        with self.lock:
            if not self.ended_at:
                self.ended_at = datetime.datetime.now()
                self.entries.append((self.ended_at, "MEETING ENDED"))
        self.save_now()

    def ingest(self, raw_text, speaker="", final=False):
        """Take the current caption block and commit any newly finished sentences.
        speaker: label added in front of each line (e.g. 'Others' on Mac when your
        own microphone is transcribed separately). final=True: the block is done
        (e.g. Zoom replaced its caption line), so its last sentence is finished too."""
        if self.ended_at:
            return                        # meeting ended: stop recording
        text = " ".join(raw_text.split())
        if not text:
            return
        parts = SENTENCE_SPLIT.split(text)
        finals, pending = (parts, "") if final else (parts[:-1], parts[-1])

        with self.lock:
            if self.skip_visible:          # captions from before this meeting started
                self.skip_visible = False
                for sentence in parts:
                    self.recent.append(norm(sentence))
                self.last_final = finals[-1] if finals else None
                return
            if self.last_final and self.last_final in finals:
                # Everything after the last sentence we already have is new
                idx = len(finals) - 1 - finals[::-1].index(self.last_final)
                candidates = finals[idx + 1:]
            else:
                candidates = finals

            now = datetime.datetime.now()
            self._check_batch(now, speaker, candidates)
            for sentence in candidates:
                key = norm(sentence)
                if not key or key in self.recent:
                    continue        # duplicate or a punctuation-only revision
                self._commit(now, f"{speaker}: {sentence}" if speaker else sentence, key, speaker)
                self._note_cues(sentence)
                if speaker:
                    self.others_recent.append((time.time(), key))
            if candidates:
                self.last_final = candidates[-1]
            self.pending = f"{speaker}: {pending}" if (speaker and pending) else pending

    def add_spoken(self, speaker, text):
        """A phrase from Sidenote's own microphone transcription ('You')."""
        if self.ended_at:
            return False
        text = " ".join(text.split())
        key = norm(text)
        if len(key) < 3:
            return False
        now_t = time.time()
        with self.lock:
            # the mic can hear the others through the speakers: skip what Live
            # Captions already caught from the computer audio
            for t, k in list(self.others_recent):
                if now_t - t < 20 and (k in key or key in k or _same(k, key)):
                    return False
            now = datetime.datetime.now()
            for sentence in SENTENCE_SPLIT.split(text):
                k = norm(speaker + sentence)
                if norm(sentence) and k not in self.recent:
                    self._commit(now, f"{speaker}: {sentence}", k, speaker)
                    self._note_cues(sentence)
        return True

    def _is_repeat(self, now, speaker, words):
        """True if this line is a re-send of one already captured from the same
        speaker. Live Captions re-sends lines in two ways:
          - each copy shorter ('I also will review files', 'also will review
            files', ...): identical or the end of a line from the last
            REPEAT_WINDOW_SECONDS (REPEAT_LONG_SECONDS for 4+ words);
          - old text read again from its buffer minutes later: 8+ words found
            anywhere inside a line from the last STALE_SECONDS."""
        if not words:
            return False
        n = len(words)
        window = REPEAT_LONG_SECONDS if n >= REPEAT_LONG_WORDS else REPEAT_WINDOW_SECONDS
        for t, spk, prev, _ in self.recent_words:
            if spk != speaker or len(prev) < n:
                continue
            age = (now - t).total_seconds()
            if age <= window and prev[-n:] == words:
                return True
            if n >= STALE_WORDS and age <= STALE_SECONDS and any(
                    prev[i:i + n] == words for i in range(len(prev) - n + 1)):
                return True
        return False

    def _find_revision(self, now, speaker, words):
        """The recent line this one corrects, if any. Live Captions sometimes
        sends a finished line again a second later with a word changed ('fit all
        the pony' -> 'fit all a pony'). Only for lines of REVISION_MIN_WORDS+ words,
        REVISION_SIMILARITY alike, from the last REVISION_SECONDS."""
        if len(words) < REVISION_MIN_WORDS:
            return None
        for rec in reversed(self.recent_words):
            t, spk, prev, idx = rec
            if (now - t).total_seconds() > REVISION_SECONDS:
                break
            if spk == speaker and len(prev) >= REVISION_MIN_WORDS and \
                    difflib.SequenceMatcher(None, prev, words).ratio() >= REVISION_SIMILARITY:
                return rec
        return None

    def _is_replay(self, now, speaker, words):
        """Live Captions sometimes re-sends the whole conversation (thousands of
        lines). A line of REPLAY_MIN_WORDS+ words already captured this meeting
        is a replay; a shorter one is too while a replay is going on (seconds
        after another replayed line). Logged once per meeting."""
        if not words or (speaker, words) not in self.captured:
            return False
        replaying = self._replay_at is not None and \
            (now - self._replay_at).total_seconds() <= REPLAY_RUN_SECONDS
        if len(words) < REPLAY_MIN_WORDS and not replaying:
            return False
        if self.replay_skipped == 0:
            log.info("Captions replayed earlier lines: skipping them")
        self.replay_skipped += 1
        self._replay_at = now
        return True

    def _check_batch(self, now, speaker, sentences):
        """A batch of new caption lines that is mostly lines we already have is a
        replay as a whole, so its short lines ('Okay.', 'Hi.') are skipped too."""
        sigs = [(speaker, tuple(re.findall(r"\w+", s.lower()))) for s in sentences]
        sigs = [s for s in sigs if s[1]]
        seen = sum(1 for s in sigs if s in self.captured)
        if seen >= 3 and seen * 2 >= len(sigs):
            self._replay_at = now

    def _remember(self, speaker, words):
        """Note a captured line for replay detection, and who spoke (Meet names)."""
        if words:
            self.captured.add((speaker, words))
        if speaker and speaker not in ("Others", "You", "Me") and \
                speaker not in self.speakers and len(self.speakers) < 50:
            self.speakers.append(speaker)

    def _commit(self, now, line, key, speaker=""):
        """Add a finished sentence. If captions extended the previous sentence
        ('I added' -> 'I added X to the agenda') or corrected a recent one ('fit
        all the pony' -> 'fit all a pony'), replace it instead of adding a second
        copy. A shorter re-send, the tail end of a recent line, and old text read
        again from the captions buffer are skipped."""
        sentence = line[len(speaker) + 2:] if speaker else line
        words = tuple(re.findall(r"\w+", sentence.lower()))
        if self._is_repeat(now, speaker, words) or self._is_replay(now, speaker, words):
            self.recent.append(key)
            return False
        self._remember(speaker, words)
        rec = self._find_revision(now, speaker, words)
        if rec is not None and rec[3] < len(self.entries):
            idx = rec[3]
            self.entries[idx] = (self.entries[idx][0], line)   # keep the first time
            rec[2] = words
            if idx == len(self.entries) - 1:
                self._last_key = key
            self.recent.append(key)
            self.dirty = True
            return True
        last = self.entries[-1] if self.entries else None
        last_key = getattr(self, "_last_key", "")
        if last and last_key and (now - last[0]).total_seconds() < 20:
            if key.startswith(last_key) and len(key) > len(last_key):
                self.entries[-1] = (last[0], line)
                self._last_key = key
                self.recent.append(key)
                self.recent_words.append([now, speaker, words, len(self.entries) - 1])
                self.dirty = True
                return True
            if last_key.startswith(key):
                self.recent.append(key)
                return False
        self.entries.append((now, line))
        self._last_key = key
        self.recent.append(key)
        self.recent_words.append([now, speaker, words, len(self.entries) - 1])
        self.dirty = True
        return True

    def ingest_blocks(self, blocks):
        """Speaker-labelled captions (Google Meet): blocks = [(speaker, text), ...],
        oldest first. Finished sentences are committed as 'Speaker: sentence'."""
        if self.ended_at or not blocks:
            return
        now = datetime.datetime.now()
        with self.lock:
            if self.skip_visible:          # captions from before this meeting started
                self.skip_visible = False
                for speaker, text in blocks:
                    for sentence in SENTENCE_SPLIT.split(" ".join(text.split())):
                        self.recent.append(norm(speaker + sentence))
                        self.recent.append(norm(sentence))
                return
            pending = ""
            for i, (speaker, text) in enumerate(blocks):
                text = " ".join(text.split())
                if not text:
                    continue
                parts = SENTENCE_SPLIT.split(text)
                last_block = i == len(blocks) - 1
                finals = parts if not last_block else parts[:-1]
                if last_block:
                    pending = f"{speaker}: {parts[-1]}" if speaker else parts[-1]
                for sentence in finals:
                    key = norm(speaker + sentence)
                    if not norm(sentence) or key in self.recent:
                        continue
                    self._commit(now, f"{speaker}: {sentence}" if speaker else sentence, key, speaker)
                    self._note_cues(sentence)
            self.pending = pending

    def _note_cues(self, sentence):
        if CUE_WORDS.search(sentence):
            self.cue_at = time.time()
        for key in TICKET_KEY.findall(sentence):
            if key not in self.tickets_seen:
                self.tickets_seen.append(key)
                self.tickets_new.append(key)

    def add_note(self, label, text):
        """Record a question or a Claude answer in the transcript."""
        with self.lock:
            self.entries.append((datetime.datetime.now(), f"{label}: {text}"))
            self.dirty = True

    # --- structured file -------------------------------------------------
    def _target_path(self):
        name = safe_filename(self.display_title()) or "Meeting"
        base = f"{name} - {self.started.strftime('%Y-%m-%d')}"
        path = os.path.join(SAVE_DIR, base + ".txt")
        n = 2
        while os.path.exists(path) and os.path.normcase(path) != os.path.normcase(self.file_path or ""):
            path = os.path.join(SAVE_DIR, f"{base} ({n}).txt")
            n += 1
        return path

    def _render(self):
        """The meeting file, written to be read later by other people: real names
        (never 'You'), real dates, and each list exactly once. Typed questions
        and Claude's live answers stay in the window, not in the file."""
        c = self.context
        end = self.ended_at or datetime.datetime.now()
        day = self.started.date()
        me = profile.name
        when = lambda text: real_dates(text, day)
        section = lambda title, body: [title, body.strip() if body else "", ""]
        owner = lambda a: owner_text(a["owner"]) + ("?" if a["owner"] and not a.get("sure", True) else "")
        actions = []
        for a in c["actions"]:
            who = owner(a) or "owner: ?"
            due = f", due {when(a['due'])}" if a["due"] else ""
            actions.append(f"- [{'x' if a['done'] else ' '}] {when(a['text'])} ({who}{due})")
        open_q = [when(line) for line in c["open_debates"].splitlines() if line.strip()]
        open_q += [f"- [ ] {when(q['text'])}" for q in c["questions"] if not q["done"]]
        people = self.people()
        lines = [
            f"MEETING: {c['title'] or c['subject']}",
            f"Date: {self.started:%a} {day.day} {self.started:%b %Y}, "
            f"{self.started:%H:%M} - {end:%H:%M}",
            f"Participants: {', '.join(people)}",
        ]
        if c["agenda"]:
            lines += ["Agenda:"] + [f"- [{'x' if a in c['agenda_done'] else ' '}] {a}"
                                    for a in c["agenda"]]
        if c["role"]:
            lines.append(f"{me + chr(39) + 's' if me else 'My'} role: {c['role']}")
        if c["goals"]:
            lines.append(f"{me + chr(39) + 's' if me else 'My'} goals: {c['goals']}")
        lines.append("")
        lines += section("SUMMARY", when(c["recap"]))
        lines += section("BY PERSON", when(c["by_person"]))
        lines += section("DECISIONS", when(c["decisions"]))
        lines += section("ACTION ITEMS", "\n".join(actions))
        lines += section("OPEN QUESTIONS", "\n".join(open_q))
        lines += section("CONTEXT", "\n".join(
            f"- {x['title']}" + (f" ({x['source']})" if x["source"] else "")
            + (f": {x['detail']}" if x["detail"] else "")
            + (f" {x['url']}" if x["url"] else "") for x in c["context"]))
        lines.append("TRANSCRIPT")
        lines += [f"[{t.strftime('%H:%M:%S')}] {display_line(s)}" for t, s in self.entries
                  if not s.startswith(("YOU ASKED:", "CLAUDE:"))]
        return "\n".join(lines) + "\n"

    def to_json(self):
        """The meeting as structured data (meeting.json), schema SCHEMA_VERSION."""
        c = self.context
        end = self.ended_at or datetime.datetime.now()
        day = self.started.date()

        def rows(text):
            return [re.sub(r"^\s*[-*\u2022]\s*", "", l).strip()
                    for l in (text or "").splitlines() if l.strip()]
        by_person = []
        for line in rows(c["by_person"]):
            who, sep, said = line.partition(":")
            by_person.append({"name": who.strip(), "text": said.strip()}
                             if sep and len(who) <= 60 else {"name": "", "text": line})
        spoken = []
        for t, line in self.entries:
            if line.startswith(NOTE_PREFIXES):
                continue
            line = display_line(line)
            who, sep, said = line.partition(": ")
            spoken.append({"t": t.strftime("%H:%M:%S"), "speaker": who if sep and len(who) <= 40
                           else "", "text": said if sep and len(who) <= 40 else line})
        actions = []
        for a in c["actions"]:
            actions.append({
                "id": a.get("id", ""), "text": real_dates(a["text"], day),
                "owner": owner_text(a["owner"]), "owner_sure": a.get("sure", True),
                "due": a["due"], "status": "done" if a["done"] else "open",
                "created_in": a.get("created_in", self.meeting_id),
                "source_time": a.get("source_time", ""), "closed_at": a.get("closed_at", ""),
                "closed_by": a.get("closed_by", ""), "close_evidence": a.get("close_evidence", "")})
        return {
            "schema_version": SCHEMA_VERSION, "id": self.meeting_id, "imported": False,
            "app": f"Sidenote {SIDENOTE_VERSION}",
            "title": c["title"] or c["subject"], "subject": c["subject"],
            "date": day.isoformat(), "start": self.started.strftime("%H:%M"),
            "end": end.strftime("%H:%M"),
            "duration_min": int((end - self.started).total_seconds() // 60),
            "ended": bool(self.ended_at), "user_name": profile.name,
            "participants": self.people(), "role": c["role"], "goals": c["goals"],
            "agenda": [{"text": a, "covered": a in c["agenda_done"]} for a in c["agenda"]],
            "summary": real_dates(c["recap"], day), "by_person": by_person,
            "decisions": [{"id": f"d{i}", "text": real_dates(x, day)}
                          for i, x in enumerate(rows(c["decisions"]), 1)],
            "open_questions": [{"id": f"q{i}", "text": real_dates(x, day),
                                "status": self.item_status.get(f"q{i}", "open")}
                               for i, x in enumerate(rows(c["open_debates"]), 1)],
            "action_items": actions,
            "questions_to_ask": [{"id": q.get("id", f"t{i}"), "text": q["text"], "asked": q["done"]}
                                 for i, q in enumerate(c["questions"], 1)],
            "context": [dict(x) for x in c["context"]],
            "transcript": spoken,
            "saved_at": datetime.datetime.now().isoformat(timespec="seconds"),
        }

    def save_now(self):
        with self.lock:
            has_content = self.entries or any(
                self.context[k] for k in ("title", "subject", "role", "goals",
                                          "participants", "agenda", "recap"))
            if not has_content:
                return
            try:
                os.makedirs(SAVE_DIR, exist_ok=True)
                target = self._target_path()
                if self.file_path and self.file_path != target and os.path.exists(self.file_path):
                    os.replace(self.file_path, target)    # title changed: rename the file
                    old_json = json_path_for(self.file_path)
                    if os.path.exists(old_json):
                        os.replace(old_json, json_path_for(target))
                _write_json(json_path_for(target), self.to_json())    # json first (see import)
                tmp = target + ".tmp"
                with open(tmp, "w", encoding="utf-8") as f:
                    f.write(self._render())
                os.replace(tmp, target)
                self.file_path = target
                self.dirty = False
            except OSError as e:
                log.warning("Could not save meeting file: %s", e)

    def _writer_loop(self):
        while True:
            time.sleep(3)
            if self.dirty:
                self.save_now()

    # --- reading -----------------------------------------------------------
    def _format(self, items):
        lines = [f"[{t.strftime('%H:%M:%S')}] {display_line(s)}" for t, s in items]
        if self.pending:
            lines.append(f"[now, still speaking] {display_line(self.pending)}")
        return "\n".join(lines)

    def since(self, minutes):
        cutoff = datetime.datetime.now() - datetime.timedelta(minutes=minutes)
        with self.lock:
            return self._format([(t, s) for t, s in self.entries if t >= cutoff])

    def count_lines(self):
        with self.lock:
            return len(self.entries)

    def lines_from(self, start):
        with self.lock:
            items = [(t, s) for t, s in self.entries[start:]
                     if not s.startswith(("YOU ASKED:", "CLAUDE:"))]
        return "\n".join(f"[{t.strftime('%H:%M:%S')}] {display_line(s)}" for t, s in items)

    def full(self):
        with self.lock:
            return self._format(list(self.entries))

    def tail(self, n=3):
        with self.lock:
            items = [s for _, s in self.entries
                     if not s.startswith(("YOU ASKED:", "CLAUDE:"))][-n:]
            if self.pending:
                items.append(self.pending)
        return " ".join(display_line(i) for i in items[-n:])

    def spoken_stats(self):
        """(lines, words) actually said in the meeting: typed questions,
        Claude's answers and the end marker are not counted."""
        with self.lock:
            spoken = [s for _, s in self.entries if not s.startswith(NOTE_PREFIXES)]
        return len(spoken), sum(len(s.split()) for s in spoken)

    def conversation(self):
        """[(time, 'you' or 'claude', text)] for every question and answer."""
        with self.lock:
            items = list(self.entries)
        out = []
        for t, s in items:
            if s.startswith("YOU ASKED:"):
                out.append((t, "you", s[len("YOU ASKED:"):].strip()))
            elif s.startswith("CLAUDE:"):
                out.append((t, "claude", s[len("CLAUDE:"):].strip()))
        return out

    def stats(self):
        with self.lock:
            count = len(self.entries)
            minutes = int(((self.ended_at or datetime.datetime.now())
                           - self.started).total_seconds() // 60)
        return count, minutes

    def context_text(self):
        count, minutes = self.stats()
        with self.lock:
            c = dict(self.context)
            agenda = "\n".join(
                f"{i}. [{'covered' if a in c['agenda_done'] else 'not covered yet'}] {a}"
                for i, a in enumerate(c["agenda"], 1))
            people = ", ".join(c["participants"])
            heard = ", ".join(s for s in self.speakers if s not in c["participants"])
            actions = "\n".join(
                f"{i}. [{'done' if a['done'] else 'open'}] {a['text']}"
                + (f" - owner: {owner_text(a['owner'])}" if owner_text(a["owner"])
                   else " - owner: unknown")
                + (" (unsure)" if a["owner"] and not a.get("sure", True) else "")
                + (f" - due: {a['due']}" if a["due"] else "")
                for i, a in enumerate(c["actions"], 1))
            questions = "\n".join(
                f"{i}. [{'asked' if q['done'] else 'not asked yet'}] {q['text']}"
                for i, q in enumerate(c["questions"], 1))
            ctx = "\n".join(f"- {x['title']} ({x['source']})" + (f": {x['detail']}" if x["detail"] else "")
                            for x in c["context"])
        return (
            f"User's name: {profile.name or '(not known yet)'}"
            f"{' (lines labelled You in the captions are this person)' if profile.name else ''}\n"
            f"Meeting date: {fmt_day(self.started)} {self.started:%Y}\n"
            f"Meeting title: {c['title'] or '(not set)'}\n"
            f"Subject: {c['subject'] or '(not set)'}\n"
            f"Agenda:\n{agenda or '(not set)'}\n"
            f"Participants: {people or '(not set)'}\n"
            f"Other names heard in the captions: {heard or '(none)'}\n"
            f"User's role: {c['role'] or '(not set)'}\n"
            f"User's goals: {c['goals'] or '(not set)'}\n"
            f"Action items so far:\n{actions or '(none)'}\n"
            f"Questions to ask (saved for the user):\n{questions or '(none)'}\n"
            f"Context already found (Jira/Confluence):\n{ctx or '(none)'}\n"
            f"Transcript source: {self.source or '(none yet)'}"
            f"{' - speaker names included' if self.source in ('Google Meet', 'Microsoft Teams') else ' - names only when Zoom shows them' if self.source == 'Zoom' else ''}\n"
            f"Meeting running for {minutes} min, {count} lines captured."
        )


# ---------------------------------------------------------------------------
# Meeting history: one <name>.meeting.json next to each <name>.txt
# ---------------------------------------------------------------------------
# The json holds everything (recap, lists, transcript), so each meeting is one
# self-contained file to back up or move. A small cache (.sidenote_index.json)
# keeps titles, summaries and items for fast queries; it is rebuilt from the
# meeting files whenever they change, so it is safe to delete.
SCHEMA_VERSION = 1
MEETING_EXT = ".meeting.json"
INDEX_NAME = ".sidenote_index.json"
INDEX_VERSION = 2               # bump when the cached fields change (cache is rebuilt)
_history_lock = threading.RLock()


def new_meeting_id(started):
    return f"{started:%Y%m%d-%H%M}-{os.urandom(2).hex()}"


def json_path_for(txt_path):
    base = txt_path[:-4] if txt_path.lower().endswith(".txt") else txt_path
    return base + MEETING_EXT


def _write_json(path, data):
    import json
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


def migrate_meeting(data):
    """Bring a meeting.json from any Sidenote version to the current schema.
    Version 1 is the first one; later versions add steps here. Missing fields
    get defaults, so older or imported files never break a query."""
    version = int(data.get("schema_version") or 0)
    if version > SCHEMA_VERSION:
        log.info("Meeting %s is from a newer Sidenote (schema %s)", data.get("id"), version)
    defaults = {"id": "", "imported": False, "title": "", "subject": "", "date": "",
                "start": "", "end": "", "duration_min": None, "participants": [],
                "agenda": [], "summary": "", "by_person": [], "decisions": [],
                "open_questions": [], "action_items": [], "questions_to_ask": [],
                "context": [], "transcript": [], "user_name": "", "role": "", "goals": ""}
    for key, value in defaults.items():
        if data.get(key) is None:
            data[key] = value if not isinstance(value, list) else []
    data["schema_version"] = max(version, SCHEMA_VERSION) if version else SCHEMA_VERSION
    return data


def load_meeting(path):
    import json
    with open(path, encoding="utf-8") as f:
        data = migrate_meeting(json.load(f))
    data["_path"] = path
    return data


# ---- import of meetings saved before meeting.json existed ------------------------
_IMPORT_HEADERS_V6 = {"AGENDA", "PARTICIPANTS", "MY ROLE", "MY GOALS", "QUICK RECAP",
                      "ACTION ITEMS", "CONTEXT (Jira / Confluence)", "QUESTIONS TO ASK",
                      "FULL TRANSCRIPT"}
_IMPORT_HEADERS_V8 = {"SUMMARY", "BY PERSON", "DECISIONS", "ACTION ITEMS", "OPEN QUESTIONS",
                      "CONTEXT", "TRANSCRIPT"}
_LINE = re.compile(r"^\[(\d{2}:\d{2}:\d{2})\] (.*)$")
_SPEAKER = re.compile(r"^([A-ZЀ-Я][\w.'\-]*(?: [A-ZЀ-Я][\w.'\-]*){0,3}): (.+)$")


def _split_speaker(line):
    m = _SPEAKER.match(line)
    if m and m.group(1) not in ("YOU ASKED", "CLAUDE"):
        return m.group(1), m.group(2)
    return "", line


def parse_meeting_txt(path):
    """Best-effort reading of a saved meeting .txt (all three layouts Sidenote has
    used). Returns a meeting dict marked imported, or None if it isn't a meeting."""
    import hashlib
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            text = f.read()
    except OSError:
        return None
    lines = text.splitlines()
    name = os.path.basename(path)
    if not lines:
        return None
    structured = lines[0].startswith("MEETING:")
    if not structured and not any(_LINE.match(l) for l in lines[:20]):
        return None                              # not a meeting (debug or capture file)
    d = migrate_meeting({"imported": True, "source_txt": name})
    m = re.search(r"(\d{4}-\d{2}-\d{2})(?:_(\d{2})(\d{2}))?", name)
    day = m.group(1) if m else ""
    start = f"{m.group(2)}:{m.group(3)}" if m and m.group(2) else ""
    end = ""
    sections, current = {}, None
    headers = _IMPORT_HEADERS_V6 | _IMPORT_HEADERS_V8
    for line in lines:
        if line.strip() in headers:
            current = line.strip()
            sections[current] = []
            continue
        if current is None:
            if line.startswith("MEETING:"):
                d["title"] = line[8:].strip()
            elif line.startswith("Subject:"):
                d["subject"] = line[8:].strip()
            elif line.startswith("Date:"):
                dm = re.search(r"(\d{4}-\d{2}-\d{2})", line)
                if dm:
                    day = dm.group(1)
                else:
                    dm = re.search(r"(\d{1,2}) (\w{3}) (\d{4})", line)
                    if dm:
                        try:
                            day = datetime.datetime.strptime(" ".join(dm.groups()),
                                                             "%d %b %Y").date().isoformat()
                        except ValueError:
                            pass
                times = re.findall(r"(\d{2}:\d{2})", line)
                if times:
                    start, end = times[0], times[-1]
            elif line.startswith("Participants:"):
                d["participants"] = parse_list(line[13:])
            elif re.match(r"^- \[[ x]\] ", line):
                d["agenda"].append({"text": line[6:].strip(), "covered": line[3] == "x"})
            elif re.match(r"^(?:.+'s|My) role: ", line):
                d["role"] = line.split(": ", 1)[1].strip()
            elif re.match(r"^(?:.+'s|My) goals: ", line):
                d["goals"] = line.split(": ", 1)[1].strip()
            elif _LINE.match(line):
                current = "TRANSCRIPT"
                sections[current] = [line]
            continue
        sections[current].append(line)

    def body(*keys):
        for k in keys:
            if k in sections:
                return [l for l in sections[k] if l.strip()]
        return []

    def bullets(rows):
        return [re.sub(r"^\s*[-*•]\s*", "", r).strip() for r in rows]

    v8 = "SUMMARY" in sections or "BY PERSON" in sections      # owner in brackets
    if "AGENDA" in sections:
        for row in body("AGENDA"):
            am = re.match(r"^- (?:\[([ x])\] )?(.*)$", row)       # oldest files: '- item'
            if am and am.group(2).strip():
                d["agenda"].append({"text": am.group(2).strip(), "covered": am.group(1) == "x"})
    if not d["participants"]:
        d["participants"] = bullets(body("PARTICIPANTS"))
    if body("MY ROLE"):
        d["role"] = " ".join(body("MY ROLE"))
    if body("MY GOALS"):
        d["goals"] = " ".join(body("MY GOALS"))
    decisions, open_qs = bullets(body("DECISIONS")), []
    recap = body("QUICK RECAP")
    if recap:                                     # v6: 'Summary: ... / Decisions: ...'
        summary = []
        for row in recap:
            label, sep, rest = row.partition(":")
            key = label.strip().lower()
            if sep and key == "summary":
                summary.append(rest.strip())
            elif sep and key == "decisions":
                if rest.strip().lower().rstrip(".") not in ("none", "none yet", "no"):
                    decisions += [x.strip() for x in re.split(r";\s*", rest) if x.strip()]
            elif sep and key == "open questions":
                open_qs += [x.strip() for x in re.split(r";\s*", rest) if x.strip()]
            elif sep and key == "action items":
                pass                              # the ACTION ITEMS list is the source
            else:
                summary.append(row.strip())
        d["summary"] = "\n".join(summary)
    else:
        d["summary"] = "\n".join(body("SUMMARY"))
    for row in body("BY PERSON"):
        who, sep, said = row.partition(":")
        d["by_person"].append({"name": who.strip(), "text": said.strip()} if sep
                              else {"name": "", "text": row.strip()})
    for row in body("OPEN QUESTIONS"):
        qm = re.match(r"^- \[([ x])\] (.*)$", row)
        if qm:
            d["questions_to_ask"].append({"text": qm.group(2).strip(), "asked": qm.group(1) == "x"})
        else:
            open_qs.append(re.sub(r"^\s*-\s*", "", row).strip())
    for row in body("QUESTIONS TO ASK"):
        qm = re.match(r"^- \[([ x])\] (.*?)(?: \(asked\))?$", row)
        if qm:
            d["questions_to_ask"].append({"text": qm.group(2).strip(), "asked": qm.group(1) == "x"})
    nothing = re.compile(r"^(?:none|n/?a|no (?:open )?(?:questions|decisions)|nothing)\b", re.I)
    decisions = [x for x in decisions if x and not nothing.match(x)]
    open_qs = [x for x in open_qs if x and not nothing.match(x)]
    d["decisions"] = [{"id": f"d{i}", "text": t} for i, t in enumerate(decisions, 1)]
    d["open_questions"] = [{"id": f"q{i}", "text": t, "status": "open"}
                           for i, t in enumerate(open_qs, 1)]
    d["questions_to_ask"] = [dict(q, id=f"t{i}") for i, q in enumerate(d["questions_to_ask"], 1)]
    for i, row in enumerate(body("ACTION ITEMS"), 1):
        am = re.match(r"^- \[([ x])\] (.*)$", row)
        if not am:
            continue
        task, owner, due = am.group(2).strip(), "", ""
        for pm in re.finditer(r"\((owner|due): ([^)]*)\)", task):          # v6 layout
            if pm.group(1) == "owner":
                owner = pm.group(2).strip()
            else:
                due = pm.group(2).strip()
        task = re.sub(r"\s*\((?:owner|due): [^)]*\)", "", task)
        pm = re.search(r"\s*\(([^()]*)\)$", task) if v8 else None          # v8 layout
        if pm and not owner:
            inside = pm.group(1)
            parts = [p.strip() for p in inside.split(", due ")]
            if parts[0] and parts[0] != "owner: ?":
                owner = parts[0]
            if len(parts) > 1:
                due = parts[1]
            task = task[:pm.start()]
        d["action_items"].append({"id": f"a{i}", "text": task.strip(),
                                  "owner": owner.rstrip("?") if owner != "?" else "",
                                  "owner_sure": not owner.endswith("?"), "due": due,
                                  "status": "done" if am.group(1) == "x" else "open",
                                  "created_in": "", "source_time": "", "closed_at": "",
                                  "closed_by": "", "close_evidence": ""})
    for row in body("CONTEXT (Jira / Confluence)", "CONTEXT"):
        d["context"].append({"title": re.sub(r"^\s*-\s*", "", row).strip(), "source": "",
                             "detail": "", "url": ""})
    for row in sections.get("FULL TRANSCRIPT", []) + sections.get("TRANSCRIPT", []):
        lm = _LINE.match(row)
        if not lm or lm.group(2).startswith(("YOU ASKED:", "CLAUDE:", "MEETING ENDED")):
            continue
        speaker, said = _split_speaker(lm.group(2))
        d["transcript"].append({"t": lm.group(1), "speaker": speaker, "text": said})
    if d["transcript"]:
        start = start or d["transcript"][0]["t"][:5]
        end = end or d["transcript"][-1]["t"][:5]
    if not (d["transcript"] or d["summary"] or d["action_items"] or d["agenda"]
            or d["questions_to_ask"]):
        return None                              # an empty meeting: nothing to keep
    if not d["participants"]:
        seen = []
        for row in d["transcript"]:
            if row["speaker"] and row["speaker"] not in seen and row["speaker"] != "Others":
                seen.append(row["speaker"])
        d["participants"] = seen[:20]
    if not d["title"]:
        stem = re.sub(r"\s*-?\s*\d{4}-\d{2}-\d{2}.*$", "", name[:-4]).strip(" -_")
        d["title"] = d["subject"] or (stem if stem and stem.lower() != "meeting" else "")
    d["date"], d["start"], d["end"] = day, start, end
    try:                                # 'today' / 'tomorrow' -> real dates of that meeting
        base = datetime.date.fromisoformat(day)
        for a in d["action_items"]:
            a["due"] = real_dates(a["due"], base, due=True)
            a["text"] = real_dates(a["text"], base)
        d["summary"] = real_dates(d["summary"], base)
    except ValueError:
        pass
    if profile.name:                    # old files said 'You' for the user
        d["participants"] = [profile.name if p in ("You", "Me") else p for p in d["participants"]]
        for row in d["transcript"]:
            if row["speaker"] in ("You", "Me"):
                row["speaker"] = profile.name
    d["participants"] = [p for p in d["participants"] if p not in ("You", "Me")]
    try:
        t0 = datetime.datetime.strptime(start, "%H:%M")
        t1 = datetime.datetime.strptime(end, "%H:%M")
        d["duration_min"] = int((t1 - t0).total_seconds() // 60) % (24 * 60)
    except ValueError:
        d["duration_min"] = None
    digest = hashlib.sha1(name.encode("utf-8")).hexdigest()[:4]
    d["id"] = f"{day.replace('-', '')}-{start.replace(':', '') or '0000'}-{digest}"
    for a in d["action_items"]:
        a["created_in"] = d["id"]
    return d


def import_old_meetings():
    """One-time, best effort: make a meeting.json for every saved meeting .txt that
    has none. Never changes or deletes a .txt. Returns how many were imported."""
    import glob
    count = 0
    live = os.path.normcase(transcript.file_path or "")
    for txt in glob.glob(os.path.join(SAVE_DIR, "*.txt")):
        target = json_path_for(txt)
        if os.path.exists(target) or os.path.normcase(txt) == live:
            continue
        data = parse_meeting_txt(txt)
        if data is None:
            continue
        try:
            _write_json(target, data)
            count += 1
        except OSError as e:
            log.info("Could not import %s: %s", os.path.basename(txt), e)
    if count:
        log.info("Imported %d earlier meeting(s) into the history", count)
    return count


# ---- index (cache) and queries ----------------------------------------------------
def _title_from(summary):
    """A name for a meeting without a title: the start of its summary."""
    text = re.sub(r"^(?:quick recap|summary)\s*[:\-]\s*", "", (summary or "").strip(), flags=re.I)
    text = re.split(r"[.;:(\n]", text)[0].strip()
    words = text.split()
    if not words:
        return "Untitled meeting"
    words[0] = words[0][:1].upper() + words[0][1:]
    short = " ".join(words[:6])
    return short + ("\u2026" if len(words) > 6 else "")


def _index_entry(d, stat):
    summary = (d["summary"] or "").strip().splitlines()
    line = summary[0] if summary else (d["agenda"][0]["text"] if d["agenda"] else "")
    return {"id": d["id"], "path": d["_path"], "mtime": stat.st_mtime, "size": stat.st_size,
            "title": d["title"] or d["subject"] or _title_from(d["summary"]), "date": d["date"],
            "start": d["start"], "end": d["end"], "participants": d["participants"],
            "summary_line": line[:200], "imported": d["imported"],
            "action_items": d["action_items"], "decisions": d["decisions"],
            "open_questions": d["open_questions"], "questions_to_ask": d["questions_to_ask"],
            "agenda": d["agenda"], "lines": len(d["transcript"])}


def history_index():
    """All meetings (newest first), from the cache; files that changed are re-read."""
    import glob, json
    with _history_lock:
        import_old_meetings()
        path = os.path.join(SAVE_DIR, INDEX_NAME)
        try:
            with open(path, encoding="utf-8") as f:
                cache = json.load(f)
            if cache.get("schema_version") != SCHEMA_VERSION or \
                    cache.get("index_version") != INDEX_VERSION:
                cache = {}
        except Exception:
            cache = {}
        old = {e["path"]: e for e in cache.get("meetings", [])}
        entries, changed = [], False
        for file in glob.glob(os.path.join(SAVE_DIR, "*" + MEETING_EXT)):
            try:
                stat = os.stat(file)
            except OSError:
                continue
            e = old.get(file)
            if e and e["mtime"] == stat.st_mtime and e["size"] == stat.st_size:
                entries.append(e)
                continue
            try:
                entries.append(_index_entry(load_meeting(file), stat))
                changed = True
            except Exception as ex:
                log.info("Skipped unreadable meeting file %s: %s", os.path.basename(file), ex)
        if changed or len(entries) != len(old):
            try:
                _write_json(path, {"schema_version": SCHEMA_VERSION,
                                   "index_version": INDEX_VERSION, "meetings": entries})
            except OSError:
                pass
        entries.sort(key=lambda e: (e["date"], e["start"]), reverse=True)
        return entries


def _in_range(e, date_from, date_to):
    return (not date_from or e["date"] >= date_from) and (not date_to or e["date"] <= date_to)


def _day_label(e):
    try:
        d = datetime.date.fromisoformat(e["date"])
        return f"{fmt_day(d)} {d.year}"
    except Exception:
        return e["date"] or "(no date)"


def find_meeting(meeting_id):
    for e in history_index():
        if e["id"] == meeting_id:
            return e
    return None


profile = Profile()
transcript = Transcript()
ui_queue = queue.Queue()        # server -> overlay
question_queue = queue.Queue()  # overlay -> server


class LiveState:
    def __init__(self):
        self.waiting = False
        self.last_seen = 0.0     # last time Claude called wait_for_question
        self.quiet_rounds = 0    # wait calls without a question since the last scan
        self.last_scan = 0.0     # when Claude last scanned the transcript
        self.released = False    # Claude stopped listening after an ended meeting
        self.scanned_upto = 0    # transcript lines already scanned
        self.autofill_sent = False  # auto title/agenda note already sent this meeting
        self.mode = "home"          # window screen: home, history or record
        self.last_activity = time.time()   # last question or screen change (idle timer)
        self.answer_target = "live"  # where show_suggestion goes: live, history, dropped
        self.pending_info = {}      # meeting info given before Record was pressed
        self.record_on_open = False  # open straight into a recording (user asked)

    def label(self):
        if self.released:
            return "Sidenote idle - type 'open Sidenote' in the Claude app"
        if self.waiting:
            return "Sidenote listening - type below"
        if self.last_seen and time.time() - self.last_seen < PAUSED_AFTER_SECONDS:
            return "Claude is thinking..."
        if self.last_seen:
            return "Sidenote paused - type 'continue' in the Claude app"
        return "Connecting to Claude... (if it stays like this, type 'continue' in the Claude app)"


live = LiveState()

window_open = threading.Event()     # overlay currently shown
open_request = threading.Event()    # someone asked to open the overlay


# ---------------------------------------------------------------------------
# Live Captions reader (background thread)
# ---------------------------------------------------------------------------
class CaptionsWindow:
    """Moves the Live Captions window off-screen so it keeps running without
    taking screen space, and puts it back when asked or when Sidenote exits."""
    SWP_NOSIZE, SWP_NOZORDER, SWP_NOACTIVATE = 0x0001, 0x0004, 0x0010

    def __init__(self):
        self.hide_wanted = True
        self.saved_pos = None
        self.note = ""
        try:
            import ctypes
            from ctypes import wintypes
            self.user32 = ctypes.windll.user32
            self.RECT = wintypes.RECT
            self.ctypes = ctypes
        except Exception:      # not on Windows (tests)
            self.user32 = None

    def _hwnd(self):
        return self.user32.FindWindowW(CAPTIONS_WINDOW_CLASS, None) if self.user32 else 0

    def _rect(self, hwnd):
        r = self.RECT()
        self.user32.GetWindowRect(hwnd, self.ctypes.byref(r))
        return r

    def _move(self, hwnd, x, y):
        self.user32.SetWindowPos(hwnd, 0, int(x), int(y), 0, 0,
                                 self.SWP_NOSIZE | self.SWP_NOZORDER | self.SWP_NOACTIVATE)

    def _offscreen_x(self):
        # right of the whole virtual desktop (all monitors)
        return self.user32.GetSystemMetrics(76) + self.user32.GetSystemMetrics(78) + 200

    def tick(self):
        """Called regularly: enforce the hidden/visible state."""
        if not self.user32:
            return
        try:
            hwnd = self._hwnd()
            if not hwnd:
                self.note = ""
                return
            r = self._rect(hwnd)
            off_x = self._offscreen_x()
            offscreen = r.left >= off_x - 50
            docked = (r.right - r.left) >= self.user32.GetSystemMetrics(0) - 10 and not offscreen
            if self.hide_wanted:
                if docked:
                    self.note = ("To hide Live Captions: in its gear menu set "
                                 "Position to 'Floating on screen'")
                    return
                self.note = ""
                if not offscreen:
                    self.saved_pos = (r.left, r.top)
                    self._move(hwnd, off_x, r.top)
            else:
                self.note = ""
                if offscreen:
                    self._restore(hwnd)
        except Exception as e:
            log.info("Could not move Live Captions window: %s", e)

    def _restore(self, hwnd):
        if self.saved_pos:
            self._move(hwnd, *self.saved_pos)
        else:
            self._move(hwnd, 100, 100)

    def ensure_running(self):
        """Start Live Captions if it isn't open yet (remember that we did)."""
        self.started_by_us = False
        if not self.user32 or self._hwnd():
            return
        exe = os.path.join(os.environ.get("SystemRoot", r"C:\Windows"),
                           "System32", "LiveCaptions.exe")
        try:
            import subprocess
            subprocess.Popen([exe], close_fds=True)
            self.started_by_us = True
            log.info("Started Live Captions")
            return
        except Exception as e:
            log.info("Could not start LiveCaptions.exe (%s), trying Win+Ctrl+L", e)
        try:  # fallback: press Win+Ctrl+L
            VK_LWIN, VK_CONTROL, VK_L, UP = 0x5B, 0x11, 0x4C, 0x0002
            for vk in (VK_LWIN, VK_CONTROL, VK_L):
                self.user32.keybd_event(vk, 0, 0, 0)
            for vk in (VK_L, VK_CONTROL, VK_LWIN):
                self.user32.keybd_event(vk, 0, UP, 0)
            self.started_by_us = True
        except Exception as e:
            log.info("Could not start Live Captions: %s", e)

    def close_live_captions(self):
        """Close Windows Live Captions (used when Sidenote closes)."""
        if not self.user32:
            return
        try:
            hwnd = self._hwnd()
            if not hwnd:
                return
            self.user32.PostMessageW(hwnd, 0x0010, 0, 0)        # WM_CLOSE
            for _ in range(15):                                  # up to 1.5 s
                time.sleep(0.1)
                if not self._hwnd():
                    log.info("Closed Live Captions")
                    return
            import subprocess                                    # still open: end it
            subprocess.run(["taskkill", "/IM", "LiveCaptions.exe"], capture_output=True,
                           creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
            time.sleep(0.5)
            if self._hwnd():
                subprocess.run(["taskkill", "/F", "/IM", "LiveCaptions.exe"],
                               capture_output=True,
                               creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
            log.info("Closed Live Captions")
        except Exception as e:
            log.info("Could not close Live Captions: %s", e)

    def show_now(self):
        """Bring the window back immediately (used when Sidenote exits)."""
        self.hide_wanted = False
        if not self.user32:
            return
        try:
            hwnd = self._hwnd()
            if hwnd and self._rect(hwnd).left >= self._offscreen_x() - 50:
                self._restore(hwnd)
        except Exception:
            pass


class MacCaptionsWindow:
    """macOS: switch Live Captions on/off (via System Settings, the only way macOS
    allows) and keep its window off-screen while Sidenote reads it."""
    OFFSCREEN = (20000, 20000)
    SETTINGS_URL = "x-apple.systempreferences:com.apple.Accessibility-Settings.extension?LiveCaptions"
    SWITCH_ID = "AX_SYSTEM_TRANSCRIPTION_ENABLED"

    def __init__(self):
        self.hide_wanted = True
        self.saved_pos = None
        self.note = ""
        self.started_by_us = False
        self.busy = False

    # -- helpers ----------------------------------------------------------------
    def _window(self):
        try:
            for app in mac_apps((MAC_LC_BUNDLE,)):
                el = AXUIElementCreateApplication(app.processIdentifier())
                for w in ax(el, "AXWindows") or []:
                    return w
        except Exception:
            pass
        return None

    def _pos(self, w):
        try:
            from ApplicationServices import AXValueGetValue, kAXValueCGPointType
            ok, p = AXValueGetValue(ax(w, "AXPosition"), kAXValueCGPointType, None)
            return (p.x, p.y) if ok else None
        except Exception:
            return None

    def _move(self, w, xy):
        try:
            from ApplicationServices import AXValueCreate, kAXValueCGPointType
            from Quartz import CGPoint
            AXUIElementSetAttributeValue(w, "AXPosition",
                                         AXValueCreate(kAXValueCGPointType, CGPoint(*xy)))
        except Exception as e:
            log.info("Could not move Live Captions: %s", e)

    def _set_enabled(self, on):
        """Flip the Live Captions switch in System Settings, then close Settings."""
        import subprocess
        from AppKit import NSWorkspace
        def settings_apps():
            return [a for a in NSWorkspace.sharedWorkspace().runningApplications()
                    if str(a.bundleIdentifier() or "") == "com.apple.systempreferences"]
        was_open = bool(settings_apps())
        subprocess.run(["open", "-g", self.SETTINGS_URL])
        switch = None
        for _ in range(30):                               # up to ~6 s
            time.sleep(0.2)
            for app in settings_apps():
                el = AXUIElementCreateApplication(app.processIdentifier())
                for w in ax(el, "AXWindows") or []:
                    for x, _ in ax_walk(w, 45):
                        if ax(x, "AXIdentifier") == self.SWITCH_ID:
                            switch = x
                            break
                    if switch is not None:
                        break
            if switch is not None:
                break
        changed = False
        if switch is not None:
            value = ax(switch, "AXValue")
            if bool(value) != on:
                try:
                    from ApplicationServices import AXUIElementPerformAction
                    AXUIElementPerformAction(switch, "AXPress")
                    changed = True
                except Exception as e:
                    log.info("Could not press the Live Captions switch: %s", e)
        else:
            log.info("Live Captions switch not found in System Settings")
        time.sleep(0.6)
        for app in settings_apps():                       # tidy up Settings
            try:
                if not was_open:
                    app.terminate()
            except Exception:
                pass
        return switch is not None, changed

    # -- the same interface as the Windows helper ------------------------------------
    def ensure_running(self):
        if self.busy or self._window() is not None:
            return
        def work():
            self.busy = True
            try:
                found, changed = self._set_enabled(True)
                self.started_by_us = changed
                if not found:
                    self.note = "Turn on Live Captions: Settings > Accessibility"
                else:
                    ui_queue.put(("toast", "Turned on Live Captions"))
            finally:
                self.busy = False
        threading.Thread(target=work, daemon=True).start()

    def tick(self):
        w = self._window()
        if w is None:
            return
        self.note = ""
        pos = self._pos(w)
        if pos is None:
            return
        offscreen = pos[0] >= self.OFFSCREEN[0] - 100
        if self.hide_wanted and not offscreen:
            self.saved_pos = pos
            self._move(w, self.OFFSCREEN)
        elif not self.hide_wanted and offscreen:
            self._move(w, self.saved_pos or (200, 200))

    def show_now(self):
        self.hide_wanted = False
        w = self._window()
        if w is not None:
            pos = self._pos(w)
            if pos and pos[0] >= self.OFFSCREEN[0] - 100:
                self._move(w, self.saved_pos or (200, 200))

    def close_live_captions(self):
        """Sidenote closed: put the window back and switch Live Captions off.
        The switch is turned off even when no captions window is showing:
        macOS can keep Live Captions on with its window closed or hidden."""
        if self._window() is not None:
            self.show_now()
        try:
            self._set_enabled(False)
            log.info("Turned off Live Captions")
        except Exception as e:
            log.info("Could not turn off Live Captions: %s", e)


captions_win = MacCaptionsWindow() if IS_MAC else CaptionsWindow()


def _lc_window():
    win = auto.WindowControl(searchDepth=1, ClassName=CAPTIONS_WINDOW_CLASS)
    return win if win.Exists(0, 0) else None


def _lc_roots(win):
    """The Live Captions window plus its pop-up menu windows (same process)."""
    roots = [win]
    try:
        pid = win.ProcessId
        for w in auto.GetRootControl().GetChildren():
            try:
                if w.ProcessId == pid and w.NativeWindowHandle != win.NativeWindowHandle:
                    roots.append(w)
            except Exception:
                continue
    except Exception:
        pass
    return roots


def _lc_find(win, predicate, depth=14):
    for root in _lc_roots(win):
        for control, _ in _walk(root, depth):
            try:
                if predicate(control):
                    return control
            except Exception:
                continue
    return None


def _activate(control):
    """Press a button or open a menu item without moving the mouse."""
    for getter, action in (("GetInvokePattern", "Invoke"),
                           ("GetExpandCollapsePattern", "Expand"),
                           ("GetTogglePattern", "Toggle")):
        try:
            pattern = getattr(control, getter)()
            if pattern:
                getattr(pattern, action)()
                return True
        except Exception:
            continue
    return False


def _lc_wait(win, pred, seconds=3.0):
    """Look for a Live Captions element for up to a few seconds (menus open slowly,
    especially right after Live Captions starts)."""
    end = time.time() + seconds
    while True:
        found = _lc_find(win, pred)
        if found is not None or time.time() >= end:
            return found
        time.sleep(0.3)


def enable_lc_microphone():
    """Turn on 'Include microphone audio' in Live Captions (it resets on every start).
    Returns 'on', 'already', or an error text."""
    win = _lc_window()
    if not win:
        return "Live Captions is not running"
    name = lambda c: (c.Name or "").strip().lower()
    mic_pred = lambda c: "microphone" in name(c) and c.ControlTypeName in (
        "MenuItemControl", "CheckBoxControl", "ButtonControl", "ListItemControl")
    mic = _lc_find(win, mic_pred)
    opened = False
    if mic is None:
        settings = _lc_find(win, lambda c: c.ControlTypeName in (
            "ButtonControl", "SplitButtonControl", "MenuItemControl") and (
            "setting" in name(c) or "settings" in (c.AutomationId or "").lower()))
        if settings is None:
            return "could not find the Live Captions settings button"
        _activate(settings)
        opened = True
        prefs = _lc_wait(win, lambda c: c.ControlTypeName == "MenuItemControl"
                         and name(c).startswith("preferences"))
        if prefs is None:
            return "could not find Preferences in the Live Captions menu"
        _activate(prefs)
        mic = _lc_wait(win, mic_pred)
        if mic is None:
            return "could not find 'Include microphone audio'"
    try:
        toggle = mic.GetTogglePattern()
        if toggle and toggle.ToggleState == 1:
            result = "already"
        else:
            toggle.Toggle() if toggle else _activate(mic)
            result = "on"
    except Exception:
        result = "on" if _activate(mic) else "could not switch the microphone option"
    if opened:          # close the menu again if it is still open
        try:
            settings_again = _lc_find(win, lambda c: c.ControlTypeName in (
                "ButtonControl", "SplitButtonControl") and "setting" in name(c))
            menu_open = _lc_find(win, lambda c: c.ControlTypeName == "MenuItemControl"
                                 and name(c).startswith("preferences"), depth=10)
            if menu_open is not None and settings_again is not None:
                try:
                    settings_again.GetExpandCollapsePattern().Collapse()
                except Exception:
                    _activate(settings_again)
        except Exception:
            pass
    return result


class LiveCaptionsReader:
    """Windows 11 Live Captions: one text block, no speaker names."""
    name = "Windows Live Captions"

    def __init__(self):
        self.text_box = None
        self.last_raw = None
        self.mic_done_for = None          # Live Captions window we already set up
        self.status = "Live Captions not found - press Win+Ctrl+L"

    MIC_TRIES = 3
    MIC_RETRY_SECONDS = 10

    def ensure_microphone(self, win):
        try:
            handle = win.NativeWindowHandle
        except Exception:
            return
        if self.mic_done_for == handle:
            return
        tries, last = getattr(self, "mic_tries", {}).get(handle, (0, 0.0))
        if tries >= self.MIC_TRIES or time.time() - last < self.MIC_RETRY_SECONDS:
            return
        result = enable_lc_microphone()
        self.mic_tries = {handle: (tries + 1, time.time())}
        log.info("Live Captions microphone: %s (try %d)", result, tries + 1)
        if result in ("on", "already"):
            self.mic_done_for = handle
        if result == "on":
            ui_queue.put(("toast", "Turned on your microphone in Live Captions"))
        elif result != "already":
            ui_queue.put(("toast", "Couldn't turn on the mic in Live Captions: " + result))

    def reset(self):
        self.text_box = None
        self.last_raw = None

    def poll(self):
        """Read once. Returns True while the source is usable."""
        try:
            if self.text_box is None:
                win = auto.WindowControl(searchDepth=1, ClassName=CAPTIONS_WINDOW_CLASS)
                if not win.Exists(0, 0):
                    self.status = "Live Captions not found - press Win+Ctrl+L"
                    return False
                self.ensure_microphone(win)
                candidate = win.TextControl(AutomationId=CAPTIONS_TEXT_ID)
                if not candidate.Exists(0, 0):
                    self.status = "Live Captions open - waiting for speech"
                    return True
                self.text_box = candidate
                self.lc_window = win
                log.info("Connected to Live Captions")
            if getattr(self, "lc_window", None) is not None:
                self.ensure_microphone(self.lc_window)     # retries a failed first try
            raw = self.text_box.Name or ""
            self.status = "Live Captions connected"
            if raw != self.last_raw:
                self.last_raw = raw
                transcript.ingest(raw)
            return True
        except Exception as e:
            if self.text_box is not None:
                log.info("Lost Live Captions: %s", e)
            self.reset()
            self.status = "Live Captions not found - press Win+Ctrl+L"
            return False


BROWSER_CLASSES = ("Chrome_WidgetWin_1",)       # Chrome, Edge, Brave, ...


def _walk(control, max_depth, depth=0):
    """Depth-first walk of a UI Automation subtree."""
    yield control, depth
    if depth >= max_depth:
        return
    try:
        children = control.GetChildren()
    except Exception:
        return
    for child in children:
        yield from _walk(child, max_depth, depth + 1)


# Meet's captions button ("CC"): words in its label, lower case. Meet shows the
# label in the user's language; add more here if a language is missing.
MEET_CC_LABELS = ("captions", "subtítulos", "subtitulos", "sous-titres",
                  "untertitel", "sottotitoli", "legendas", "субтитры")


def meet_key(title):
    """The meeting code from a Meet window title (abc-defg-hij), or the title."""
    m = re.search(r"[a-z]{3}-[a-z]{4}-[a-z]{3}", (title or "").lower())
    return m.group(0) if m else (title or "").lower()


SIDENOTE_VERSION = "2026-11-12 v10"
auto_cc_status = {"text": ""}     # shown by get_status, for troubleshooting


class AutoCaptions:
    """Turns on Meet's captions (CC) for the user. At most two tries per
    meeting, a few seconds apart. Once captions have been on in a meeting it
    never presses again, so turning them off on purpose is respected."""
    MAX_TRIES = 2
    RETRY_SECONDS = 6

    def __init__(self, app="Google Meet", short="Meet"):
        self.app, self.short = app, short
        self.clear()

    def clear(self):
        self.tries = {}          # meeting key -> (count, time of last try)
        self.seen_on = set()     # meetings where captions have been on
        auto_cc_status["text"] = ""

    def captions_on(self, key):
        if key not in self.seen_on:
            self.seen_on.add(key)
            auto_cc_status["text"] = f"{self.short} captions on"

    def attempt(self, key):
        """Number of this try (0 = first), or None if no press is wanted now."""
        if key in self.seen_on:
            return None
        count, last = self.tries.get(key, (0, 0.0))
        if count >= self.MAX_TRIES or time.time() - last < self.RETRY_SECONDS:
            return None
        return count

    def pressed(self, key, attempt, how, ok):
        self.tries[key] = (attempt + 1, time.time())
        auto_cc_status["text"] = (f"{self.short} CC pressed via {how}, try {attempt + 1}"
                                  + ("" if ok else " (press failed)"))
        log.info("Auto captions: %s", auto_cc_status["text"])
        if ok and attempt == 0:
            ui_queue.put(("toast", f"Turning on {self.app} captions"))


class MeetReader:
    """Google Meet captions in Chrome or Edge, with speaker names.

    Meet shows captions in a region labelled 'Captions'. Each block in it holds
    the speaker's name followed by what they are saying."""
    name = "Google Meet"

    def __init__(self):
        self.region = None
        self.window = None
        self.last_search = 0.0
        self.last_ok = 0.0
        self.status = "Google Meet not found"
        self.auto = AutoCaptions()
        self.cc_box = None          # Meet's CC toggle, if seen with captions off
        self.cc_btn = None          # "Turn on captions" button, if seen

    def reset(self):
        self.region = None
        self.window = None

    def _find_meet_window(self):
        for win in auto.GetRootControl().GetChildren():
            try:
                title = (win.Name or "").strip().lower()
                if win.ClassName in BROWSER_CLASSES and (
                        title.startswith("meet") or "google meet" in title
                        or "meet.google.com" in title):
                    return win
            except Exception:
                continue
        return None

    def _find_region(self, win):
        self.cc_box = self.cc_btn = None
        for control, _ in _walk(win, 40):
            try:
                raw = (control.Name or "").strip()
                name = raw.lower()
            except Exception:
                continue
            note_meet_label(raw)
            if name in ("captions", "subtítulos", "sous-titres", "subtitulos") and \
                    control.ControlTypeName in ("GroupControl", "CustomControl",
                                                "PaneControl", "DocumentControl"):
                return control
            kind = self._cc_kind(control, name)
            if kind == "box" and self.cc_box is None:
                self.cc_box = control
            elif kind == "button" and self.cc_btn is None:
                self.cc_btn = control
        return None

    @staticmethod
    def _cc_kind(control, name):
        """'box': Meet's captions toggle, now off. 'button': a "Turn on
        captions" button. None: anything else."""
        if not any(w in name for w in MEET_CC_LABELS):
            return None
        try:
            kind = control.ControlTypeName
        except Exception:
            return None
        if kind not in ("CheckBoxControl", "ButtonControl"):
            return None
        try:
            pattern = control.GetTogglePattern()
        except Exception:
            pattern = None
        if pattern is not None:
            try:
                return "box" if pattern.ToggleState == auto.ToggleState.Off else None
            except Exception:
                return None
        return "button" if name.startswith("turn on") else None

    def _find_cc_button(self, win):
        for control, _ in _walk(win, 40):
            try:
                name = (control.Name or "").strip().lower()
            except Exception:
                continue
            if self._cc_kind(control, name) == "button":
                return control
        return None

    def _auto_turn_on_captions(self):
        """Turn on Meet's captions for the user (UI Automation: no mouse, no keys).
        Current Meet: the CC toggle opens a small menu, and the "Turn on
        captions" button is inside it. Older Meet: the button is on the bar."""
        key = meet_key(self.window.Name if self.window else "")
        attempt = self.auto.attempt(key)
        if attempt is None or (self.cc_box is None and self.cc_btn is None):
            return
        how, ok = "", False
        try:
            button = self.cc_btn
            if button is None:
                pattern = self.cc_box.GetTogglePattern()
                if pattern is not None:
                    pattern.Toggle()
                else:
                    self.cc_box.GetInvokePattern().Invoke()
                how = "menu+"
                for _ in range(10):                 # wait for the menu, up to 2 s
                    time.sleep(0.2)
                    button = self._find_cc_button(self.window)
                    if button is not None:
                        break
            if button is not None:
                ok = bool(button.GetInvokePattern().Invoke())
                how += "button"
            else:
                how += "no button"
        except Exception as e:
            log.info("Could not press Meet captions: %s", e)
        self.auto.pressed(key, attempt, how, ok)

    def _blocks(self):
        blocks = []
        for block in self.region.GetChildren():
            texts = []
            for control, _ in _walk(block, 8):
                try:
                    if control.ControlTypeName == "TextControl":
                        t = (control.Name or "").strip()
                        if t and (not texts or texts[-1] != t):
                            texts.append(t)
                except Exception:
                    continue
            if not texts:
                continue
            if len(texts) == 1:
                blocks.append(("", texts[0]))
            else:
                blocks.append((texts[0], " ".join(texts[1:])))
        return blocks

    def poll(self):
        now = time.time()
        try:
            if self.region is None:
                if now - self.last_search < 4:
                    return False
                self.last_search = now
                self.window = self._find_meet_window()
                if self.window is None:
                    self.status = "Google Meet not found"
                    return False
                self.region = self._find_region(self.window)
                if self.region is None:
                    self.status = "Google Meet open - turn on captions (CC button)"
                    self._auto_turn_on_captions()
                    return False
                log.info("Connected to Google Meet captions")
                self.auto.captions_on(meet_key(self.window.Name))
                # Captions already on screen were captured before (or by the other
                # source): mark them as seen instead of recording them again.
                if transcript.count_lines():
                    transcript.skip_visible = True
            if not self.region.Exists(0, 0):
                raise RuntimeError("captions region gone")
            transcript.ingest_blocks(self._blocks())
            self.status = "Google Meet captions connected"
            self.last_ok = now
            return True
        except Exception as e:
            if self.region is not None:
                log.info("Lost Google Meet captions: %s", e)
            self.reset()
            self.status = "Google Meet captions lost"
            return False


# ---------------------------------------------------------------------------
# macOS: read Live Captions and Google Meet (Chrome) through the Accessibility API
# ---------------------------------------------------------------------------
if IS_MAC:
    from AppKit import NSWorkspace
    from ApplicationServices import (AXUIElementCreateApplication,
                                     AXUIElementCopyAttributeValue,
                                     AXUIElementSetAttributeValue,
                                     AXIsProcessTrustedWithOptions,
                                     kAXTrustedCheckOptionPrompt)

    MAC_LC_BUNDLE = "com.apple.accessibility.LiveTranscriptionAgent"
    MAC_BROWSERS = ("com.google.Chrome", "com.microsoft.edgemac", "com.brave.Browser",
                    "company.thebrowser.Browser", "com.google.Chrome.canary")

    def ax(el, name):
        try:
            err, val = AXUIElementCopyAttributeValue(el, name, None)
            return val if err == 0 else None
        except Exception:
            return None

    def ax_walk(el, max_depth, depth=0):
        yield el, depth
        if depth >= max_depth:
            return
        for child in ax(el, "AXChildren") or []:
            yield from ax_walk(child, max_depth, depth + 1)

    def mac_apps(bundle_ids):
        out = []
        for app in NSWorkspace.sharedWorkspace().runningApplications():
            if str(app.bundleIdentifier() or "") in bundle_ids:
                out.append(app)
        return out

    def mac_trusted(prompt=False):
        try:
            return bool(AXIsProcessTrustedWithOptions({kAXTrustedCheckOptionPrompt: prompt}))
        except Exception:
            return False


class MacLiveCaptionsReader:
    """macOS Live Captions: lines of text in a window, no speaker names."""
    name = LC_NAME

    def __init__(self):
        self.region = None
        self.last_raw = None
        self.status = "Live Captions not found - " + LC_HINT

    def reset(self):
        self.region = None
        self.last_raw = None

    def _find_region(self):
        apps = mac_apps((MAC_LC_BUNDLE,))
        if not apps:
            return None
        app = AXUIElementCreateApplication(apps[0].processIdentifier())
        for win in ax(app, "AXWindows") or []:
            if ax(win, "AXIdentifier") == "AXLiveCaptionsWindow" or \
                    str(ax(win, "AXTitle") or "") == "Live Captions":
                for el, _ in ax_walk(win, 6):
                    if str(ax(el, "AXDescription") or "") == "Captions":
                        return el
        return None

    def ensure_microphone(self, _win=None):
        pass                        # macOS Live Captions has one source; nothing to switch

    def poll(self):
        try:
            if not mac_trusted():
                self.status = "Needs Accessibility permission"
                return False
            if self.region is None or ax(self.region, "AXRole") is None:
                self.region = self._find_region()
                if self.region is None:
                    self.status = "Live Captions not found - " + LC_HINT
                    return False
                log.info("Connected to macOS Live Captions")
            parts = [str(ax(c, "AXValue") or "") for c in ax(self.region, "AXChildren") or []]
            raw = " ".join(p for p in parts if p.strip())
            if not raw:
                self.status = "Live Captions open - waiting for speech"
                return True
            self.status = "Live Captions connected"
            if raw != self.last_raw:
                self.last_raw = raw
                transcript.ingest(raw, speaker="Others" if mic.status == "on" else "")
            return True
        except Exception as e:
            log.info("Lost macOS Live Captions: %s", e)
            self.reset()
            self.status = "Live Captions not found - " + LC_HINT
            return False


class MacMeetReader:
    """Google Meet captions in Chrome (or Edge, Brave, Arc) on macOS, with names."""
    name = "Google Meet"

    def __init__(self):
        self.region = None
        self.last_search = 0.0
        self.status = "Google Meet not found"
        self._asked = set()
        self.auto = AutoCaptions()
        self.key = ""

    def reset(self):
        self.region = None

    @staticmethod
    def _cc_kind(el):
        """'box': Meet's captions toggle, now off. 'button': a "Turn on
        captions" button. None: anything else."""
        role = ax(el, "AXRole")
        if role not in ("AXCheckBox", "AXButton"):
            return None
        label = (str(ax(el, "AXTitle") or "") + " " +
                 str(ax(el, "AXDescription") or "")).lower().strip()
        if not any(w in label for w in MEET_CC_LABELS):
            return None
        if role == "AXCheckBox":
            return "box" if str(ax(el, "AXValue")) in ("0", "False") else None
        return "button" if label.startswith("turn on") else None

    def _find_cc_button(self, win):
        for el, _ in ax_walk(win, 60):
            if self._cc_kind(el) == "button":
                return el
        return None

    def _auto_turn_on_captions(self, win, cc_box, cc_btn):
        """Turn on Meet's captions for the user (Accessibility API, no mouse/keys).
        Current Meet: the CC toggle opens a small menu, and the "Turn on
        captions" button is inside it. Older Meet: the button is on the bar."""
        attempt = self.auto.attempt(self.key)
        if attempt is None or (cc_box is None and cc_btn is None):
            return
        how, ok = "", False
        try:
            from ApplicationServices import AXUIElementPerformAction
            button = cc_btn
            if button is None:
                AXUIElementPerformAction(cc_box, "AXPress")    # opens the menu
                how = "menu+"
                for _ in range(10):                 # wait for the menu, up to 2 s
                    time.sleep(0.2)
                    button = self._find_cc_button(win)
                    if button is not None:
                        break
            if button is not None:
                ok = AXUIElementPerformAction(button, "AXPress") == 0
                how += "button"
            else:
                how += "no button"
        except Exception as e:
            log.info("Could not press Meet captions: %s", e)
        self.auto.pressed(self.key, attempt, how, ok)

    def _find_region(self):
        for app in mac_apps(MAC_BROWSERS):
            pid = app.processIdentifier()
            el_app = AXUIElementCreateApplication(pid)
            if pid not in self._asked:          # ask the browser to expose page content
                self._asked.add(pid)
                for flag in ("AXManualAccessibility", "AXEnhancedUserInterface"):
                    try:
                        AXUIElementSetAttributeValue(el_app, flag, True)
                    except Exception:
                        pass
            for win in ax(el_app, "AXWindows") or []:
                title = str(ax(win, "AXTitle") or "").lower()
                if not (title.startswith("meet") or "google meet" in title):
                    continue
                self.key = meet_key(title)
                cc_box = cc_btn = None
                for el, _ in ax_walk(win, 60):
                    note_meet_label(str(ax(el, "AXTitle") or "") or
                                    str(ax(el, "AXDescription") or ""))
                    if ax(el, "AXRole") == "AXGroup" and (
                            str(ax(el, "AXTitle") or "") == "Captions" or
                            str(ax(el, "AXDescription") or "") == "Captions"):
                        if ax(el, "AXChildren"):
                            return el
                    kind = self._cc_kind(el)
                    if kind == "box" and cc_box is None:
                        cc_box = el
                    elif kind == "button" and cc_btn is None:
                        cc_btn = el
                self.status = "Google Meet open - turn on captions (CC button)"
                self._auto_turn_on_captions(win, cc_box, cc_btn)
        return None

    def _blocks(self):
        blocks = []
        for block in ax(self.region, "AXChildren") or []:
            texts = []
            for el, _ in ax_walk(block, 8):
                if ax(el, "AXRole") == "AXStaticText":
                    t = str(ax(el, "AXValue") or "")
                    if t.strip():
                        texts.append(t.strip())
            if not texts:
                continue
            if len(texts) == 1:
                blocks.append(("", texts[0]))
            else:
                blocks.append((texts[0], " ".join(texts[1:])))
        return blocks

    def poll(self):
        now = time.time()
        try:
            if self.region is None or ax(self.region, "AXRole") is None:
                self.region = None
                if now - self.last_search < 4:
                    return False
                self.last_search = now
                self.status = "Google Meet not found"
                self.region = self._find_region()
                if self.region is None:
                    return False
                log.info("Connected to Google Meet captions (macOS)")
                self.auto.captions_on(self.key)
                if transcript.count_lines():
                    transcript.skip_visible = True
            transcript.ingest_blocks(self._blocks())
            self.status = "Google Meet captions connected"
            return True
        except Exception as e:
            log.info("Lost Google Meet captions: %s", e)
            self.reset()
            self.status = "Google Meet captions lost"
            return False


# ---------------------------------------------------------------------------
# Zoom in the browser (Zoom's web client, app.zoom.us), Windows and Mac
# ---------------------------------------------------------------------------
# Captions are one rolling line in the page; Sidenote turns them on with
# "Show Captions" (on the bar, or under More) once per meeting.
ZOOM_CAPTION_BOX = "live-transcription-subtitle__box"
ZOOM_SHOW_CAPTIONS = "Show Captions"
ZOOM_MORE = "More meeting control"
ZOOM_IGNORE = {"captions are on", "captions are off"}
ZOOM_BROWSERS_WIN = ("chrome.exe", "msedge.exe", "brave.exe", "opera.exe", "vivaldi.exe")
NAMED_SOURCES = ("Google Meet", "Zoom", "Microsoft Teams")   # sources with speaker names
SPEAKER_LINE = re.compile(r"^([A-Z][\w.'\- ]{1,30}):\s+(\S.*)$")


def _continues(old, new):
    """True if the new caption text goes on from the old one: Zoom grows the line
    while someone speaks, and trims its start when it gets long."""
    o, n = norm(old), norm(new)
    if not o or not n:
        return False
    return n.startswith(o[:20]) or o[-25:] in n


class CaptionStream:
    """A caption line that grows while someone speaks and is replaced when the
    next line starts. Finished sentences are saved as they come; the rest of a
    line when it is replaced or lost."""

    def __init__(self):
        self.reset()

    def reset(self):
        self.text, self.speaker = "", ""

    @staticmethod
    def split(texts):
        """(speaker, text). Zoom may show a name as its own item, or 'Name: text'."""
        texts = [t for t in texts if t.strip().lower() not in ZOOM_IGNORE]
        if not texts:
            return "", ""
        if len(texts) >= 2 and len(texts[0]) <= 40 and len(texts[0].split()) <= 4 \
                and not re.search(r"[.!?,:]", texts[0]) and texts[0][:1].isupper():
            return texts[0], " ".join(texts[1:])
        m = SPEAKER_LINE.match(" ".join(texts))
        if m and len(m.group(1).split()) <= 4:
            return m.group(1).strip(), m.group(2)
        return "", " ".join(texts)

    @staticmethod
    def merge(old, new):
        """The whole line so far. When Zoom trims the start of a long line, put
        the trimmed part back: new = (end of old) + more words."""
        if not old or norm(new).startswith(norm(old)[:20]):
            return new
        ow, nw = old.split(), new.split()
        key = lambda w: norm(w)
        for skip in (0, 1):                  # the first new word may be cut ('e migration')
            rest = nw[skip:]
            for i in range(max(0, len(ow) - len(rest)), len(ow) - 2):
                tail = ow[i:]
                if [key(w) for w in tail] == [key(w) for w in rest[:len(tail)]]:
                    return " ".join(ow + rest[len(tail):])
        return new

    def feed(self, texts):
        speaker, text = self.split(texts)
        if not text:
            return
        if self.text and (speaker != self.speaker or not _continues(self.text, text)):
            self.flush()                     # a new line started: the old one is done
        text = self.merge(self.text, text) if self.text else text
        self.text, self.speaker = text, speaker
        transcript.ingest(text, speaker=speaker)

    def flush(self):
        if self.text:
            transcript.ingest(self.text, speaker=self.speaker, final=True)
        self.reset()


class ZoomWebReader:
    """Zoom meetings in the browser on Windows (Chrome, Edge, ...)."""
    name = "Zoom"
    MISSING_SECONDS = 8          # caption box gone this long = captions off / lost

    def __init__(self):
        self.window = self.box = None
        self.last_search = self.box_seen = 0.0
        self.status = "Zoom not found"
        self.auto = AutoCaptions("Zoom", "Zoom")
        self.stream = CaptionStream()

    def reset(self):
        self.window = self.box = None
        self.stream.reset()

    HINT_EVERY = 120             # background-tab reminder at most every 2 minutes

    def _hint_background_tab(self, now):
        """Browsers only expose the tab on screen. If a Zoom meeting is open in
        a background tab, say so (a toast: it doesn't take focus)."""
        if now - getattr(self, "hint_at", 0) < self.HINT_EVERY:
            return
        for win in auto.GetRootControl().GetChildren():
            try:
                if win.ClassName not in BROWSER_CLASSES or \
                        _win_process_name(win.ProcessId) not in ZOOM_BROWSERS_WIN:
                    continue
                for c, _ in _walk(win, 12):
                    if c.ControlTypeName == "TabItemControl" and \
                            (c.Name or "").lower().startswith("zoom meeting"):
                        self.hint_at = now
                        ui_queue.put(("toast", "Zoom is in a background tab: bring it to "
                                               "the front so Sidenote can read its captions"))
                        return
            except Exception:
                continue

    def _find_window(self):
        for win in auto.GetRootControl().GetChildren():
            try:
                if win.ClassName in BROWSER_CLASSES and "zoom" in (win.Name or "").lower() \
                        and _win_process_name(win.ProcessId) in ZOOM_BROWSERS_WIN:
                    return win
            except Exception:
                continue
        return None

    def _scan(self, root, want=None):
        """Caption box and the buttons Sidenote may press, in one walk."""
        found = {"box": None, "show": None, "more": None, "hide": None}
        for c, _ in _walk(root, 80):
            try:
                kind, name = c.ControlTypeName, (c.Name or "")
                if ZOOM_CAPTION_BOX in (c.ClassName or ""):
                    found["box"] = c
                elif kind == "ButtonControl":
                    if name == ZOOM_SHOW_CAPTIONS:
                        found["show"] = c
                    elif name == "Hide Captions":
                        found["hide"] = c
                    elif name.startswith(ZOOM_MORE):
                        found["more"] = c
                note_meet_label(name)
            except Exception:
                continue
            if want and found[want] is not None:
                break
        return found

    def _turn_on(self, found):
        """Press Show Captions (bar, or More > Show Captions), once per meeting."""
        key = (self.window.Name or "zoom") if self.window else "zoom"
        attempt = self.auto.attempt(key)
        if attempt is None or (found["show"] is None and found["more"] is None):
            return
        how, ok = "", False
        try:
            if found["show"] is not None:
                found["show"].GetInvokePattern().Invoke()
                how, ok = "bar button", True
            else:
                menu = found["more"].GetExpandCollapsePattern()
                menu.Expand()
                how = "More menu"
                try:
                    for _ in range(10):                  # wait for the menu, up to 2 s
                        time.sleep(0.2)
                        show = self._scan(self.window, want="show")["show"]
                        if show is not None:
                            show.GetInvokePattern().Invoke()
                            ok = True
                            break
                finally:
                    try:
                        if menu.ExpandCollapseState != 0:
                            menu.Collapse()
                    except Exception:
                        pass
        except Exception as e:
            log.info("Could not turn on Zoom captions: %s", e)
        self.auto.pressed(key, attempt, how, ok)

    def _texts(self):
        out = []
        for c, _ in _walk(self.box, 8):
            try:
                if c.ControlTypeName == "TextControl" and (c.Name or "").strip():
                    out.append(c.Name.strip())
            except Exception:
                continue
        return out

    def poll(self):
        now = time.time()
        try:
            if self.box is None or not self.box.Exists(0, 0):
                self.box = None
                if self.window is not None and now - self.box_seen < self.MISSING_SECONDS:
                    # between lines the box can vanish for a moment
                    if now - self.last_search >= 1.5:
                        self.last_search = now
                        self.box = self._scan(self.window, want="box")["box"]
                    if self.box is None:
                        return True
                else:
                    if self.window is not None:
                        log.info("Lost Zoom captions")
                        self.stream.flush()
                        self.window = None
                    if now - self.last_search < 4:
                        return False
                    self.last_search = now
                    self.window = self._find_window()
                    if self.window is None:
                        self.status = "Zoom not found"
                        self._hint_background_tab(now)
                        return False
                    found = self._scan(self.window)
                    if found["box"] is None:
                        if found["more"] is None and found["show"] is None:
                            self.status = "Zoom open - not in a meeting"
                        else:
                            self.status = "Zoom open - turn on captions (More > Show Captions)"
                            self._turn_on(found)
                        self.window = None
                        return False
                    self.box = found["box"]
                    log.info("Connected to Zoom captions")
                    self.auto.captions_on(self.window.Name or "zoom")
                    if transcript.count_lines():
                        transcript.skip_visible = True
            self.box_seen = now
            self.stream.feed(self._texts())
            self.status = "Zoom captions connected"
            return True
        except Exception as e:
            log.info("Lost Zoom captions: %s", e)
            self.stream.flush()
            self.reset()
            self.status = "Zoom captions lost"
            return False


class MacZoomWebReader:
    """Zoom meetings in the browser on macOS (Chrome, Edge, Brave, Arc, Safari)."""
    name = "Zoom"
    MISSING_SECONDS = 8

    def __init__(self):
        self.window = self.box = None
        self.last_search = self.box_seen = 0.0
        self.status = "Zoom not found"
        self.auto = AutoCaptions("Zoom", "Zoom")
        self.stream = CaptionStream()
        self._asked = set()

    def reset(self):
        self.window = self.box = None
        self.stream.reset()

    @staticmethod
    def _label(el):
        return (str(ax(el, "AXTitle") or "") or str(ax(el, "AXDescription") or "")).strip()

    HINT_EVERY = 120

    def _hint_background_tab(self, now):
        """A Zoom meeting in a background browser tab can't be read: say so."""
        if now - getattr(self, "hint_at", 0) < self.HINT_EVERY:
            return
        for app in mac_apps(MAC_BROWSERS + ("com.apple.Safari",)):
            el_app = AXUIElementCreateApplication(app.processIdentifier())
            for win in ax(el_app, "AXWindows") or []:
                for el, _ in ax_walk(win, 12):
                    if ax(el, "AXRole") in ("AXRadioButton", "AXTab") and \
                            self._label(el).lower().startswith("zoom meeting"):
                        self.hint_at = now
                        ui_queue.put(("toast", "Zoom is in a background tab: bring it to "
                                               "the front so Sidenote can read its captions"))
                        return

    def _find_window(self):
        for app in mac_apps(MAC_BROWSERS + ("com.apple.Safari",)):
            pid = app.processIdentifier()
            el_app = AXUIElementCreateApplication(pid)
            if pid not in self._asked:            # ask the browser to expose page content
                self._asked.add(pid)
                for flag in ("AXManualAccessibility", "AXEnhancedUserInterface"):
                    try:
                        AXUIElementSetAttributeValue(el_app, flag, True)
                    except Exception:
                        pass
            for win in ax(el_app, "AXWindows") or []:
                if "zoom" in str(ax(win, "AXTitle") or "").lower():
                    return win
        return None

    def _scan(self, root, want=None):
        found = {"box": None, "show": None, "more": None, "hide": None}
        for el, _ in ax_walk(root, 80):
            classes = ax(el, "AXDOMClassList") or []
            if any(ZOOM_CAPTION_BOX in str(c) for c in classes):
                found["box"] = el
            elif ax(el, "AXRole") in ("AXButton", "AXPopUpButton", "AXMenuButton"):
                label = self._label(el)
                if label == ZOOM_SHOW_CAPTIONS:
                    found["show"] = el
                elif label == "Hide Captions":
                    found["hide"] = el
                elif label.startswith(ZOOM_MORE):
                    found["more"] = el
                note_meet_label(label)
            if want and found[want] is not None:
                break
        return found

    def _turn_on(self, found):
        key = str(ax(self.window, "AXTitle") or "zoom")
        attempt = self.auto.attempt(key)
        if attempt is None or (found["show"] is None and found["more"] is None):
            return
        how, ok = "", False
        try:
            from ApplicationServices import AXUIElementPerformAction
            if found["show"] is not None:
                ok = AXUIElementPerformAction(found["show"], "AXPress") == 0
                how = "bar button"
            else:
                AXUIElementPerformAction(found["more"], "AXPress")       # opens the menu
                how = "More menu"
                for _ in range(10):
                    time.sleep(0.2)
                    show = self._scan(self.window, want="show")["show"]
                    if show is not None:
                        ok = AXUIElementPerformAction(show, "AXPress") == 0
                        break
                if self._scan(self.window, want="hide")["hide"] is None and \
                        self._scan(self.window, want="show")["show"] is not None:
                    AXUIElementPerformAction(found["more"], "AXPress")   # close the menu
        except Exception as e:
            log.info("Could not turn on Zoom captions: %s", e)
        self.auto.pressed(key, attempt, how, ok)

    def _texts(self):
        out = []
        for el, _ in ax_walk(self.box, 8):
            if ax(el, "AXRole") == "AXStaticText":
                t = str(ax(el, "AXValue") or "").strip()
                if t:
                    out.append(t)
        return out

    def poll(self):
        now = time.time()
        try:
            if self.box is None or ax(self.box, "AXRole") is None:
                self.box = None
                if self.window is not None and now - self.box_seen < self.MISSING_SECONDS:
                    if now - self.last_search >= 1.5:
                        self.last_search = now
                        self.box = self._scan(self.window, want="box")["box"]
                    if self.box is None:
                        return True
                else:
                    if self.window is not None:
                        log.info("Lost Zoom captions (macOS)")
                        self.stream.flush()
                        self.window = None
                    if now - self.last_search < 4:
                        return False
                    self.last_search = now
                    self.window = self._find_window()
                    if self.window is None:
                        self.status = "Zoom not found"
                        self._hint_background_tab(now)
                        return False
                    found = self._scan(self.window)
                    if found["box"] is None:
                        if found["more"] is None and found["show"] is None:
                            self.status = "Zoom open - not in a meeting"
                        else:
                            self.status = "Zoom open - turn on captions (More > Show Captions)"
                            self._turn_on(found)
                        self.window = None
                        return False
                    self.box = found["box"]
                    log.info("Connected to Zoom captions (macOS)")
                    self.auto.captions_on(str(ax(self.window, "AXTitle") or "zoom"))
                    if transcript.count_lines():
                        transcript.skip_visible = True
            self.box_seen = now
            self.stream.feed(self._texts())
            self.status = "Zoom captions connected"
            return True
        except Exception as e:
            log.info("Lost Zoom captions (macOS): %s", e)
            self.stream.flush()
            self.reset()
            self.status = "Zoom captions lost"
            return False


# ---------------------------------------------------------------------------
# Microsoft Teams (the app, or Teams in the browser), Windows and Mac
# ---------------------------------------------------------------------------
# Teams labels are translated, so Sidenote uses Teams' element ids, which are
# the same in every language. Captions: More > Language and speech > Show live
# captions (a switch). Each caption is a 'ChatMessageCompact' item: name, text.
TEAMS_IDS = {"more": "callingButtons-showMoreBtn", "lang": "LanguageSpeechMenuControl-id",
             "cc": "closed-captions-button", "dismiss": "captions-panel-dismiss-button",
             "hangup": "hangup-button"}
TEAMS_CAPTION_ITEM = "ChatMessageCompact__body"
TEAMS_PROCESSES_WIN = ("ms-teams.exe", "teams.exe")
TEAMS_BUNDLES_MAC = ("com.microsoft.teams2", "com.microsoft.teams")


class TeamsReader:
    """Microsoft Teams meetings on Windows: the Teams app or Teams in a browser."""
    name = "Microsoft Teams"
    MISSING_SECONDS = 8          # captions panel gone this long = captions off / lost

    def __init__(self):
        self.window = self.panel = None
        self.last_search = self.panel_seen = 0.0
        self.status = "Teams not found"
        self.auto = AutoCaptions("Microsoft Teams", "Teams")

    def reset(self):
        self.window = self.panel = None

    HINT_EVERY = 120

    def _hint_background_tab(self, now):
        """A Teams meeting in a background browser tab can't be read: say so."""
        if now - getattr(self, "hint_at", 0) < self.HINT_EVERY:
            return
        for win in auto.GetRootControl().GetChildren():
            try:
                if win.ClassName not in BROWSER_CLASSES or \
                        _win_process_name(win.ProcessId) not in ZOOM_BROWSERS_WIN:
                    continue
                for c, _ in _walk(win, 12):
                    if c.ControlTypeName == "TabItemControl" and \
                            "microsoft teams" in (c.Name or "").lower():
                        self.hint_at = now
                        ui_queue.put(("toast", "Teams is in a background tab: bring it to "
                                               "the front so Sidenote can read its captions"))
                        return
            except Exception:
                continue

    def _windows(self):
        for win in auto.GetRootControl().GetChildren():
            try:
                proc = _win_process_name(win.ProcessId)
                if proc in TEAMS_PROCESSES_WIN or (
                        win.ClassName in BROWSER_CLASSES and proc in ZOOM_BROWSERS_WIN
                        and "microsoft teams" in (win.Name or "").lower()):
                    yield win
            except Exception:
                continue

    def _scan(self, root, want=None):
        found = {k: None for k in TEAMS_IDS}
        ids = {v: k for k, v in TEAMS_IDS.items()}
        for c, _ in _walk(root, 90):
            try:
                key = ids.get(c.AutomationId or "")
                if key and found[key] is None:
                    found[key] = c
                note_meet_label(c.Name or "")
            except Exception:
                continue
            if want and found[want] is not None:
                break
        return found

    @staticmethod
    def _panel_of(dismiss):
        parent = dismiss.GetParentControl()
        return parent.GetParentControl() if parent is not None else None

    def _turn_on(self, found):
        """More > Language and speech > live captions switch, once per meeting."""
        key = self.window.Name or "teams"
        attempt = self.auto.attempt(key)
        if attempt is None or found["more"] is None:
            return
        how, ok, opened = "More > Language and speech", False, []
        try:
            more = found["more"].GetExpandCollapsePattern()
            more.Expand()
            opened.append(more)
            lang = None
            for _ in range(10):
                time.sleep(0.2)
                lang = self._scan(self.window, want="lang")["lang"]
                if lang is not None:
                    break
            if lang is not None:
                sub = lang.GetExpandCollapsePattern()
                sub.Expand()
                opened.append(sub)
                for _ in range(10):
                    time.sleep(0.2)
                    cc = self._scan(self.window, want="cc")["cc"]
                    if cc is not None:
                        toggle = cc.GetTogglePattern()
                        if toggle.ToggleState == 0:
                            toggle.Toggle()
                        ok = True
                        break
        except Exception as e:
            log.info("Could not turn on Teams captions: %s", e)
        finally:
            for menu in reversed(opened):           # close the menus again
                try:
                    if menu.ExpandCollapseState != 0:
                        menu.Collapse()
                except Exception:
                    pass
        self.auto.pressed(key, attempt, how, ok)

    def _blocks(self):
        blocks = []
        for c, _ in _walk(self.panel, 25):
            try:
                if TEAMS_CAPTION_ITEM not in (c.ClassName or ""):
                    continue
                texts = [t.Name.strip() for t, _ in _walk(c, 6)
                         if t.ControlTypeName == "TextControl" and (t.Name or "").strip()]
            except Exception:
                continue
            if len(texts) >= 2:
                blocks.append((texts[0], " ".join(texts[1:])))
            elif texts:
                blocks.append(("", texts[0]))
        return blocks

    def poll(self):
        now = time.time()
        try:
            if self.panel is None or not self.panel.Exists(0, 0):
                self.panel = None
                if self.window is not None and now - self.panel_seen < self.MISSING_SECONDS:
                    if now - self.last_search >= 1.5:
                        self.last_search = now
                        dismiss = self._scan(self.window, want="dismiss")["dismiss"]
                        self.panel = self._panel_of(dismiss) if dismiss is not None else None
                    if self.panel is None:
                        return True
                else:
                    if self.window is not None:
                        log.info("Lost Teams captions")
                        self.window = None
                    if now - self.last_search < 4:
                        return False
                    self.last_search = now
                    found = None
                    for win in self._windows():
                        f = self._scan(win)
                        if f["hangup"] is not None or f["dismiss"] is not None:
                            self.window, found = win, f
                            break
                    if found is None:
                        self.status = "Teams not found"
                        self._hint_background_tab(now)
                        return False
                    if found["dismiss"] is None:
                        self.status = "Teams open - turn on live captions (More > Language and speech)"
                        self._turn_on(found)
                        self.window = None
                        return False
                    self.panel = self._panel_of(found["dismiss"])
                    log.info("Connected to Teams captions")
                    self.auto.captions_on(self.window.Name or "teams")
                    if transcript.count_lines():
                        transcript.skip_visible = True
            self.panel_seen = now
            transcript.ingest_blocks(self._blocks())
            self.status = "Microsoft Teams captions connected"
            return True
        except Exception as e:
            log.info("Lost Teams captions: %s", e)
            self.reset()
            self.status = "Microsoft Teams captions lost"
            return False


class MacTeamsReader:
    """Microsoft Teams meetings on macOS: the Teams app or Teams in a browser."""
    name = "Microsoft Teams"
    MISSING_SECONDS = 8

    def __init__(self):
        self.window = self.panel = None
        self.last_search = self.panel_seen = 0.0
        self.status = "Teams not found"
        self.auto = AutoCaptions("Microsoft Teams", "Teams")
        self._asked = set()

    def reset(self):
        self.window = self.panel = None

    HINT_EVERY = 120

    def _hint_background_tab(self, now):
        """A Teams meeting in a background browser tab can't be read: say so."""
        if now - getattr(self, "hint_at", 0) < self.HINT_EVERY:
            return
        for app in mac_apps(MAC_BROWSERS + ("com.apple.Safari",)):
            el_app = AXUIElementCreateApplication(app.processIdentifier())
            for win in ax(el_app, "AXWindows") or []:
                for el, _ in ax_walk(win, 12):
                    label = (str(ax(el, "AXTitle") or "") or str(ax(el, "AXDescription") or ""))
                    if ax(el, "AXRole") in ("AXRadioButton", "AXTab") and \
                            "microsoft teams" in label.lower():
                        self.hint_at = now
                        ui_queue.put(("toast", "Teams is in a background tab: bring it to "
                                               "the front so Sidenote can read its captions"))
                        return

    def _windows(self):
        browsers = MAC_BROWSERS + ("com.apple.Safari",)
        for app in mac_apps(TEAMS_BUNDLES_MAC + browsers):
            pid = app.processIdentifier()
            el_app = AXUIElementCreateApplication(pid)
            if pid not in self._asked:            # ask the app to expose its web content
                self._asked.add(pid)
                for flag in ("AXManualAccessibility", "AXEnhancedUserInterface"):
                    try:
                        AXUIElementSetAttributeValue(el_app, flag, True)
                    except Exception:
                        pass
            in_browser = str(app.bundleIdentifier()) in browsers
            for win in ax(el_app, "AXWindows") or []:
                if not in_browser or "microsoft teams" in str(ax(win, "AXTitle") or "").lower():
                    yield win

    def _scan(self, root, want=None):
        found = {k: None for k in TEAMS_IDS}
        ids = {v: k for k, v in TEAMS_IDS.items()}
        for el, _ in ax_walk(root, 90):
            key = ids.get(str(ax(el, "AXDOMIdentifier") or ""))
            if key and found[key] is None:
                found[key] = el
            note_meet_label(str(ax(el, "AXDescription") or "") or str(ax(el, "AXTitle") or ""))
            if want and found[want] is not None:
                break
        return found

    @staticmethod
    def _panel_of(dismiss):
        parent = ax(dismiss, "AXParent")
        return ax(parent, "AXParent") if parent is not None else None

    def _turn_on(self, found):
        key = str(ax(self.window, "AXTitle") or "teams")
        attempt = self.auto.attempt(key)
        if attempt is None or found["more"] is None:
            return
        how, ok = "More > Language and speech", False
        try:
            from ApplicationServices import AXUIElementPerformAction
            AXUIElementPerformAction(found["more"], "AXPress")          # opens the menu
            lang = cc = None
            for _ in range(10):
                time.sleep(0.2)
                lang = self._scan(self.window, want="lang")["lang"]
                if lang is not None:
                    break
            if lang is not None:
                for action in ("AXPress", "AXShowMenu"):               # opens the submenu
                    AXUIElementPerformAction(lang, action)
                    for _ in range(5):
                        time.sleep(0.2)
                        cc = self._scan(self.window, want="cc")["cc"]
                        if cc is not None:
                            break
                    if cc is not None:
                        break
            if cc is not None:
                if str(ax(cc, "AXValue")) in ("0", "False", "None"):
                    AXUIElementPerformAction(cc, "AXPress")
                ok = True
            if self._scan(self.window, want="lang")["lang"] is not None:
                AXUIElementPerformAction(found["more"], "AXPress")      # close the menu
        except Exception as e:
            log.info("Could not turn on Teams captions: %s", e)
        self.auto.pressed(key, attempt, how, ok)

    def _blocks(self):
        blocks = []
        for el, _ in ax_walk(self.panel, 25):
            classes = ax(el, "AXDOMClassList") or []
            if not any(TEAMS_CAPTION_ITEM in str(c) for c in classes):
                continue
            texts = [str(ax(t, "AXValue") or "").strip() for t, _ in ax_walk(el, 6)
                     if ax(t, "AXRole") == "AXStaticText"]
            texts = [x for x in texts if x]
            if len(texts) >= 2:
                blocks.append((texts[0], " ".join(texts[1:])))
            elif texts:
                blocks.append(("", texts[0]))
        return blocks

    def poll(self):
        now = time.time()
        try:
            if self.panel is None or ax(self.panel, "AXRole") is None:
                self.panel = None
                if self.window is not None and now - self.panel_seen < self.MISSING_SECONDS:
                    if now - self.last_search >= 1.5:
                        self.last_search = now
                        dismiss = self._scan(self.window, want="dismiss")["dismiss"]
                        self.panel = self._panel_of(dismiss) if dismiss is not None else None
                    if self.panel is None:
                        return True
                else:
                    if self.window is not None:
                        log.info("Lost Teams captions (macOS)")
                        self.window = None
                    if now - self.last_search < 4:
                        return False
                    self.last_search = now
                    found = None
                    for win in self._windows():
                        f = self._scan(win)
                        if f["hangup"] is not None or f["dismiss"] is not None:
                            self.window, found = win, f
                            break
                    if found is None:
                        self.status = "Teams not found"
                        self._hint_background_tab(now)
                        return False
                    if found["dismiss"] is None:
                        self.status = "Teams open - turn on live captions (More > Language and speech)"
                        self._turn_on(found)
                        self.window = None
                        return False
                    self.panel = self._panel_of(found["dismiss"])
                    log.info("Connected to Teams captions (macOS)")
                    self.auto.captions_on(str(ax(self.window, "AXTitle") or "teams"))
                    if transcript.count_lines():
                        transcript.skip_visible = True
            self.panel_seen = now
            transcript.ingest_blocks(self._blocks())
            self.status = "Microsoft Teams captions connected"
            return True
        except Exception as e:
            log.info("Lost Teams captions (macOS): %s", e)
            self.reset()
            self.status = "Microsoft Teams captions lost"
            return False


class MicTranscriber:
    """Mac: transcribes the user's own microphone on the computer (Whisper), while
    macOS Live Captions hears the other people (it listens to one source at a
    time). Lines are saved as 'You: ...' (shown with the user's name).

    The mic is reached through Claude's microphone permission (Sidenote runs
    inside Claude). Sidenote asks macOS for it first, so the user gets the normal
    "Claude would like to access the microphone" prompt; without asking, macOS
    only hands over silence. If audio is still pure silence, the footer says so.

    status: off, asking, blocked, loading, on, silent, missing, error."""
    MODEL = "base"            # multilingual, ~145 MB, downloaded once
    RATE = 16000
    SILENT_SECONDS = 4        # this long of exact zeros = macOS gives us silence
    LOCK_LANGUAGE_PROB = 0.8  # detected this surely -> keep that language

    def __init__(self):
        self.thread = None
        self.running = threading.Event()
        self.status = "off"
        self.model = None
        self.language = None  # detected, then kept for the rest of the session
        self.detail = ""      # last error, for the logs and get_status

    def available(self):
        try:
            import faster_whisper, sounddevice, numpy  # noqa: F401
            return True
        except Exception as e:
            self.detail = f"packages missing: {e}"
            return False

    def start(self):
        if self.running.is_set():
            return
        if not self.available():
            self.status = "missing"
            log.info("Microphone: %s", self.detail)
            return
        self.running.set()
        self.language = None
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def stop(self):
        self.running.clear()
        if self.status not in ("blocked", "silent", "missing", "error"):
            self.status = "off"

    # --- permission -------------------------------------------------------------
    def permission(self, ask=True, timeout=60):
        """'granted', 'denied', 'restricted' or 'unknown'. Asks macOS once when it
        has never been asked (the prompt names Claude, which runs Sidenote)."""
        try:
            from AVFoundation import AVCaptureDevice, AVMediaTypeAudio
        except Exception as e:
            log.info("Microphone: AVFoundation unavailable (%s)", e)
            return "unknown"
        names = {0: "not_determined", 1: "restricted", 2: "denied", 3: "granted"}
        state = names.get(int(AVCaptureDevice.authorizationStatusForMediaType_(AVMediaTypeAudio)),
                          "unknown")
        log.info("Microphone permission: %s", state)
        if state != "not_determined" or not ask:
            return state
        self.status = "asking"
        answered, result = threading.Event(), {}

        def done(granted):
            result["granted"] = bool(granted)
            answered.set()
        AVCaptureDevice.requestAccessForMediaType_completionHandler_(AVMediaTypeAudio, done)
        answered.wait(timeout)
        state = "granted" if result.get("granted") else (
            "denied" if answered.is_set() else "not_determined")
        log.info("Microphone permission after asking: %s", state)
        return state

    # --- transcription ----------------------------------------------------------
    def _load(self):
        if self.model is None:
            self.status = "loading"
            ui_queue.put(("toast", "Preparing microphone transcription (one-time download)…"))
            from faster_whisper import WhisperModel
            self.model = WhisperModel(self.MODEL, device="cpu", compute_type="int8")
        return self.model

    def _transcribe(self, audio):
        segments, info = self._load().transcribe(
            audio, language=self.language, beam_size=1, vad_filter=False,
            condition_on_previous_text=False)
        words = []
        for seg in segments:
            if seg.no_speech_prob > 0.6 or seg.avg_logprob < -1.0:
                continue
            words.append(seg.text.strip())
        text = " ".join(w for w in words if w)
        # Auto-detect the language, then keep it once Whisper is sure: short
        # phrases are often mis-detected on their own.
        if self.language is None and text and \
                getattr(info, "language_probability", 0) >= self.LOCK_LANGUAGE_PROB:
            self.language = info.language
            log.info("Microphone language: %s", self.language)
        return text

    def _run(self):
        state = self.permission()
        if state != "granted" and state != "unknown":
            self.status = "blocked"
            self.detail = f"permission {state}"
            ui_queue.put(("toast", "Microphone blocked: allow Claude in Privacy & Security "
                                   "> Microphone"))
            self.running.clear()
            return
        import numpy as np
        import sounddevice as sd
        blocks = queue.Queue()
        try:
            self._load()
            device = (sd.query_devices(kind="input") or {}).get("name")
            log.info("Microphone: model ready, input device %r", device)
            stream = sd.InputStream(samplerate=self.RATE, channels=1, dtype="float32",
                                    blocksize=int(self.RATE * 0.1),
                                    callback=lambda data, frames, t, st: blocks.put(data.copy()))
            stream.start()
        except Exception as e:
            log.info("Microphone transcription unavailable: %s", e)
            self.detail = str(e)[:200]
            ui_queue.put(("toast", "Mic didn't start: " + str(e)[:120]))
            self.status = "error"
            self.running.clear()
            return
        self.status = "on"
        log.info("Microphone transcription started")
        peak, peak_t, started = 0.0, time.time(), time.time()
        any_signal = False
        noise, speech, silence, heard = 0.004, [], 0.0, 0.0
        try:
            while self.running.is_set():
                try:
                    block = blocks.get(timeout=0.5)
                except queue.Empty:
                    continue
                if not any_signal:
                    any_signal = bool(np.any(block))
                    if not any_signal and time.time() - started >= self.SILENT_SECONDS:
                        # exact zeros: macOS is withholding the microphone
                        self.status = "silent"
                        self.detail = "microphone delivers only silence"
                        log.info("Microphone: only silence (all zeros) after %ss",
                                 self.SILENT_SECONDS)
                        ui_queue.put(("toast", "The microphone gives Sidenote only silence"))
                        break
                level = float(np.sqrt(np.mean(block ** 2)))
                peak = max(peak, level)
                if time.time() - peak_t >= 30:
                    log.info("Microphone: peak level last 30 s %.4f", peak)
                    peak, peak_t = 0.0, time.time()
                talking = level > max(0.012, noise * 3.0)
                if not talking and not speech:
                    noise = 0.95 * noise + 0.05 * level          # follow the room noise
                if talking:
                    speech.append(block); silence = 0.0; heard += 0.1
                    transcript.pending = "You: …"
                elif speech:
                    speech.append(block); silence += 0.1
                long_enough = len(speech) * 0.1 >= 12
                if speech and (silence >= 0.8 or long_enough):
                    if heard >= 0.4:
                        audio = np.concatenate(speech)[:, 0]
                        try:
                            text = self._transcribe(audio)
                            if text:
                                transcript.add_spoken("You", text)
                        except Exception as e:
                            log.info("Transcription error: %s", e)
                    speech, silence, heard = [], 0.0, 0.0
                    if transcript.pending == "You: …":
                        transcript.pending = ""
        finally:
            try:
                stream.stop(); stream.close()
            except Exception:
                pass
            if self.status == "on":
                self.status = "off"
            self.running.clear()
            log.info("Microphone transcription stopped (%s)", self.status)


mic = MicTranscriber()
MIC_NEEDS_USER = ("blocked", "silent", "missing", "error")   # don't retry these by itself


def update_mic(on_live_captions):
    """Mic on while Sidenote is open, a meeting is running and the source is Live
    Captions (Meet's captions already include the user). After 'blocked',
    'silent', 'missing' or 'error' it waits for the user (click in the footer)."""
    want = window_open.is_set() and live.mode == "record" and on_live_captions \
        and not transcript.ended_at
    if want and not mic.running.is_set() and mic.status not in MIC_NEEDS_USER:
        mic.start()
    elif not want and mic.running.is_set():
        mic.stop()


def retry_mic():
    """Footer click: open the Microphone privacy page if access is blocked,
    then let update_mic try again."""
    if mic.status in ("blocked", "silent") and IS_MAC:
        try:
            import subprocess
            subprocess.Popen(["open", "x-apple.systempreferences:com.apple.preference."
                                      "security?Privacy_Microphone"])
        except Exception as e:
            log.info("Could not open Privacy settings: %s", e)
    mic.status = "off"


def captions_loop():
    """Picks the best caption source and keeps reading it.

    Prefers captions with speaker names: Google Meet, Zoom in the browser,
    then Microsoft Teams (app or browser).
    If neither is available, or its captions are lost for a few seconds, uses
    the computer's Live Captions (plus the user's mic on Mac)."""
    with uia_thread():
        meet = MacMeetReader() if IS_MAC else MeetReader()
        zoom = MacZoomWebReader() if IS_MAC else ZoomWebReader()
        teams = MacTeamsReader() if IS_MAC else TeamsReader()
        named = (meet, zoom, teams)
        windows = MacLiveCaptionsReader() if IS_MAC else LiveCaptionsReader()
        active = None              # reader currently feeding the transcript
        lost_since = None
        while True:
            if IS_MAC and MAC_MIC_ENABLED:
                update_mic(active is not None and active not in named)
            if not window_open.is_set() or live.mode != "record":
                for reader in named:
                    reader.reset()
                    reader.auto.clear()
                windows.reset()
                active = None
                transcript.status = "Sidenote closed" if not window_open.is_set() \
                    else "Not recording"
                transcript.source = ""
                time.sleep(POLL_SECONDS)
                continue

            if active in named:
                if active.poll():
                    lost_since = None
                else:
                    lost_since = lost_since or time.time()
                    if time.time() - lost_since > 6:
                        lost = active.name
                        active = windows
                        windows.reset()
                        transcript.pending = ""
                        transcript.skip_visible = True   # don't copy old on-screen text
                        captions_win.ensure_running()
                        transcript.source_note = f"{lost} captions lost, switched to {LC_SHORT}"
                        ui_queue.put(("toast", f"{lost} captions lost \u00b7 switched to {LC_SHORT}"))
                        log.info("Fell back to %s", LC_NAME)
            else:
                # Try Meet, Zoom and Teams every few seconds; use one as soon as it works
                for reader in named:
                    if reader.poll():
                        transcript.pending = ""
                        active = reader
                        lost_since = None
                        transcript.source_note = ""
                        ui_queue.put(("toast", f"Connected to {reader.name} captions"))
                        break
                else:
                    if active is None:
                        active = windows
                    windows.poll()

            if active in named and not IS_MAC:
                try:
                    lc = _lc_window()
                    if lc is not None:
                        windows.ensure_microphone(lc)   # ready for a fallback
                except Exception:
                    pass
            transcript.source = active.name if active else ""
            transcript.status = active.status if active else windows.status
            captions_win.tick()
            time.sleep(POLL_SECONDS)


def _mac_dump(path, bundles, title_filter=None):
    lines = [f"Accessibility allowed: {mac_trusted(prompt=True)}"]
    for app in mac_apps(bundles):
        el_app = AXUIElementCreateApplication(app.processIdentifier())
        for win in ax(el_app, "AXWindows") or []:
            title = str(ax(win, "AXTitle") or "")
            lines.append(f"===== {app.localizedName()} window {title!r} =====")
            if title_filter and not title_filter(title.lower()):
                continue
            for el, d in ax_walk(win, 60):
                if len(lines) > 8000:
                    break
                lines.append(f"{'  ' * min(d, 30)}{ax(el, 'AXRole')} title={str(ax(el, 'AXTitle'))[:50]!r} "
                             f"desc={str(ax(el, 'AXDescription'))[:50]!r} value={str(ax(el, 'AXValue'))[:100]!r}")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    return path


def debug_dump_live_captions(path):
    """Write the UI tree of Live Captions (with its settings menu open) to a file."""
    if IS_MAC:
        return _mac_dump(path, (MAC_LC_BUNDLE,))
    lines = []
    with auto.UIAutomationInitializerInThread():
        win = _lc_window()
        if not win:
            lines.append("Live Captions is not running")
        else:
            def dump(title):
                lines.append(f"===== {title} =====")
                for root in _lc_roots(win):
                    for control, depth in _walk(root, 25):
                        try:
                            lines.append(f"{'  ' * depth}{control.ControlTypeName} "
                                         f"name={(control.Name or '')[:80]!r} "
                                         f"id={control.AutomationId!r} class={control.ClassName!r}")
                        except Exception:
                            continue
            dump("closed")
            settings = _lc_find(win, lambda c: c.ControlTypeName in (
                "ButtonControl", "SplitButtonControl", "MenuItemControl") and
                "setting" in (c.Name or "").lower())
            if settings:
                _activate(settings)
                time.sleep(0.8)
                dump("settings menu open")
                prefs = _lc_find(win, lambda c: c.ControlTypeName == "MenuItemControl"
                                 and (c.Name or "").lower().startswith("preferences"))
                if prefs:
                    _activate(prefs)
                    time.sleep(0.8)
                    dump("preferences open")
                _activate(settings)
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines[:8000]))
    return path


# Capturing Teams and Zoom windows, to build caption readers for them
CALL_APPS = {
    # app: (Mac bundle ids, Windows process names, window-title words, in a browser?)
    "teams": (("com.microsoft.teams2", "com.microsoft.teams") +
              (MAC_BROWSERS + ("com.apple.Safari", "org.mozilla.firefox") if IS_MAC else ()),
              ("ms-teams.exe", "teams.exe"), ("microsoft teams",), True),
    "zoom": (MAC_BROWSERS + ("com.apple.Safari", "org.mozilla.firefox", "us.zoom.xos")
             if IS_MAC else (),
             ("zoom.exe",), ("zoom",), True),
}
CAPTION_HINTS = ("caption", "transcript", "subtitle", "cc ", "live caption")


def _win_process_name(pid):
    """Executable name of a Windows process ('ms-teams.exe'), or ''."""
    try:
        import ctypes
        from ctypes import wintypes
        handle = ctypes.windll.kernel32.OpenProcess(0x1000, False, pid)   # query limited info
        if not handle:
            return ""
        try:
            buf = ctypes.create_unicode_buffer(1024)
            size = wintypes.DWORD(1024)
            if ctypes.windll.kernel32.QueryFullProcessImageNameW(handle, 0, buf, ctypes.byref(size)):
                return os.path.basename(buf.value).lower()
        finally:
            ctypes.windll.kernel32.CloseHandle(handle)
    except Exception:
        pass
    return ""


def debug_dump_call_app(path, app):
    """Write the accessibility tree of the Teams or Zoom (browser) windows to a
    file, with a summary of caption-like elements first. Used to build their
    readers. Privacy: other windows are not named, and for browsers only the web
    page is captured (never bookmarks, tabs, extensions or the profile)."""
    bundles, processes, title_words, browser = CALL_APPS[app]
    lines, hints = [], []
    found = [0]

    def note(depth, text):
        found[0] += 1
        lines.append(f"{'  ' * min(depth, 30)}{text}")
        if any(h in text.lower() for h in CAPTION_HINTS) and len(hints) < 60:
            hints.append(f"line {len(lines)}: {text.strip()[:160]}")

    if IS_MAC:
        browsers = MAC_BROWSERS + ("com.apple.Safari", "org.mozilla.firefox")
        lines.append(f"Accessibility allowed: {mac_trusted(prompt=True)}")
        for running in mac_apps(bundles):
            el_app = AXUIElementCreateApplication(running.processIdentifier())
            for flag in ("AXManualAccessibility", "AXEnhancedUserInterface"):
                try:
                    AXUIElementSetAttributeValue(el_app, flag, True)    # expose web content
                except Exception:
                    pass
            time.sleep(1.5)
            in_browser = str(running.bundleIdentifier()) in browsers
            for win in ax(el_app, "AXWindows") or []:
                title = str(ax(win, "AXTitle") or "")
                if title_words and in_browser and not any(w in title.lower() for w in title_words):
                    continue
                lines.append(f"===== {running.localizedName()} "
                             f"({running.bundleIdentifier()}) window {title!r} =====")
                # In a browser, only the web page: never bookmarks, tabs or profile
                roots = [el for el, _ in ax_walk(win, 40) if ax(el, "AXRole") == "AXWebArea"] \
                    if in_browser else [win]
                if in_browser and not roots:
                    lines.append("(the page content is not exposed yet: try again in a few seconds)")
                for root in roots:
                    for el, d in ax_walk(root, 70):
                        if len(lines) > 20000:
                            lines.append("... truncated")
                            break
                        note(d, f"{ax(el, 'AXRole')} title={str(ax(el, 'AXTitle'))[:60]!r} "
                                f"desc={str(ax(el, 'AXDescription'))[:60]!r} "
                                f"value={str(ax(el, 'AXValue'))[:160]!r} "
                                f"id={str(ax(el, 'AXIdentifier'))[:40]!r}")
    else:
        with auto.UIAutomationInitializerInThread():
            targets, others = [], 0
            for w in auto.GetRootControl().GetChildren():
                try:
                    proc = _win_process_name(w.ProcessId)
                    title = (w.Name or "").lower()
                    in_browser = w.ClassName in BROWSER_CLASSES + ("MozillaWindowClass",) \
                        and proc not in ("code.exe", "claude.exe", "spotify.exe")
                    if proc in processes:
                        targets.append((w, False))
                    elif browser and in_browser and any(t in title for t in title_words):
                        targets.append((w, True))
                    else:
                        others += 1
                except Exception:
                    continue
            lines.append(f"Windows captured: {len(targets)}; other windows (not captured): {others}")

            def pages(win):
                return [c for c, _ in _walk(win, 40) if c.ControlTypeName == "DocumentControl"]

            for win, in_browser in targets:
                lines += ["", f"===== {win.Name!r} [{win.ClassName}] ====="]
                if in_browser:
                    pages(win)                   # first look makes Chrome expose the page
                    time.sleep(2.0)
                roots = pages(win) if in_browser else [win]
                if in_browser and not roots:
                    lines.append("(the page content is not exposed yet: try again in a few seconds)")
                for root in roots:
                    for control, depth in _walk(root, 60):
                        if len(lines) > 20000:
                            lines.append("... truncated")
                            break
                        try:
                            name = (control.Name or "").replace("\n", " ")[:160]
                            note(depth, f"{control.ControlTypeName} name={name!r} "
                                        f"id={control.AutomationId!r} class={control.ClassName!r}")
                        except Exception:
                            continue
    summary = [f"Sidenote {SIDENOTE_VERSION} - {app} window capture, "
               f"{'macOS' if IS_MAC else 'Windows'}",
               f"Caption-like elements ({len(hints)}):"] + hints + ["", "Full tree:"]
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(summary + lines))
    return path, found[0], len(hints)


def debug_dump_meet(path):
    """Write the UI tree of the Meet window to a file (for troubleshooting)."""
    if IS_MAC:
        return _mac_dump(path, MAC_BROWSERS,
                         lambda t: t.startswith("meet") or "google meet" in t)
    lines = []
    with auto.UIAutomationInitializerInThread():
        reader = MeetReader()
        roots = auto.GetRootControl().GetChildren()
        lines.append("Top-level windows:")
        for w in roots:
            try:
                lines.append(f"  [{w.ClassName}] {w.Name!r}")
            except Exception:
                pass
        win = reader._find_meet_window()
        lines.append("")
        lines.append(f"Meet window: {win.Name if win else None!r}")
        if win:
            for control, depth in _walk(win, 45):
                if len(lines) > 6000:
                    lines.append("... truncated")
                    break
                try:
                    name = (control.Name or "").replace("\n", " ")[:120]
                    lines.append(f"{'  ' * depth}{control.ControlTypeName} name={name!r} "
                                 f"id={control.AutomationId!r} class={control.ClassName!r}")
                except Exception:
                    continue
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    return path


# ---------------------------------------------------------------------------
# MCP server
# ---------------------------------------------------------------------------
mcp = FastMCP(
    "sidenote",
    instructions=(
        "You are Sidenote, a live meeting assistant for the user. The transcript comes "
        "from Google Meet, Zoom (browser) or Microsoft Teams captions (lines start with the "
        "speaker's name when the app shows it; the user's own "
        "lines show the user's name, or 'You' while it is unknown) or, as a fallback, "
        "the computer's Live Captions (no names; on Mac the lines are 'Others' and the "
        "user's own microphone lines carry the user's name). The meeting "
        "info tells you which source is active. Captions may contain small recognition "
        "errors; read them charitably.\n\n"
        "OPENING: the Sidenote window is hidden until the user asks for it. When the "
        "user says 'start Sidenote' or 'open Sidenote', call open_sidenote: the window "
        "opens with two tabs, New meeting (where the user starts recording) and Past "
        "meetings. "
        "Pass new_meeting=true only if the user explicitly asked to record or start a "
        "meeting now. Pass the meeting title, agenda, role, goals and participants if the "
        "user gave them. Start the wait_for_question loop right away in every case, "
        "without asking anything in the chat. Never close the Sidenote window yourself: "
        "call close_sidenote only when the user explicitly asks to close it.\n\n"
        "HISTORY: every meeting is saved in Documents/Sidenote, and these tools read them "
        "even when the window is closed (also from a normal chat): list_meetings (cheap, "
        "call it first), find_items (action items, decisions, questions across meetings), "
        "get_meeting (recap and lists; transcript only with include_transcript=true), "
        "search_transcripts (snippets) and update_item (status only). Always name the "
        "source meeting and date. Keep answers compact; load transcripts only when the "
        "user asks for detail. Action items stay open until the user ticks them or "
        "explicitly asks you to close them: never close one on your own inference, never "
        "suggest closing items during a meeting, and if the user's request could match more "
        "than one open item, ask which one first. When you close one, pass the user's "
        "request as evidence.\n\n"
        "MEETING INFO: the meeting title, agenda, the user's role, goals and participants "
        "are sent to you with every question. Always use them: tie your answers to the "
        "agenda, the user's role and goals. When a message from the user contains new "
        "meeting info (a title, an extra agenda item, their role, a goal, participant "
        "names), save it first with update_meeting_info, add_agenda_items or "
        "add_participants, then confirm briefly in the overlay. If the user hasn't "
        "given a title, you may set a short 'subject' with update_meeting_info once the "
        "topic is clear from the transcript; never invent a title, agenda, role or "
        "participants. The user's name and role are remembered between meetings: never "
        "ask for them again when the meeting info has them. If you know the user's name "
        "and the meeting info says it is not known yet, pass it once as user_name.\n\n"
        "LIVE MODE: after opening Sidenote (or when the user says 'continue'), call "
        "wait_for_question in a loop. When it returns a QUESTION, answer it, send the "
        "answer with show_suggestion, then call wait_for_question again right away. "
        "When it returns NO_QUESTION, just call it again. Do not write long chat "
        "messages between calls; the user reads the overlay, not the chat. When it "
        "returns STOP, CLOSED or IDLE, follow its instructions and stop the loop. "
        "HISTORY QUESTION results come from the History screen: answer them about past "
        "meetings. During a recording, answer from the live transcript unless the question "
        "refers to the past ('last time', 'before', 'in October', a meeting name) or the live "
        "transcript can't answer it; then check past meetings with the cheap history tools "
        "first and name the source meeting and date. If unclear, answer from the live "
        "meeting and add one line offering to check past meetings.\n\n"
        "Answers in the overlay: 1-3 short, concrete points (questions to ask, "
        "uncovered agenda items, missing decisions or owners), under 70 words, plain "
        "text, in the language the user wrote in.\n\n"
        "ACTION ITEMS AND QUESTIONS: keep two lists for the user. (1) When your answer "
        "suggests questions for the user to ask, also save each one with "
        "add_questions_to_ask (short, one line each). (2) When the transcript shows a "
        "commitment or task (someone will do something), save it with add_action_item. "
        "The owner is always a person's name: the speaker who committed ('I'll do X'), "
        "else the person addressed ('Leon, can you...'), else a name said with the task; "
        "'Team' for team-wide items; never 'you' or 'someone' (leave it empty if unsure: "
        "the user picks it in one click). Pass the due date as said. Never duplicate items that "
        "are already in the lists sent with each question, and don't re-suggest "
        "questions marked 'asked'. If a saved question was clearly asked in the "
        "transcript, mark it with mark_done. These saves are silent: do not call "
        "show_suggestion just to report them.\n\n"
        "SCAN: wait_for_question returns SCAN with new transcript lines as soon as "
        "something relevant may have been said. Quickly check them and save only clear "
        "items: action items, questions the user should ask, agenda topics someone "
        "stated (if there is no agenda yet this becomes the agenda; otherwise add only "
        "topics that are not already on it), and agenda items that are now clearly "
        "covered (mark_done kind 'agenda'). Then immediately call wait_for_question "
        "again. Never call show_suggestion for a scan.\n\n"
        "AUTO TITLE: once per meeting, if there is still no title after a few minutes, "
        "a SCAN adds an AUTO TITLE note. Follow it: set a short title (and 1-2 agenda "
        "topics only if the agenda is empty) with update_meeting_info, never changing "
        "what the user typed or stated.\n\n"
        "CONTEXT: (1) Right after open_sidenote, FIRST check whether you have Jira "
        "and/or Confluence tools in this conversation (tool names containing jira, "
        "atlassian or confluence; count deferred tools too and load them via tool "
        "search if needed) and call set_context_sources accordingly. Then call "
        "wait_for_question in a loop. (2) As soon as the meeting topic is known (title, "
        f"agenda or the first transcript lines), search once for it and add up to "
        f"{PRELOAD_MAX} of the most useful hits with add_context_item: project home, "
        "product/spec page, active sprint dashboard or epic, pages for agenda features, "
        "previous meeting notes and decisions. (3) During the meeting, when a new "
        "feature, epic, ticket key or document is mentioned and is not in the Context "
        f"list yet, search once and add the best 1-{MAX_PER_TOPIC} hits. wait_for_question "
        "also returns CONTEXT when the agenda changes or ticket numbers are mentioned. "
        "If the user says aloud something like 'do I have context' or 'pull up X', "
        "treat it as a request even though it came through the transcript. (4) The "
        f"Context list holds at most {MAX_CONTEXT_ITEMS} items; when it is full, stop "
        "adding and answer explicit lookups with show_suggestion. (5) Search per topic, "
        "not per transcript line, and never repeat a search for a topic already "
        "covered (Atlassian searches cost credits). (6) Only read from Jira and "
        "Confluence; never create or edit anything there unless the user explicitly "
        "asks and confirms.\n\n"
        "RECAP: when asked for a recap, or when the meeting ends, call get_full_transcript "
        "and save the recap with save_recap in parts: summary (3 lines at most), "
        "by_person (one line per person in the meeting, the user by name included: what "
        "they reported, what they own, what they asked or are blocked on; 'Attended; no "
        "update captured.' if they said little), decisions, and open_questions. Open "
        "debates: when people stated different positions on the same topic without a "
        "conclusion, add one line to open_questions: '- Topic: Name1 wants X; Name2 "
        "wants Y (no conclusion)'. Sidenote adds the Action items, the To-ask questions "
        "and the Context list to the file itself: do not repeat them. The file is read "
        "by other people: real names (never 'You' or 'you' for a person) and real dates "
        "(never 'today' or 'tomorrow'). This applies to every meeting type."
    ),
)


# --- Core operations (run in the primary instance, which owns the overlay) ---
END_TOKEN = "\x00END_MEETING\x00"
MISSED_TOKEN = "\x00WHAT_DID_I_MISS\x00"
MISSED_MINUTES = 3


def _end_instructions(kind):
    if kind == "END":
        return ("END: the user clicked 'End meeting'. Call get_full_transcript, write the "
                "recap and save it with save_recap in parts (summary, by_person, decisions, "
                "open_questions incl. open debates; see the save_recap description). It is "
                "shown in the Sidenote window automatically. Then call wait_for_question "
                "again: for 15 minutes Sidenote "
                "stays ready in case the user starts a new meeting from the window; after that "
                "wait_for_question returns IDLE and you stop. Stop when it returns STOP, "
                "CLOSED or IDLE.")
    count, _ = transcript.stats()
    if count and not transcript.context["recap"]:
        recap = ("Before stopping: call get_full_transcript, write the recap and save it "
                 "with save_recap in parts (summary, by_person, decisions, open_questions), "
                 "then tell the user in one line that the "
                 f"meeting file is saved ({transcript.file_path or 'Documents/Sidenote'}).")
    else:
        recap = "Then stop."
    if kind == "STOP":
        return f"STOP: the user ended Sidenote live mode. {recap} Stop calling wait_for_question."
    return (f"CLOSED: the Sidenote window was closed, which ends the meeting. {recap} Stop calling "
            "wait_for_question. The user can say 'open Sidenote' to bring it back.")


# Appended to every open_sidenote result. Some clients (e.g. cloud sessions reaching
# this server through the desktop bridge) never see the server instructions, so the
# result itself must tell Claude to start listening, or the overlay stays on
# "Connecting to Claude...".
LISTEN_NOW = (
    "\n\nLISTEN NOW: immediately call wait_for_question and keep calling it in a loop "
    "(after every answer, SCAN or NO_QUESTION) until it returns STOP, CLOSED or IDLE. "
    "Never close the Sidenote window yourself. "
    "Do NOT stop to ask the user for a title, agenda, role or participants in the chat; "
    "missing meeting info is fine. If none was given, you may show one short tip in the "
    "overlay with show_suggestion, then start the loop. Do not write chat messages "
    "between calls; the user reads the overlay.")


# Added to every open_sidenote result: first the Jira/Confluence step, then
# the listen-now instruction (the overlay only shows Claude as connected while
# the chat keeps calling wait_for_question).
LIVE_NEXT = ("\n\nFIRST STEP (required): if you have Jira or Confluence tools in this "
             "conversation (including deferred ones; load them via tool search if needed), "
             "call set_context_sources with jira=true and/or confluence=true now, or with "
             "both false if you have neither. If you have them, search them for the "
             f"meeting topic and add up to {PRELOAD_MAX} of the best hits with "
             "add_context_item." + LISTEN_NOW)


def core_open_sidenote(new_meeting=False, title="", agenda="", role="", goals="",
                       participants="", user_name=""):
    """Opens the window on its Home screen (Record a meeting / History). Records
    right away only if the user asked for it (new_meeting=True)."""
    if user_name:
        set_user_name(user_name, "claude")
    info = {k: v for k, v in (("title", title), ("agenda", agenda), ("role", role),
                              ("goals", goals), ("participants", participants)) if v}
    live.last_activity = time.time()
    if window_open.is_set():
        recording = live.mode == "record" and not transcript.ended_at
        if new_meeting and not recording:
            ui_queue.put(("record", info))
            return "Recording a new meeting in the open Sidenote window." + LIVE_NEXT
        if info and recording:
            core_update_meeting_info(**info)
            return "Sidenote is open and recording. Meeting info updated." + LIVE_NEXT
        if info:
            live.pending_info.update(info)
        where = "recording a meeting" if recording else f"on its {live.mode.capitalize()} screen"
        return f"Sidenote is already open, {where}." + LIVE_NEXT
    live.pending_info = info
    live.record_on_open = bool(new_meeting)
    live.mode = "record" if new_meeting else "home"
    open_request.set()
    for _ in range(50):
        if window_open.is_set():
            break
        time.sleep(0.1)
    if new_meeting:
        return "Sidenote is open and recording a new meeting." + LIVE_NEXT
    return ("Sidenote is open on its New meeting tab (past meetings are on the other tab); "
            "the user starts the meeting there. Don't ask them anything in the chat." + LIVE_NEXT)


def end_if_needed():
    """Closing Sidenote ends the meeting (end time + 'MEETING ENDED' in the file)."""
    count, _ = transcript.stats()
    if count and not transcript.ended_at:
        transcript.end_meeting()


def core_close_sidenote():
    if not window_open.is_set():
        return "Sidenote is already closed."
    end_if_needed()
    ui_queue.put(("close", None))
    return "Sidenote closed and the meeting ended."


def _autofill_ready():
    """True once the meeting has run 3+ min, has 30+ spoken lines or 100+ spoken
    words, still has no title, and the AUTO TITLE note hasn't been sent yet."""
    if live.autofill_sent or transcript.context["title"] or transcript.ended_at:
        return False
    elapsed = (datetime.datetime.now() - transcript.started).total_seconds()
    if elapsed < AUTOFILL_AFTER_SECONDS:
        return False
    lines, words = transcript.spoken_stats()
    return lines >= AUTOFILL_MIN_LINES or words >= AUTOFILL_MIN_WORDS


def _autofill_note():
    """One-time AUTO TITLE note for a SCAN: ask Claude for a short title (and
    1-2 agenda items only if the agenda is empty). Sent at most once per meeting."""
    if not _autofill_ready():
        return ""
    c = transcript.context
    live.autofill_sent = True
    if c["agenda"]:
        fields = ("ONLY the title field: a short meeting title, 8 words max. The agenda "
                  "already exists: do not pass agenda")
    else:
        fields = ("ONLY title (a short meeting title, 8 words max) and agenda (1 or 2 "
                  "main topics actually discussed, one per line; never 3 or more)")
    return ("\n\nAUTO TITLE (one time, required): the meeting has no title yet. Besides "
            f"the scan, call update_meeting_info with {fields}. Leave every other field "
            "empty. If someone stated the meeting's title or agenda in the transcript, "
            "use their words. Captions can be messy: still pick the best short title "
            "(a broad one like 'Sidenote testing' is fine) rather than skipping.\n\n"
            "--- TRANSCRIPT, LAST 10 MIN (for the title) ---\n"
            f"{transcript.since(10) or '(nothing captured)'}")


def context_guidance(full=True):
    """Appended to wait_for_question results. full=False (NO_QUESTION) only
    gives the set_context_sources reminder, so an idle loop never asks for
    repeated searches (Atlassian searches cost credits)."""
    sources = transcript.sources
    if sources is None:
        return ("\n\nREMINDER: set_context_sources has not been called yet. If you have "
                "Jira or Confluence tools, call it now, then preload context.")
    if not full or not any(sources.values()):
        return ""
    left = transcript.context_slots_left()
    if left <= 0:
        return (f"\n\nContext list is full ({MAX_CONTEXT_ITEMS}). Do not add more; "
                "answer explicit lookups with show_suggestion.")
    if left == MAX_CONTEXT_ITEMS:
        return ("\n\nContext list is empty. If the meeting topic is known, search "
                f"Jira/Confluence for it once and add up to {min(PRELOAD_MAX, left)} items.")
    return (f"\n\nContext: {left} slot(s) left. If the new transcript names a feature, "
            "epic, ticket or document that isn't listed yet, search once and add the best "
            f"1-{MAX_PER_TOPIC}. Spoken requests for context (e.g. 'pull up X') count.")


def _scan_if_ready():
    """Return a SCAN request when new lines are worth checking right away:
    a cue phrase was said (a few seconds after the sentence ends), or enough
    new talk has piled up since the last check."""
    if transcript.ended_at:
        return None
    now = time.time()
    total = transcript.count_lines()
    new_lines = total - live.scanned_upto
    since_scan = now - live.last_scan
    sources = transcript.sources or {}
    has_sources = any(sources.values())
    # Context refresh (title/agenda changed) or ticket numbers mentioned
    if has_sources and since_scan >= 10 and (transcript.context_dirty or transcript.tickets_new):
        tickets, transcript.tickets_new = list(transcript.tickets_new), []
        refresh = transcript.context_dirty
        transcript.context_dirty = False
        live.last_scan = now
        tools = " and ".join(k.capitalize() for k, v in sources.items() if v)
        parts = []
        if refresh:
            parts.append("The meeting title or agenda changed: search " + tools +
                         " for pages, epics and tickets related to them")
        if tickets:
            parts.append("Ticket numbers were mentioned: " + ", ".join(tickets) +
                         " - look them up")
        return ("CONTEXT: " + ". ".join(parts) + ". Save the useful findings with "
                "add_context_item (one per ticket/page: short title, source, a one-line "
                "detail such as status, owner, due date or the key decision, and the link). "
                f"Add at most {MAX_PER_TOPIC} per topic; the list holds "
                f"{MAX_CONTEXT_ITEMS} items and has {transcript.context_slots_left()} "
                "slot(s) left. If something important "
                "comes up (a blocker, a conflict with what is said), you may also add a "
                "question with add_questions_to_ask. Do not call show_suggestion. Then call "
                "wait_for_question again.\n\n"
                f"--- MEETING INFO ---\n{transcript.context_text()}")
    if not has_sources:
        transcript.tickets_new = []
    # The one-time auto title goes out with a SCAN as soon as it is due,
    # without waiting for a cue phrase or the regular scan
    autofill_due = _autofill_ready() and since_scan >= 10
    if new_lines <= 0 and not autofill_due:
        return None
    cue = transcript.cue_at > live.last_scan and now - transcript.cue_at >= CUE_DELAY_SECONDS
    regular = new_lines >= 8 and since_scan >= REGULAR_SCAN_SECONDS
    if not ((cue and since_scan >= MIN_SCAN_GAP_SECONDS) or regular or autofill_due):
        return None
    start = max(0, live.scanned_upto - 2)          # 2 lines of overlap for context
    live.scanned_upto = total
    live.last_scan = now
    return ("SCAN: new transcript lines. Quickly save, if clearly present: action items "
            "(add_action_item; owner = a person's name: who committed, else who was asked, "
            "else a name said with it, 'Team' for everyone; empty if unsure), questions "
            "the user should ask (add_questions_to_ask), "
            "agenda topics someone stated (add_agenda_items, never duplicates), and agenda "
            "items now clearly covered (mark_done kind 'agenda'). Usually there is little or "
            "nothing to save. Do not call show_suggestion. Then call wait_for_question "
            "again.\n\n"
            f"--- CURRENT LISTS ---\n{transcript.context_text()}\n\n"
            f"--- NEW TRANSCRIPT ---\n{transcript.lines_from(start)}"
            + _autofill_note() + context_guidance())


def _history_idle():
    return live.mode != "record" and time.time() - live.last_activity > HISTORY_IDLE_SECONDS


HISTORY_IDLE_TEXT = ("IDLE: no questions for 15 minutes while Sidenote wasn't recording. Stop "
                     "calling wait_for_question. Tell the user in one short line that Sidenote "
                     "is idle and that typing 'open Sidenote' in Claude reconnects it.")


def _history_question(q):
    meeting_id = q.get("meeting_id") or ""
    e = find_meeting(meeting_id) if meeting_id else None
    scope = (f"the meeting \u201c{e['title']}\u201d ({_day_label(e)}, id {e['id']})" if e
             else "all past meetings")
    text = (f"HISTORY QUESTION (asked on Sidenote's Past meetings tab, about {scope}): "
            f"{q.get('text', '')}\n\n"
            "Answer from the saved meetings with the history tools. Start cheap: "
            "list_meetings, find_items, get_meeting (no transcript). Load a transcript "
            "(get_meeting with include_transcript=true, or search_transcripts) only if the "
            "user asks for detail the recap doesn't have. Name the source meeting and date for "
            "everything you say (e.g. 'from the Nov 5 sync with Lee'). Short plain text, under "
            "120 words. Change an item's status only if the user explicitly asks (update_item "
            "with their words as evidence); if more than one item could match, ask which one "
            "first. Send the answer with show_suggestion (it appears in the Past meetings tab), then "
            "call wait_for_question again.")
    if e:
        text += "\n\n--- SELECTED MEETING ---\n" + core_get_meeting(e["id"])
    return text


def core_wait_for_question(timeout_seconds=WAIT_DEFAULT_SECONDS):
    start_mode = live.mode
    timeout = max(5, min(int(timeout_seconds), WAIT_MAX_SECONDS)) if start_mode == "record" \
        else HISTORY_WAIT_SECONDS
    if not window_open.is_set():
        return _end_instructions("CLOSED")
    if _history_idle():
        live.released = True
        ui_queue.put(("idle", None))
        return HISTORY_IDLE_TEXT
    if live.mode == "record" and transcript.ended_at and \
            (datetime.datetime.now() - transcript.ended_at).total_seconds() > ENDED_GRACE_SECONDS:
        live.released = True
        return ("IDLE: the meeting ended and no new meeting was started. Stop calling "
                "wait_for_question. Tell the user in one short line that Sidenote is idle and "
                "that typing 'open Sidenote' starts the next meeting.")
    live.released = False
    live.waiting = True
    live.last_seen = time.time()
    try:
        deadline = time.time() + timeout
        while time.time() < deadline:
            if not window_open.is_set():
                return _end_instructions("CLOSED")
            if live.mode == "record" and start_mode != "record":
                return ("RECORDING STARTED: the user started recording a meeting in the "
                        "Sidenote window. From now on questions are about the live meeting "
                        "(see the scope rule). Call wait_for_question again now.")
            if live.mode == "record" and transcript.ended_at and (
                    datetime.datetime.now() - transcript.ended_at).total_seconds() > ENDED_GRACE_SECONDS:
                break                        # next call returns IDLE
            if _history_idle():
                break                        # next call returns IDLE
            try:
                question = question_queue.get(timeout=0.3)
            except queue.Empty:
                scan = _scan_if_ready() if live.mode == "record" else None
                if scan:
                    return scan
                continue
            if question == END_TOKEN:
                return _end_instructions("END")
            live.quiet_rounds = 0
            live.last_activity = time.time()
            if isinstance(question, dict):           # asked on the History screen
                live.answer_target = "history"
                return _history_question(question)
            live.answer_target = "live"
            if question == MISSED_TOKEN:
                recent = transcript.since(MISSED_MINUTES)
                return (
                    f"QUESTION: What did I miss? Summarize the last {MISSED_MINUTES} minutes "
                    "for someone who just looked away: at most 3 short lines covering "
                    "what was discussed, any decision, and anything asked of the user. "
                    "If nothing important happened, say so in one line. Send it with "
                    "show_suggestion, then call wait_for_question again.\n\n"
                    f"--- MEETING INFO ---\n{transcript.context_text()}\n\n"
                    f"--- TRANSCRIPT, LAST {MISSED_MINUTES} MIN ---\n"
                    f"{recent or '(nothing captured)'}"
                )
            if question.strip().lower() in ("stop", "stop sidenote", "end"):
                end_if_needed()
                return _end_instructions("STOP")
            return (
                f"QUESTION: {question}\n\n"
                "Scope: answer from the live meeting unless the question refers to the past "
                "('last time', 'before', a date, a meeting name) or the live transcript can't "
                "answer it; then use find_items / list_meetings / get_meeting (no transcript) "
                "and name the source meeting and date. If unclear, answer from the live meeting "
                "and add one line offering to check past meetings.\n\n"
                f"--- MEETING INFO (use it in your answer) ---\n{transcript.context_text()}\n\n"
                f"--- TRANSCRIPT, LAST 5 MIN ---\n{transcript.since(5) or '(nothing captured)'}"
                + context_guidance()
            )
        if live.mode != "record":
            return "NO_QUESTION: nothing asked yet. Call wait_for_question again."
        return ("NO_QUESTION: nothing typed yet. Call wait_for_question again."
                + context_guidance(full=False))
    finally:
        live.waiting = False
        live.last_seen = time.time()


def core_get_recent_transcript(minutes=5):
    text = transcript.since(minutes)
    return text or f"No transcript captured in that window. Are captions on ({LC_HINT})?"


def core_get_full_transcript():
    return ("--- MEETING INFO ---\n" + transcript.context_text() + "\n\n--- FULL TRANSCRIPT ---\n"
            + (transcript.full() or "(empty)"))


def set_user_name(name, source):
    """Save the user's name (if this source may set it) and use it everywhere."""
    if profile.set_name(name, source):
        transcript.apply_user_name()
        ui_queue.put(("info", None))
        ui_queue.put(("lists", None))


def core_update_meeting_info(title="", subject="", role="", goals="", participants="",
                             agenda="", user_name=""):
    if user_name:
        set_user_name(user_name, "claude")
    transcript.update_context(title=title, subject=subject, role=role, goals=goals,
                              participants=participants, agenda=agenda)
    ui_queue.put(("info", None))
    return "Meeting info saved.\n\n" + transcript.context_text()


def core_add_agenda_items(items):
    added = transcript.add_agenda_items(items)
    ui_queue.put(("info", None))
    ui_queue.put(("lists", "agenda" if added else None))
    return f"Added to agenda: {', '.join(added) or '(nothing)'}\n\n" + transcript.context_text()


def core_add_participants(names):
    added = transcript.add_participants(names)
    ui_queue.put(("info", None))
    return f"Added participants: {', '.join(added) or '(nobody)'}"


def core_add_action_item(task, owner="", due=""):
    added = transcript.add_action(task, owner, due)
    ui_queue.put(("lists", "actions" if added else None))
    with transcript.lock:
        item = next((a for a in transcript.context["actions"] if _same(a["text"], task)), None)
    who = owner_text(item["owner"]) if item else ""
    note = (f" Owner: {who}{'' if item.get('sure', True) else ' (unsure, the user can fix it)'}."
            if who else " Owner unknown: the window shows 'Owner: ?' for the user to pick.")
    return ("Action item saved." if added else "Already in the list (updated if needed).") + note


def core_add_questions_to_ask(questions):
    added = [q for q in parse_list(questions if "\n" in str(questions) or ";" in str(questions)
                                   else [questions]) if transcript.add_question(q)]
    ui_queue.put(("lists", "questions" if added else None))
    return f"Saved {len(added)} question(s)." if added else "Nothing new to save."


def core_mark_done(kind, number, done=True):
    k = str(kind).lower()
    key = "agenda" if k.startswith("ag") else ("actions" if k.startswith("a") else "questions")
    ok = transcript.set_done(key, int(number) - 1, bool(done))
    ui_queue.put(("lists", None))
    ui_queue.put(("info", None))
    return "Updated." if ok else f"No item number {number} in {key}."


def core_set_context_sources(jira=False, confluence=False):
    transcript.sources = {"jira": bool(jira), "confluence": bool(confluence)}
    transcript.context_dirty = True
    ui_queue.put(("lists", None))
    if not (jira or confluence):
        return ("Noted: no Jira/Confluence tools. The Context list will say that Jira and "
                "Confluence are not connected. Now call wait_for_question.")
    names = " and ".join(k.capitalize() for k, v in transcript.sources.items() if v)
    return (f"Context sources set: {names}. As soon as the meeting topic is known (title, "
            f"agenda or the first transcript lines), search {names} once for it and add up "
            f"to {PRELOAD_MAX} of the most useful hits with add_context_item (project home, "
            "product/spec page, active sprint or epic, pages for agenda features). "
            "Sidenote will also ask you when the agenda changes or ticket numbers are "
            "mentioned. Then call wait_for_question.")


def core_add_context_item(title, source="", detail="", url=""):
    result = transcript.add_context(title, source, detail, url)
    ui_queue.put(("lists", "context" if result == "added" else None))
    left = transcript.context_slots_left()
    if result == "added":
        return f"Added to Context: {title.strip()} ({left} slot(s) left)."
    if result == "updated":
        return f"Already in the Context list (updated): {title.strip()}."
    if result == "full":
        return (f"Not added: the Context list is full ({MAX_CONTEXT_ITEMS}). If the user "
                "asked for it, show it with show_suggestion instead.")
    return "Not added: a title is required."


def _by_person_complete(text):
    """Make sure every person in the meeting has a line in BY PERSON (the user
    by name, never 'You'), adding 'Attended; no update captured.' if missing."""
    out = []
    for line in (text or "").strip().splitlines():
        line = line.rstrip()
        m = re.match(r"^(\s*[-*\u2022]?\s*)(You|Me)(\s*[:\-\u2013])", line)
        if m and profile.name:
            line = m.group(1) + profile.name + line[m.end(2):]
        out.append(line)
    body = "\n".join(out).lower()
    for person in transcript.people():
        first = person.split()[0].lower()
        if not re.search(r"(^|\n)\s*[-*\u2022]?\s*" + re.escape(first), body):
            out.append(f"{person}: Attended; no update captured.")
    return "\n".join(out).strip()


def core_save_recap(recap="", summary="", by_person="", decisions="", open_questions=""):
    summary = (summary or recap or "").strip()
    by_person = _by_person_complete(by_person)
    with transcript.lock:
        c = transcript.context
        c["recap"] = summary
        c["by_person"] = by_person
        if decisions.strip():
            c["decisions"] = decisions.strip()
        if open_questions.strip():
            c["open_debates"] = open_questions.strip()
        transcript.dirty = True
    transcript.save_now()
    shown = summary + (f"\n\n{by_person}" if by_person else "")
    ui_queue.put(("recap", real_dates(shown, transcript.started)))
    return f"Recap saved in {transcript.file_path}"


# --- History (past meetings), read straight from Documents/Sidenote ---------------
def _meeting_text(e):
    return " ".join([e["title"], e["summary_line"], " ".join(e["participants"])]
                    + [a["text"] + " " + (a.get("owner") or "") for a in e["action_items"]]
                    + [x["text"] for x in e["decisions"] + e["open_questions"]]
                    + [a["text"] for a in e["agenda"]]).lower()


def _words_in(text, hay):
    return all(w in hay for w in str(text or "").lower().split())


def _open_actions(e):
    return sum(1 for a in e["action_items"] if a.get("status") != "done")


def core_list_meetings(date_from="", date_to="", text="", limit=30):
    rows = [e for e in history_index() if _in_range(e, date_from, date_to)
            and (not text or _words_in(text, _meeting_text(e)))]
    if not rows:
        return "No saved meetings match." + (" (No meetings saved yet.)" if not history_index() else "")
    out = [f"{len(rows)} meeting(s), newest first. Next: get_meeting(meeting_id) for one "
           "meeting, or find_items to search action items/decisions/questions across all."]
    for e in rows[:limit]:
        people = ", ".join(e["participants"][:4]) + (" ..." if len(e["participants"]) > 4 else "")
        extra = f" | {_open_actions(e)} open action item(s)" if _open_actions(e) else ""
        out.append(f"- {e['id']} | {_day_label(e)} {e['start']} | {e['title']}"
                   f"{' | with ' + people if people else ''}{extra}"
                   f"{' | ' + e['summary_line'] if e['summary_line'] else ''}")
    if len(rows) > limit:
        out.append(f"... {len(rows) - limit} more (narrow with date_from/date_to/text).")
    return "\n".join(out)


def _action_line(a):
    meta = ", ".join(x for x in (
        f"owner {a['owner']}" if a.get("owner") else "owner unknown",
        f"due {a['due']}" if a.get("due") else "") if x)
    closed = ""
    if a.get("status") == "done" and a.get("closed_by") == "claude":
        closed = f" (closed by Claude: “{a.get('close_evidence', '')}”)"
    return f"[{a.get('status', 'open')}] {a['text']} — {meta}{closed}"


def core_get_meeting(meeting_id, include_transcript=False):
    e = find_meeting(str(meeting_id).strip())
    if e is None:
        return f"No meeting with id {meeting_id}. Use list_meetings to find ids."
    d = load_meeting(e["path"])
    out = [f"MEETING {d['id']}: {d['title'] or 'Untitled meeting'} — {_day_label(e)}, "
           f"{d['start']}-{d['end']}" + (f" ({d['duration_min']} min)" if d["duration_min"] else "")]
    if d["imported"]:
        out.append("(Imported from an older Sidenote file: some fields may be missing.)")
    if d["participants"]:
        out.append("Participants: " + ", ".join(d["participants"]))
    if d["agenda"]:
        out.append("Agenda: " + "; ".join(f"[{'x' if a.get('covered') else ' '}] {a['text']}"
                                          for a in d["agenda"]))
    if d["summary"]:
        out.append("Summary: " + d["summary"])
    if d["by_person"]:
        out.append("By person:\n" + "\n".join(f"- {p['name'] + ': ' if p['name'] else ''}{p['text']}"
                                              for p in d["by_person"]))
    if d["decisions"]:
        out.append("Decisions:\n" + "\n".join(f"- {x['id']}: {x['text']}" for x in d["decisions"]))
    if d["open_questions"]:
        out.append("Open questions:\n" + "\n".join(f"- {x['id']} [{x.get('status', 'open')}]: "
                                                   f"{x['text']}" for x in d["open_questions"]))
    if d["action_items"]:
        out.append("Action items:\n" + "\n".join(f"- {a['id']} {_action_line(a)}"
                                                 for a in d["action_items"]))
    if d["questions_to_ask"]:
        out.append("Questions the user saved to ask:\n" + "\n".join(
            f"- {q['id']} [{'asked' if q.get('asked') else 'not asked'}]: {q['text']}"
            for q in d["questions_to_ask"]))
    n = len(d["transcript"])
    if include_transcript and n:
        rows = d["transcript"][:2000]
        out.append(f"Transcript ({n} lines):\n" + "\n".join(
            f"[{r['t']}] {r['speaker'] + ': ' if r['speaker'] else ''}{r['text']}" for r in rows)
            + ("\n... (truncated)" if n > 2000 else ""))
    else:
        out.append(f"Transcript: {n} line(s); only load it (include_transcript=true) if the user "
                   "asks for details the recap doesn't have, or use search_transcripts.")
    return "\n".join(out)


def _owner_matches(owner, wanted):
    wanted = str(wanted or "").strip()
    if not wanted:
        return True
    if wanted.lower() in SELF_WORDS and profile.name:
        wanted = profile.name
    owner = owner or ""
    return wanted.lower() in owner.lower() or (" " in owner and " " in wanted
                                                and _same_person(owner, wanted))


def core_find_items(kind="action", date_from="", date_to="", owner="", status="open", text="",
                    limit=60):
    kind = str(kind or "action").lower().rstrip("s")
    kind = {"task": "action", "action item": "action", "todo": "action",
            "open question": "question"}.get(kind, kind)
    if kind not in ("action", "decision", "question"):
        return "kind must be 'action', 'decision' or 'question'."
    status = str(status or "any").lower()
    found = []
    for e in history_index():
        if not _in_range(e, date_from, date_to):
            continue
        where = f"{e['title']}, {_day_label(e)} | meeting {e['id']}"
        if kind == "action":
            for a in e["action_items"]:
                st = a.get("status", "open")
                if (status in ("any", "all", "") or st == status) and \
                        _owner_matches(a.get("owner"), owner) and _words_in(text, a["text"].lower()):
                    found.append(f"- {_action_line(a)} | {where}, item {a['id']}")
        elif kind == "decision":
            for x in e["decisions"]:
                if _words_in(text, x["text"].lower()):
                    found.append(f"- {x['text']} | {where}, item {x['id']}")
        else:
            for x in e["open_questions"]:
                st = x.get("status", "open")
                if (status in ("any", "all", "") or st == status) and _words_in(text, x["text"].lower()):
                    found.append(f"- [{st}] {x['text']} | {where}, item {x['id']}")
            for q in e["questions_to_ask"]:
                st = "asked" if q.get("asked") else "open"
                if (status in ("any", "all", "") or st == status) and _words_in(text, q["text"].lower()):
                    found.append(f"- [{st}, saved to ask] {q['text']} | {where}, item {q['id']}")
    if not found:
        return f"No {kind} items match."
    head = f"{len(found)} {kind} item(s), newest meetings first. Always name the source meeting and date."
    return "\n".join([head] + found[:limit] + ([f"... {len(found) - limit} more."]
                                                if len(found) > limit else []))


def core_search_transcripts(text, date_from="", date_to="", max_results=20):
    words = str(text or "").lower().split()
    if not words:
        return "Give some words to search for."
    out, hits = [], 0
    for e in history_index():
        if hits >= max_results or not _in_range(e, date_from, date_to) or not e["lines"]:
            continue
        rows = load_meeting(e["path"])["transcript"]
        for i, r in enumerate(rows):
            if hits >= max_results:
                break
            if all(w in r["text"].lower() or w in r["speaker"].lower() for w in words):
                hits += 1
                ctx = rows[max(0, i - 2): i + 3]
                out.append(f"{e['title']} ({_day_label(e)}, meeting {e['id']}) at {r['t']}:\n"
                           + "\n".join(f"  {'>' if c is r else ' '} [{c['t']}] "
                                       f"{c['speaker'] + ': ' if c['speaker'] else ''}{c['text']}"
                                       for c in ctx))
    if not out:
        return "No transcript lines match."
    return f"{hits} match(es) (snippets, not whole transcripts):\n\n" + "\n\n".join(out)


ITEM_STATUSES = {"action": {"done": "done", "closed": "done", "complete": "done",
                            "completed": "done", "open": "open", "reopen": "open"},
                 "question": {"answered": "answered", "closed": "answered", "done": "answered",
                              "asked": "answered", "open": "open", "reopen": "open"}}


def core_update_item(meeting_id, kind, item_id, status, evidence="", by="claude"):
    """Change an item's status only (never its text, never deletes)."""
    kind = str(kind or "").lower().rstrip("s")
    kind = "action" if kind.startswith("action") else kind
    if kind == "decision":
        return "Decisions have no status; nothing changed."
    if kind not in ITEM_STATUSES:
        return "kind must be 'action' or 'question'."
    new = ITEM_STATUSES[kind].get(str(status or "").lower())
    if new is None:
        return f"status must be one of: {', '.join(sorted(set(ITEM_STATUSES[kind].values())))}."
    evidence = str(evidence or "").strip()
    if by == "claude" and new in ("done", "answered") and not evidence:
        return ("Not changed: when you close an item, pass the user's request as evidence. Only "
                "close items the user explicitly asked you to close.")
    meeting_id = str(meeting_id).strip()
    if meeting_id == transcript.meeting_id:
        text = transcript.update_item(kind, item_id, new, by, evidence)
        transcript.save_now()                  # History reads the file: write it now
        title = transcript.display_title() or "this meeting"
        ui_queue.put(("lists", None))
    else:
        e = find_meeting(meeting_id)
        if e is None:
            return f"No meeting with id {meeting_id}."
        with _history_lock:
            d = load_meeting(e["path"])
            text = _set_item_status(d, kind, item_id, new, by, evidence)
            if text is not None:
                d.pop("_path", None)
                _write_json(e["path"], d)
        title = e["title"]
    if text is None:
        return f"No {kind} item {item_id} in meeting {meeting_id}. Use get_meeting to see ids."
    ui_queue.put(("history_changed", meeting_id))
    who = " (closed by Claude; the user can undo it in History)" if by == "claude" and \
        new in ("done", "answered") else ""
    return f"Updated: {kind} {item_id} “{text}” in “{title}” is now {new}{who}."


def _set_item_status(d, kind, item_id, new, by, evidence):
    now = datetime.datetime.now().isoformat(timespec="seconds")
    if kind == "action":
        for a in d["action_items"]:
            if a["id"] == item_id:
                a["status"] = new
                if new == "done":
                    a.update(closed_at=now, closed_by=by,
                             close_evidence=evidence if by == "claude" else "")
                else:
                    a.update(closed_at="", closed_by="", close_evidence="")
                return a["text"]
        return None
    for q in d["open_questions"]:
        if q["id"] == item_id:
            q["status"] = new
            q["closed_by"] = by if new == "answered" else ""
            q["close_evidence"] = evidence if new == "answered" and by == "claude" else ""
            return q["text"]
    for q in d["questions_to_ask"]:
        if q["id"] == item_id:
            q["asked"] = new == "answered"
            return q["text"]
    return None


def core_debug_call_window(app="teams"):
    app = str(app or "").strip().lower()
    app = "teams" if "team" in app else "zoom" if "zoom" in app else app
    if app not in CALL_APPS:
        return "Say which app: 'teams' or 'zoom'."
    os.makedirs(SAVE_DIR, exist_ok=True)
    path = os.path.join(SAVE_DIR, f"capture_{app}_{'mac' if IS_MAC else 'windows'}.txt")
    path, count, hints = debug_dump_call_app(path, app)
    if count == 0:
        where = ("the Teams app" if app == "teams" else "Zoom in the browser (Chrome, Edge, "
                 "Safari or Firefox; the tab title must contain 'Zoom')")
        return (f"Couldn't find {where}. Open the meeting with captions on, then try again. "
                f"(Saved what was found to {path}.)")
    return (f"Saved the {app.capitalize()} window structure to {path} ({count} lines, "
            f"{hints} caption-like elements). Tell the user to send this file to the "
            "Sidenote developer. Note for the user: it contains the text visible in that "
            "window (captions and names), and stays on their computer until they send it.")


def core_debug_meet_tree():
    path = os.path.join(SAVE_DIR, "debug_meet_tree.txt")
    os.makedirs(SAVE_DIR, exist_ok=True)
    debug_dump_meet(path)
    return f"Saved the Meet window structure to {path}"


def core_debug_live_captions_tree():
    path = os.path.join(SAVE_DIR, "debug_live_captions_tree.txt")
    os.makedirs(SAVE_DIR, exist_ok=True)
    debug_dump_live_captions(path)
    return f"Saved the Live Captions window structure to {path}"


def core_get_meeting_context():
    return transcript.context_text()


def core_show_suggestion(text):
    text = text.strip()
    if live.answer_target == "history":
        ui_queue.put(("history_answer", text))
        return "Shown in the Past meetings tab."
    if live.answer_target == "dropped":
        live.answer_target = "live"
        return ("Not shown: the user started recording a meeting, so the History question was "
                "dropped. Call wait_for_question.")
    transcript.add_note("CLAUDE", text)
    ui_queue.put(("suggestion", text))
    return "Shown in the overlay."


def core_start_new_meeting(title=""):
    if window_open.is_set():
        ui_queue.put(("record", {"title": title} if title else {}))
        return ("Recording a new meeting in the Sidenote window. The previous meeting file is "
                "saved in Documents/Sidenote.")
    transcript.new_meeting(title)
    ui_queue.put(("info", None))
    ui_queue.put(("suggestion", "New meeting started."))
    return "New meeting started. The previous meeting file is saved in Documents/Sidenote."


def core_get_status():
    count, minutes = transcript.stats()
    return (f"Source: {transcript.source or 'none'}. {transcript.status}. "
            f"{transcript.source_note + '. ' if transcript.source_note else ''}"
            f"{count} lines in {minutes} min. "
            f"Sidenote: {live.label()}. File: {transcript.file_path or '(not saved yet)'}. "
            f"{auto_cc_status['text'] + '. ' if auto_cc_status['text'] else ''}"
            f"{f'{transcript.replay_skipped} replayed caption lines skipped. ' if transcript.replay_skipped else ''}"
            f"User: {profile.name or '(name not set)'}. "
            f"{f'Mic: {mic.status}' + (f' ({mic.detail})' if mic.detail else '') + '. ' if IS_MAC else ''}"
            f"Version: {SIDENOTE_VERSION}")


OPS = {
    "wait_for_question": core_wait_for_question,
    "get_recent_transcript": core_get_recent_transcript,
    "get_full_transcript": core_get_full_transcript,
    "update_meeting_info": core_update_meeting_info,
    "add_agenda_items": core_add_agenda_items,
    "add_participants": core_add_participants,
    "save_recap": core_save_recap,
    "add_action_item": core_add_action_item,
    "add_questions_to_ask": core_add_questions_to_ask,
    "mark_done": core_mark_done,
    "set_context_sources": core_set_context_sources,
    "add_context_item": core_add_context_item,
    "get_meeting_context": core_get_meeting_context,
    "debug_meet_tree": core_debug_meet_tree,
    "debug_call_window": core_debug_call_window,
    "debug_live_captions_tree": core_debug_live_captions_tree,
    "show_suggestion": core_show_suggestion,
    "list_meetings": core_list_meetings,
    "get_meeting": core_get_meeting,
    "find_items": core_find_items,
    "search_transcripts": core_search_transcripts,
    "update_item": core_update_item,
    "start_new_meeting": core_start_new_meeting,
    "get_status": core_get_status,
    "open_sidenote": core_open_sidenote,
    "close_sidenote": core_close_sidenote,
}


# --- Single instance: Claude may start several copies of this server -------
# The first copy becomes "primary": it owns the overlay and reads captions.
# Later copies are "secondary": they forward every tool call to the primary
# over a local-only connection, so only one overlay ever appears.
PEER_ADDRESS = ("127.0.0.1", 47821)
PEER_AUTHKEY = b"sidenote-local-v1"
role = {"primary": False}


# When Sidenote is updated, an older copy can still be running and owning the
# window. A newer copy asks it to save, close and exit, then takes over, so the
# latest code always runs.
try:
    CODE_STAMP = os.path.getmtime(os.path.abspath(__file__))
except OSError:
    CODE_STAMP = 0.0


def core__info():
    return {"version": SIDENOTE_VERSION, "stamp": CODE_STAMP, "window": window_open.is_set()}


def core__handover():
    """A newer Sidenote is starting: save, close the window and exit."""
    log.info("A newer Sidenote is starting: saving and handing over")
    had_window = window_open.is_set()
    try:
        transcript.save_now()
    except Exception:
        pass
    ui_queue.put(("close", None))

    def leave():
        try:
            captions_win.show_now()
        except Exception:
            pass
        os._exit(0)
    threading.Timer(1.5, leave).start()
    return {"window": had_window}


OPS["_info"] = core__info            # (registered here: they are defined after OPS)
OPS["_handover"] = core__handover


def take_over_from_older(wait=12.0):
    """If the running primary copy has older code, ask it to hand over and take
    its place. Returns (became_primary, its_window_was_open)."""
    info = call("_info", {})
    if not isinstance(info, dict) or info.get("stamp", 0) >= CODE_STAMP - 1:
        return False, False                     # same code, newer code, or a very old copy
    log.info("An older Sidenote (%s) is running: taking over", info.get("version"))
    result = call("_handover", {})
    end = time.time() + wait
    while time.time() < end:
        time.sleep(0.5)
        if try_become_primary():
            return True, isinstance(result, dict) and result.get("window", False)
    return False, False


def try_become_primary():
    try:
        listener = Listener(PEER_ADDRESS, authkey=PEER_AUTHKEY)
    except OSError:
        return False
    role["primary"] = True
    threading.Thread(target=serve_peers, args=(listener,), daemon=True).start()
    threading.Thread(target=captions_loop, daemon=True).start()
    log.info("Primary instance: overlay and captions run here")
    return True


def serve_peers(listener):
    while True:
        try:
            conn = listener.accept()
        except Exception:
            continue
        threading.Thread(target=handle_peer, args=(conn,), daemon=True).start()


def handle_peer(conn):
    try:
        op, kwargs = conn.recv()
        try:
            result = OPS[op](**kwargs)
        except Exception as e:
            result = f"Error in {op}: {e}"
        conn.send(result)
    except (EOFError, OSError):
        pass
    finally:
        conn.close()


def call(op, kwargs):
    if role["primary"]:
        return OPS[op](**kwargs)
    try:
        conn = Client(PEER_ADDRESS, authkey=PEER_AUTHKEY)
        try:
            conn.send((op, kwargs))
            return conn.recv()
        finally:
            conn.close()
    except (OSError, EOFError):
        return ("Sidenote's overlay is restarting. Wait a few seconds and try again; "
                "if it persists, restart the Claude app.")


async def run(op, **kwargs):
    return await asyncio.to_thread(call, op, kwargs)


# --- MCP tools ---------------------------------------------------------------
@mcp.tool()
async def open_sidenote(new_meeting: bool = False, title: str = "", agenda: str = "",
                        role: str = "", goals: str = "", participants: str = "",
                        user_name: str = "") -> str:
    """Show the Sidenote window. Use when the user says 'start Sidenote' or 'open
    Sidenote'. It opens on the Home screen (Record a meeting / History); pass
    new_meeting=true only if the user explicitly asked to record a meeting now.
    Optionally pass the meeting title, agenda (one item per line), the user's
    role, goals and participants (comma separated); they are used when recording
    starts.
    user_name: the user's own name, if you know it (Sidenote uses it instead of
    'You' everywhere; a name the user typed in Sidenote takes priority).
    Right after this returns, call wait_for_question and keep calling it in a
    loop until it returns STOP or CLOSED; don't stop to ask for missing meeting
    info. Sidenote shows 'Claude not connected' while no one is listening."""
    return await run("open_sidenote", new_meeting=new_meeting, title=title, agenda=agenda,
                     role=role, goals=goals, participants=participants,
                     user_name=user_name)


@mcp.tool()
async def close_sidenote() -> str:
    """Close the Sidenote window. Only when the user explicitly asks to close it;
    never on your own (the user closes it, or keeps it open between meetings)."""
    return await run("close_sidenote")


@mcp.tool()
async def wait_for_question(timeout_seconds: int = WAIT_DEFAULT_SECONDS) -> str:
    """Live mode: wait for the user to type a question or comment in the
    overlay. Returns the question with the meeting info and the last
    5 minutes of transcript, or NO_QUESTION after the timeout. Call it again
    after answering (or after NO_QUESTION) to keep Sidenote running."""
    return await run("wait_for_question", timeout_seconds=timeout_seconds)


@mcp.tool()
async def update_meeting_info(title: str = "", subject: str = "", role: str = "",
                              goals: str = "", participants: str = "",
                              agenda: str = "", user_name: str = "") -> str:
    """Save or change meeting info. Empty fields keep their value. 'agenda'
    replaces the whole agenda (one item per line); use add_agenda_items to add.
    'participants' replaces the list (comma separated). 'subject' is a short topic
    used for the file name when there is no title. The role is remembered for
    the next meetings. user_name: the user's own name, if you know it."""
    return await run("update_meeting_info", title=title, subject=subject, role=role,
                     goals=goals, participants=participants, agenda=agenda,
                     user_name=user_name)


@mcp.tool()
async def add_agenda_items(items: str) -> str:
    """Add one or more agenda items (one per line or separated by ;) without
    removing existing ones."""
    return await run("add_agenda_items", items=items)


@mcp.tool()
async def add_participants(names: str) -> str:
    """Add participant names (comma separated) without removing existing ones."""
    return await run("add_participants", names=names)


@mcp.tool()
async def add_action_item(task: str, owner: str = "", due: str = "") -> str:
    """Save an action item from the meeting (a task someone committed to).
    owner: always a person's name, found in this order: the speaker who
    committed ('I'll do X'), the person addressed ('Leon, can you...'), a name
    mentioned with the task. Use 'Team' for team-wide items. Never 'you' or
    'someone': if unsure, leave it empty and the user picks it in one click.
    due: as said ('tomorrow', 'Friday'); Sidenote turns it into a real date.
    Duplicates are ignored."""
    return await run("add_action_item", task=task, owner=owner, due=due)


@mcp.tool()
async def add_questions_to_ask(questions: str) -> str:
    """Save questions the user should ask later in the meeting (one per line).
    Duplicates are ignored."""
    return await run("add_questions_to_ask", questions=questions)


@mcp.tool()
async def mark_done(kind: str, number: int, done: bool = True) -> str:
    """Mark an item as done: kind 'agenda' (topic covered), 'action' (task done)
    or 'question' (asked).
    'number' is the item's number in the list sent with each question."""
    return await run("mark_done", kind=kind, number=number, done=done)


@mcp.tool()
async def set_context_sources(jira: bool = False, confluence: bool = False) -> str:
    """Tell Sidenote whether you (Claude) have Jira and/or Confluence tools in this
    conversation. Call once right after open_sidenote."""
    return await run("set_context_sources", jira=jira, confluence=confluence)


@mcp.tool()
async def add_context_item(title: str, source: str = "", detail: str = "",
                           url: str = "") -> str:
    """Add a Jira ticket/epic or Confluence page relevant to the meeting to the
    Context list. title: e.g. 'ESP-142 API schema v2'; source: 'Jira' or
    'Confluence'; detail: one line (status, owner, due date, key decision);
    url: link to open it."""
    return await run("add_context_item", title=title, source=source, detail=detail, url=url)


@mcp.tool()
async def save_recap(summary: str = "", by_person: str = "", decisions: str = "",
                     open_questions: str = "", recap: str = "") -> str:
    """Save the meeting recap into the meeting file, in parts. Sidenote writes the
    Action items, the To-ask questions and the Context list itself: never repeat
    them here.
    summary: at most 3 lines.
    by_person: one line per person, 'Name: what they reported, what they own,
    what they asked or are blocked on' (1-3 sentences), including the user by
    name. Everyone gets a line, even 'Name: Attended; no update captured.'
    decisions: one per line, '- ...'.
    open_questions: unresolved questions and open debates, one per line. A debate:
    '- Topic: Name1 wants X; Name2 wants Y (no conclusion)'.
    Use real names, never 'You'/'you' for a person. recap: old single-text form."""
    return await run("save_recap", summary=summary, by_person=by_person,
                     decisions=decisions, open_questions=open_questions, recap=recap)


@mcp.tool()
async def debug_meet_tree() -> str:
    """Troubleshooting: save the structure of the Google Meet window to a file in
    Documents/Sidenote, to fix reading Meet captions."""
    return await run("debug_meet_tree")


@mcp.tool()
async def debug_call_window(app: str = "teams") -> str:
    """Troubleshooting / development: save the structure of the Microsoft Teams
    app window (app='teams') or a Zoom meeting open in the browser (app='zoom')
    to a file in Documents/Sidenote, so Sidenote can learn to read their
    captions with speaker names. Use when the user asks to capture the Teams or
    Zoom window. Best done during a call with captions turned on."""
    return await run("debug_call_window", app=app)


@mcp.tool()
async def debug_live_captions_tree() -> str:
    """Troubleshooting: save the structure of the Live Captions window and its
    settings menu to a file in Documents/Sidenote."""
    return await run("debug_live_captions_tree")


@mcp.tool()
async def get_meeting_context() -> str:
    """Return the meeting title, agenda, participants, role and goals."""
    return await run("get_meeting_context")


@mcp.tool()
async def get_recent_transcript(minutes: float = 5) -> str:
    """Return the live meeting transcript from the last N minutes (default 5)."""
    return await run("get_recent_transcript", minutes=minutes)


@mcp.tool()
async def get_full_transcript() -> str:
    """Return the meeting info and the whole transcript, including the user's
    questions and Claude's answers, for recaps and summaries."""
    return await run("get_full_transcript")


@mcp.tool()
async def show_suggestion(text: str) -> str:
    """Display a short suggestion or answer in the user's floating overlay."""
    return await run("show_suggestion", text=text)


@mcp.tool()
async def start_new_meeting(title: str = "") -> str:
    """Save the current meeting file and start a new, empty meeting."""
    return await run("start_new_meeting", title=title)


@mcp.tool()
async def list_meetings(date_from: str = "", date_to: str = "", text: str = "") -> str:
    """Past meetings saved by Sidenote (works even when the Sidenote window is
    closed): id, date, title, participants, open action items, one-line summary.
    Cheap: call this first. date_from/date_to: YYYY-MM-DD (inclusive). text: words
    to match in titles, summaries, participants and items."""
    return await run("list_meetings", date_from=date_from, date_to=date_to, text=text)


@mcp.tool()
async def get_meeting(meeting_id: str, include_transcript: bool = False) -> str:
    """One saved meeting: recap, by person, decisions, open questions, action items
    (with item ids). The transcript is only included with include_transcript=true:
    use that only when the user asks for detail the recap doesn't have."""
    return await run("get_meeting", meeting_id=meeting_id, include_transcript=include_transcript)


@mcp.tool()
async def find_items(kind: str = "action", date_from: str = "", date_to: str = "",
                     owner: str = "", status: str = "open", text: str = "") -> str:
    """Search structured items across all saved meetings. kind: 'action' (action
    items), 'decision' or 'question' (open questions and questions the user saved
    to ask). status: 'open', 'done' (actions), 'answered' (questions) or 'any'.
    owner: a name ('me' = the user). Each result names its meeting, date and ids.
    Use this for 'my open action items', 'what did we decide about X'."""
    return await run("find_items", kind=kind, date_from=date_from, date_to=date_to,
                     owner=owner, status=status, text=text)


@mcp.tool()
async def search_transcripts(text: str, date_from: str = "", date_to: str = "") -> str:
    """Search the words people said in saved meetings. Returns short snippets (a few
    lines of context) with meeting, date and time, never whole transcripts. Use it
    when the recap and items don't answer the question."""
    return await run("search_transcripts", text=text, date_from=date_from, date_to=date_to)


@mcp.tool()
async def update_item(meeting_id: str, kind: str, item_id: str, status: str,
                      evidence: str = "") -> str:
    """Change the status of a saved item; never its text, never deletes. kind:
    'action' (status 'done' or 'open') or 'question' ('answered' or 'open').
    Only when the user explicitly asks; if more than one item could match, ask
    which one first. evidence: the user's request, word for word (required to
    close an item). The user can undo it in the History screen."""
    return await run("update_item", meeting_id=meeting_id, kind=kind, item_id=item_id,
                     status=status, evidence=evidence, by="claude")


@mcp.tool()
async def get_status() -> str:
    """Check whether Live Captions is connected, and where the meeting file is saved."""
    return await run("get_status")


# ---------------------------------------------------------------------------
# Overlay (tkinter must run on the main thread)
# ---------------------------------------------------------------------------
# Palette
BG = "#18181c"          # window background
SURFACE = "#232329"     # cards, input
SURFACE_HI = "#2d2d35"  # hover
LINE = "#2f2f37"        # dividers
FG = "#ececf1"          # main text
MUTED = "#8b8b96"       # secondary text
FAINT = "#5d5d68"       # tertiary text
ACCENT = "#d97757"      # Sidenote orange
ACCENT_HI = "#e58a6c"
OK = "#6cc28a"          # green status dot
WARN = "#e0a458"        # amber status
END_RED = "#8e2b2b"     # End meeting (dark red)
END_RED_HI = "#a83434"
FIELD = SURFACE
FONT = "Helvetica Neue" if IS_MAC else "Segoe UI"
MAC_UI_SCALE = 1.45      # text size multiplier on macOS


ICON_256 = "iVBORw0KGgoAAAANSUhEUgAAAQAAAAEACAYAAABccqhmAABnG0lEQVR42u29eZxk11Um+J1734uI3GpVlVRSaS0tlmRbNhhvYFcJsOUdQ3fWGDDgNmCGrceGZuxmmaz8dcP8munGmAGDrcFjm54BKtma7vEmgarc2EDbkmXJVdZe2kpVqj0rl1jeu/fMH2+7b4t4EfEiMjIrnn6hzMqMjOXFO9t3vvMdYHyMj/ExPsbH+Bgf42N8jI/xMT7Gx/gYH+NjfIyP8TE+xsf4GB/jY3yMj/ExPsbH+BgfG+WgS+0NM0CYmyPcfpQOHbmN9u3zf3EIwO23M44c4fFlsYGP4HM3PvZ9tx9lHLmNMT/PBPDYAWwwYz8EiH37AByCpvl5PbaC8ZF3zM3NiQOAOARgH6A3ulPYcA6AmQkLCwJHjhDNz7up33/sY9X69otXAHq30nQ1WF+lQTuY+XKtdU0K7FTM8VOjE24l49u08+FMjxT/Nt8X6fa/bvvY2b/j9I90+wfh7FfV8bS0fxAO/7hfq2Jw2+fViVcpSUBpPiuFWAHzWYBPg8XzRPq5CYnnlhx98ppf/mg99VAHD0oAwOysJiIeO4BRNXosgPYvqOiDm5VN9co9Tqv1SiK8GsAdrtI3guiKqmVVq7YEkQgeBAyG0rrYBdzmomcuYvxF7JUzHjvngTnv5XLOa+xsvZzlQPJsLvF6ud27a/sYxX7eyfg55w8FEYiiS1+zRstRaDquA6KTAvwkgx4UUjwATV/f9cGJR4mirJHn5sQhQOw7cEBtBGdA69vw5wQWbifavz80+qXPzu0UQn6P1vxmrfUbieim6ZptEQm4SsFxFRyl4WrN5IUHL1j7nyWzcU66ukpNo+J2Ntrhws432vg1z51tpc3jZL9AynI5hnEnfp/xfrn9B1bgPPToYNudZ/OCJ++vg4cg7/5CgIQtJWxLwJISWjOWG01FwGMM/mcL+KKkicM7f+m3TpgBZgHAfiPojB3AMOr6gweFmY7xwbltdYfeqhV+SGu+c6pW2SqEQLPloOk40MyKgyuYQAARxa5mBvcYiSIbKRL1uXMG363xc7/G3+FXzB3tNPbuON/4uUOawUU+/Q6fTScnyzmPwwwmYmZNzMQMZiIiWbMtVC0JzYzVlrNIRF9lpgVLOp+74oO/96LpDLB/Qa83vIDWm+Gb0X7xs3Ovl0L8ODS/e6pauZyZsdp04CilPPNmASbKfJ+cY5ZcqJpvW1+3NX4u/hDZ1yoXCOhc4DkK1CQdjb9o5Ed3xt9Lys+diyvu4ERiGRxFj0wMzUwkJcmJig1BhJVm66wAfU4I/vSuX/rdv4/hBfv3rxtHsC4cAB88KAPD/9bcXOWGm+gHmflnBYm9tYqNlXoLjquU/44Egant5cA5hp1n/D1kBF1F/jZOhDuEOS4C9hVKbzpFzQ7Gz73W+1wAE8mM2O3rfS7uibjIaaEgiWENAJYQcrpqo+UquFr/swJ/Ui7V/+yq+U+uBhkBrYPSYKQdAM/NCRw4wETE35qbq+zZwz/KJH5pomK91NWM5XqTASgwJBFRoYhU0Pi5U0E5VOPvLeXv1/j7TfmL1PuFjZ8zfU/qHGdnCsWzL0p8l+WAySv5GIBmQExVK2QJQr3lPknMv3+Rl/741g9/aokA/PnsrNy/MLqOgEYT3AMdOjAn7/TbeKt/Mrcf4N+YqFRe2nJdrDYdBSYQQfaCMBe66NqCUJ3T/k5PWC7Yh65Tfu7cGuhs/Oi13k8Yf4eUPPWyOHoEznOOXNDF+CeKKPszoNBEcq4JAhisocFVW8rJio2VRutJCPzm3b/ye5+ZBzQfnJWYPTiSLUQavXQ/Sp0WP/Mbr7NJ/OaEbd3ZUsozfAIRgt5dn+lmDyl/Eaiq53q/XXuuxMjfL9iHrjCLHuv9PH/EGYYf3DcrMwg5HUVKBOPnlBH5sxpE/sP7+YJmQFcty6rZFupN55+V1r9+7b/9/XtHtSygUQT5HvvYL27avWXbAQY+OGFLulhvKiYmghB54YC5M0hXvP9eAtLP3YOGXYF9her9opEfJYB9nRH6lPnnGH/SmE0jZ3C6BMl8fC6CbWbZeeI3nGEklHnCA36BZtbM4OmqLZkZrlafWnJbv37br3/yhJcNLGii0QAJaWRqfZ9yeeFTv3pX1bI/VqvZtywurTIDmohku4Kyk/EXMvx1ZfxcUsqPrqJ+78ZfpNvi9fe5TQeAUxwAjp1ybsMTCB1LKmqHebzJFYiMgxOmQonSIWFCzAjLCc1aEwFbJmqi3nJOOIp/6fpf+4M/A4CDI4INrLkDuG9uzrpzft69b26v9V3XvfG3KxX5Ia01VluOK4isntLNEsG+Tu0lLpz2c59g4tql/GWAfZ3er+7Q+tNJw09gBGygAuDspzQ/S8q6jnzLpcR9KM4kit3HLA1imQWZr5PdipRWxbLQcNxPnV50fulV/+GTi8G1f8k6AJ6bs2h+3n3x7o/cOF2pfHqyVvnuC8sr2j+pAr20l1Bib7lQ1C/QPmNGr/D7YCJ/ScaPzvV+kTtns6+zoj7HDT60dQ5/mFUgcheOiBIgAHkESZCZERClDYiRyAZ8YNF/TZqZCaS3TdXkSqt1dKXVet9L5u7+WmADl5QDMOv9c3f/6jsnqvLTFcvatrha96M+JYyTsiHeTjZk/pn5J5RIBzOehrMKxcyUn/pH+Sm6L8UiUuL1Jfir3A646tn4u+nvU/b5MbOCjM+AjM8gOs9kwn/eME/sBfjVv46fX058n3zfnFOCUMR+jn/MQXkQmweLnAEF7zrWNiCjHPC/Gq+DDMiAWbtTFdvSWtfrrvqfb/rfPvFZnp2VWFgbFqFck8EdgOgXfkEv/vGvf2iyKj+tNE+sNFpKCLK4I1+9PypoGUh/cWZfb+Qe9AT2FU/5h07u4c58fvOcso5PS7KB8gd/p2FkBxxzHeHb1UY1wBmfgQ4fl1PkIs+GKTwP1AYLiRgonFkWmY6QANFylWKgMlOr/ODPvuGV1rY/+OzfHfDsQhw+fJg3bAbAzIQDB4jm5/XFT/3a78xM1j60uLyq2fOaomfjx4DrfS7J+NEtGFe8Lz+clL8Hck/OOWKdb/zIMP7AUNkw/Fjkj/X+E4+ZyNY4K+XnVMBPYQBkIP0mkEggEMVmytKhP4EbaGYWgtSWWs1arDf/5LP6ivfNz89rnpsTw9SsoLUx/l/9f2emJn74wtKK67H4/PPWR8RBwd4yup2R4ZxLvyxyz8CZfWWBfUWGIzuRezgy5izjT7b52Kz3E8afiNocug2OEYXiITj7M8ii58SMHoGxUwgBkAH/EUVpf9KiIoIqpytJ7/26WycmrOVm80tnFf/gq+Y/uTpMJ0BDN/4//tU/nZmqvefC8qpDgF1GutlXyl84KvcR9YdA7llb4y8OuMaNP64xwO2ivkkAMh2D8dg69/VQ1ElgDZIy7jkoDlUQ50X+yKjjjiHeUozBA8yeE0DCP8QgLe1sm5qwL9abh85pvH2YTkAOR6xjv6Bf+LhevPsjf7rJMP6OVNA+JvD6qvcHlvKXMcyDrode+qr3MRjjRwrsyzZ+nTB+1pHxs9HfZwOUZG/iO4rfgqCVi8qW7Zi44ho0zp4ASTuW93OHk8Gc7OpwvPvA8e4FcUZ6EpQaiRNGgFxtOc6mWnWPVOq73/+dt/3FFb/1e84wMAEaFtp//u6P/OmW6YkCxt8juacH3IDXYox3iP39IrgBcz/KPVx8JiGJzgcwX47xczLy+yQh0/CjNqHfQaBEQy94QiHgri7hsu98A7bc/io8/un/BHt6E6A0svjElNHiMzOBsBNgRPsgKzDLhjgEEG8SUubMAztbJ2v2Yr319zfSlW8CAByY50GyBi0MluUj6c797rlPfPijnvGvOASyudf+fknGz2ifQRQn92DN6v1ShnnKmuTjzpTbbOOPw3Xa/x+H/+ZYhDcZfYGpcgTTx6g54CDzJxARmBlT196ETTfcBmtyGqw1wkZ9ivGXPkeUGHQKHAGz7wSY/fah18Im8h0TZVAE82jJRPb51YazdbL2vY+vPv//3Pzv/viH78Nei3FYDapFKAZK8rlz3j3zh7/yoa0zEx9cXFpxiGFzlN8lbjrU5Uv9LvwbHf99xmPFU8LELWgjJX+pEfaVmBPok857KWyGq9iNYw/M5gNHqWP4c516v4zk+4o/Dmc9r9bR85s3nfh3dCqRdapjvfXcqF8E7DPeT+x773Vq1rH3w4oBFb1OrTWYNVhF70GzUQKELUEdtQlBYb0f6sAQwKwha5OYvvpGyIlJTFx5LZTrgKWnF8PwFCRYeH+uiWKlh1GAhM+ldXAJGK9JwX9/xuVhXlvGNRN8NsnPkQD7wsqqs22i+p5Hfu39//HO+cMu5ubkusIA+OBBSb/wC+rUJ3757Ztq1c+sNpquYlghjNp1ujlqyj1d9ve71gQsm9ZbtL/fKYPonl2Z4PLE3QcnIzrHI7/OcOBGSh1Sp8io+YnAJLx/CwESBHZd1HZciV373gESEq0LZ3DxqW/DqtSiYUFDKJSZYmNAIcEoyTbk5Lnj1HUSBxA5RTij7M9S1h3X2TxZ/Z5/9dpbn9v573/v/vvm9lqfOfyMHvkMgOfmvJr/Dz983bRV+c+OUuwyC8o0fo5aQx1S/nVr/HmGmdG8iE/BpUmsmdJfJTL7MAjZLjZluuPeMGb8PuBXxPjZ7OwRxW4shFePC/K/SrBysemGWyAsGwAwc8OtEFbF8xfB/Uj4SpHCcCY5SZJ501FbMkoM423NGBsx72JPZF+a2VputNR0pfqH3/pff/zVd84fdg/OzsqRxgCYQVi4nfi+OWvx8dU/q9jWlsV6Uwki2esY7zDIPYWiMooY/zrk83ORUWnuIXOJ+yAdQXeRD9BRj1+H5J4M4084gSikEmJNOAqM2aDvkoCQFjbtuT18XVNXXY/qtu1wlxejlqBRHpLJOiTydxhwIAsWENVB/vfk3438lh+x58gE+RgF6RjnmJOtQc5ipRM5riabRKVqW39+bO4nXnkdrrvo/ymPZgZwYE7S/v3q/KNLv715auI1i6sNV8A3frNeN1on8TnORC2a+XPkED26N36OVbTJTISNqMapaBsv7ZMgARJ4ANI1u1kfJ/4mGSVTfaRkupmBM3Sj1JuTmMWjUgbsYpJyONkO82vjPMyCWRvGb/yMOQMd4qgep+zI76X7XspP/vdCSgAalc1bMXXNHt/paMhqDTNX3wgoF1JaICF85yHCW/jvsKygeJsx2akIborD+l+H79XABJKnmDlT4ASeAxF1x3FnatZ1DQefoPl5fejAXjmSJQAfnJU0P++e//gvf+9MrfahxZVVV4CsVH7PqWs496LLNH4TZMoRjog445w7GpZM+ZkzXAJneKkE0JY2/ERUTV4hWXbMiTfKiDuPnBPHbQGGzvV+5xYfx9t4iaeLgYqms2LPCMLzZKxfQCIt1iFwq1OEnwD4Cx/b7O2Hhu+n+9L7KkLjFxCWBWiFqd3Xw5qciZ3/mRtu8QxcSpCQEEJ6fxc8nvAcAZMIOwkInABHOIT2NxBpc/bAaF0GvzM/zfi1lVHoGZGPCNaF1Ya7ZaK6/1sffu/77pw/7PLB8koBURbZZ2EB4N+fmxYW3e1ozVqzyK732yD9PhyfQvrT8SAXgYeOkObkz03jDaFbnRWdoguXk/8lDT8H7ONUcd+u3s9I+7PyX2O6JbtJkHiPmZ0K7Z+jnPMHLvAZ+EbNOZVxxvnTiHcjPETfQPrDz44zs4qY4ftfw4gtJAQJCN+Qw5uUIBBmbrg1lXpPX3sLrKlpEAAhpX8LHILnRALngiBDCHCBQPCDzLqejWhuvG//OmP/ugyRf61T7zXdtdHeeWKI5XpTV6X10Ud/9cevwuxBzXNzYnQygIUFsX9hQZ0RF//9psmJG+rNlorr9hWv97lDvT8UZh96xw24nVBdbr0fz0Sywb4855JD7llTHYVECRUjAyWiv/EznYf4UwLpF57xx9N+GUv9SUoQEayJSUxfe3M0m+M7gOq2nZjYsQvEGtI3fiEFhBBhFhE+nqBwACDMBCjeiWBT1cjXONAZBKh4WcVtNA1j17poKebJirVFKf59ImLcfpRGwgF4Qof71YU/+uCrJiv2Ly4urap43e9HHJ0fseHXfnl1chhxwLlRh5nbGj8XRvpzSASJ/nNenz2rL58flXUOfyCbJ5AflbXBgciLyjk8i0R2wObnkpUdac7mEOjgHAWfdTbVwbscOIhsoeHnG3+iTRfW+AQR3nzDlQLCkiApIC0JYo2Jyy5H9bJdPrImQhwARJi+5iYQawjLdwAkfeOXkSPwgUVBURkQkxEzuxn++dNGFhpE8ihDUOnPKIPLkrxGBUEuNlpqplp595GP/NjbaP+CKqMUEGVRfl1NH61KKTRzXDWxXYuvk2afKc6RhQVknT+kryROIliZ2XubB2KOg21Z3NYECYbbRn7O1qrhjDohXRamSwPk+EXEAdVM3KUwuScvg2Pjc8x4ckOlQ5ulhQ6iv074GI611SJybhL0oxjg50XqoI73v9cKU9fcCBLCM/rEMX3dLZCWFRm79G5BJkCJbCAoBcwyJOL/ssFMRIZyEcc/B5jkoGzqdBwYBqCZHKWYGL/zrbnZCo7cxtwnnV/0v7FnQV34o1/+wW2TE9+zWG+qUMCzELmHs7Nh0zlwjqqD2arhvIgWB6ZiaHsKhc9C2xNDHjGQDgmGWDICJ/hjeRZqZg4Zrz/fb8THZjMBUQOFztfJKpby52cW8U5KrMOQPBcJ4/YyDqTZi4hovEgM+BCZffvISIWMvpdChiDglJ/+mwcJ7zFrV1wDe9MWEHOIAcRuCeMPgMGgS2CyfLIymOgaSs4yJLIo5HRLUipYLOotR22pVW6h1crP0vy8PjTXX1egH+9BPDdHuPJKed595FsTVfumesth8p0K9yneMdxJPpRD7illLRePlnJPD2u4jeEWaLM21hwT89AxlNzg90cFexR1E9HYTNXNWt0j/wjPqKsTuPpHPgg5MYXUsL7f4z/xt5/GyrGjoEoNWikPmNTaoyL7X7XS0FqBlfdv+L9jrUIwz6DyhsNCgs0BIoQcBYI3M0AZ00GEDhuRGdqSghTzWVVr3nL7gYXz/unioWYAPDcnaX5eX9SP/PDWqYmbV5uOLsv4O4F9PFTj54KTfFz6/H47sI/bgX05Apm9RP6ujV9nYC6JvDdW3XBeWCKfz49E5Ccj8lPCIQTZgAS0wsQVuz3j5wylDv+JJ6+9yTNWEQcA40AgQVCQAVAs+sd3z8bxgXRRZER+5Gw3ypRKj+lTCkcptblauUys2L9IBO6HG0A9R39mYOGAff704sMTFfumutNiYkPWq2v9+fLIPYV4bWul3MODn+TrSrkH3dT7GSSsFF7jXVXBpB+HJX8y+vs/Yzay4WiQhyFigJ9nfEGaLiO0PzBciu4npIRurGL7G96FTXe83gNkRbIrrQESaJ05gRf+4g8BIcKoz9pr32nlZwFKeTetwUr52YAKf28CupTKBLwxYBGTD/N/Z8wLE1HumHDWR2wJAaX1ea1aN93+0YXzPk2Ch5IB8NycJCK+cGrxXVsmazevtlq6f+PP1nTvmdyTT7fOPbPczvgzwXfOpzPkkNi5YORP/ynHhCyzOvPcDbkHuS38rAHFxH24AFPY3PDDGdBExuvloAQwW27BLH2Q4gvAiMaCIuMPIjgAyGoNtd03xLX54kAAAMDethOVrZcBWhkZgI/8myVFEP2DliBMQNAcJDJPLcX1ChPZV367tr0DJoBcpdSmCXubsOyfIPSeBfQ6C6ABQDF/yFWawZQQY+hxkm+NlHuYc2S7ylTuydv3U5Zyz6CGefJS/gxZdZ11Qjmx4EMHoKROvHfykXRERutr7VGwDVJQ2P4LywGB6Gd+BgDlorJtJ+ytO/MdgJ8FkJCo7boOrTMnICwbitl7HKaM0sM3fDCY2Hci7GcucZ4vxbpCFCoHk+8YieKwBJskf+6cwTJYNByXldb/+rFffMvHb5r/Qit7CWLJGYBP+dUX/uBff9dExXr9UrPJBJamTFK6ncP5KH9HpJ9jtMl0m4/TM/5tjD+LGNed8XdD7onPkqfCLCd+n8HIS2kA5DxOFlsxyUzri9mXJ46QsZPPbHcF14KX8utUr9vUaUg16phiNNxgYo/g9eVFiMpHXQEhLYA1qruu85wBd56gre3e4xGHpOW1DyFiXQYi8zUYN5OklDbQmGS5+UnAFDVFQnGgTbfF7KwQIBqOqzdXK9e5lW1vJ4Dv66Ej0EMGMAtgAZrppyZsC3XH0Uhu8clc1ZqOLhzTTOPsejJ753NRWA3M2bvisup9Llu2i0dsLVcnhLlovZ+ZWUQTcsmH0xwvUXRK1osQV82k6L/A8CCibMA0eL/lRyBAa+hGHXBbqO3eUwDJ8lmBl18NYVehVpZA0o5wBFA44WdOGgavgSlcCgYd1/6PWvcAhP97YZQ53u80RJg9xK8JyvwM0nRQ1sxaqw8A+Kt92KeBw4MDAZmZiIjPfeIDm9mZeNKSYrvjKiZztrFguglweSl/xnPoHB5+9q64bKPlLAdGGXacw6AZtPH3C7gW3qzcJrHMKgtMhxKAfWZbMJYVBFRa8lV8/Jn8sP8uZYjsCyk94o60fKNnr3YHICpVVDZvR/WKa1G7eg8mrn0JyJ//L3I0jj+F+jOPovHC02idOwXVWPHKFSHA8ABC5brQroJWrgcKugE46LUPQ/an1p7jMFqCwU0k2oHClysLJcSTW4raX+tMRBCAKwXfevN//PMnu1UT7i4DOHBAAlBQtbdvnqxuP7/S8Gb9u6z3B7mJ12RfJeN7yu9wuuuQ2ZThvOwEa6TcU2w7UpZfokQXJL3QMuMPufPuQzbW7XIy+zL6/nEZ8ByxE4rUvYQv6hFw+9l1oJ0mYFmwpzejdvluTF59I2pXXo/KZbu6MvpYGXDVDahddQPADOfCGTReeAorzz6O+gvPonXhLFSr6b9Hj39AzN6cP0WCn5zah8ZxqfGM1QGsOYUDdLGPgrRmd/NExV6st/4nAL8FHBImHFOuAzh61IupCrOsmSk2RF8OuaeYNEVGqs7ZYF/y/jpTlz5HJTdrw2wJLb61JPdwmyYgc4F9C5R4pWxs9TPLrVBWi2MVv8n/TxIbAwKQl+r747hKQTstzxlMTqF62S5MXXMjJq+5CRNXXgdrejMyiQgkulaz8d6MgL11B+ytOzBz+2ugmw00Xnwey08/ipVnHsPqyefRungBSimfpCQhJPnqQKmJk8SK8Ww/Tj0uo/F9DTVcBcX8QwD+dxw4rDA/gBIgACkv3P2hbaqujkkpNrlKcyCc1K9yT9nGzxnTcdyulkrijxljedxhycco1PuFeRZdkHs6yycn1G5S230jlV/NcZBMBxRfIcEkvJ8p10vtLRvVrdsxddV1mLnhNkxffwtqO68CCZlu4WSAcT0fbR6zdf4Mlp99HBefegRLTz2K+ukTcBt1zxItC8J/D9AKpHU8/af4bFMAJJqZFxEV2mTMiRRWEHFD46Xf+bE//3Y3ZUDxDGDhoAD2K7eh9m6aqGy6uNpURJCFteH7lu3i7OuPk9ti05E03m82oqi5VNKs/TP63NH4JmUS73mdrOXqqlHJ+Wu7kyu1Q1FezSlxbc+eKDbgo43kUSsXurkCBsOa3oTJXVdj5obbsPmml2L6mhthTc0kgryOZL/KNPxYC5JSXQ0SApWtl2Hb1suw7Y7XQTstrL7wDBaf/DYWH30Yy88+gebiObDrwLKrEJadirCBzFinqE/FV84TGO7MRMXSjcZdAL7dTRlQ3AEcOUJe35DvsgV8yhOKGX8f9T4KRv3kTjlTQz6GpMZAPgpnuZnMNgululFp46GCODshF4akPDzB309tvm7qYPiE3JySMwDM7FNLBYDb+D7tYCG2NgQ9wpdjCmQivtgjeNHMDHt6CzZ/x8ux6eaXYvram1DdvjMV5dlE48XA1Oyzk2QyePtGC0/YFUxfexOmr70JV33vu9BaPI+VF57GxceP4MLRB1F/4dkEaMzZKXdsSxl39sec8sCktAYz3QXgd9FFN8Aq7BPn510+OCvPncDe1ZZLYBbc9oIpspOvR7AvE8jj1CAKcwYzzUddteNAuS1/TNQf42QdXzTJWVG8U9pfLrmnFGp1x72IXODxOVfKmtnbviMsy1PeFeTrBnjbenQCYGVtYgkMkhLWps2obNsBe9PWuPG3a1OuxUGJetDIPuyZzaht3YHmlssgqzVjIzGHdKG8x+RkA7Co8fvygXXHhYZ+zUM/+yNbaX7+PJtby/t1ADw3RzQ/z4undl8PODc3Wm6cXtVtvd+H8XPKEehU1E+O8TKzV19qBdVYBYSA3Ho5pnZdA3vbFbA3bwNZdlyhpds6pr9WfHGkP7lVrqtaPeMe1M2mVJO+5n9VCq0LZ1A/9QLqLzyLxqnjYNeBrE2ChAVmFd/uy3HQjwlonD+D5z7/53jui3+B6rbLMH31Hmy+6WXYdOPtmNx1ddtsYChH+JweuEiGDkDz7CksPf0YLjz6EBafOIrGiy9ANeuw7AqkXYn/bVFbKFh6mS7EUUpPVaytdV59OYDDmJ0VWFhQZWUAAoButZrfsWW6JhZXg7l/jq1eNkkhedxgToxjpiM7x9cpGb0TToqIhDU/GVrsgTCDiT0T3JVliOoEpl/xRky/7DWo7d4DMbEJ46O8QzeWsfLskzj3wD/g3IP/CGfpIuTklD//ziFtlv3LI3AEJASs6U0gENzVFZz/9gM4f/QBWBNTmLz8KsxcexM23Xg7pq7ZA3tma6xfHjH9ynQI8bofIQ0YUM06Vl94BktPPYLFx49g5fgxtC4uQivlMQmrNS/6B9wA5sT24KQMOMc2lKU6LpzhyCkDB2PoihBilcWrARzGbaeo9DaglPRaKbxZwGwgi9u2kTi3aZ/j6ThLuTcO9rGJ+usAbdbRMIZWUI06pm99FbZ97w+hcsV13mOoFuCsYpSyy/V7+MZiWZi5+WWYufkO7LzzXTj++T/H2a99GcK2QdL2ZulN3IYiH0/s+ks9JKha8aI+AfUXj6Px4vM4+8CXUd28FZO7rsPM9bd4vf/Ld6f7/sHOv26dQRL5N+r+1rkXsfLME1g+9giWn38KjTMvwm02ffhdersG/YlBaF/yyycDtcvNKK8FlVSU7rjEyXMymhkE8RoAwO07uUwHoP1z9ArXZW95Gg13mEdzusWXrPfjOusC2nEAIux45/uw+dVv9t5Ga9XvwfhTZTQ23zJbZ7pZB7NG7bLLceP7/g02v/RVePpP/whuswGqVD0RjQBzISPKEYUlHfmrMEkKkG1DWBakkFDNJpaeOoqVY0dhVSdQ3b4Dk1fdgMlrbkJt17WwNm1Lj/32gPyrxiqaJ5/1+v7PP4nGqRNwVpagtY/gV6qQ0oZ2XWjXBStljAV3Hu325oza1/uE9lOrGcFXOK4CWN86NzcnaP+8KjIcVOTy9wDdT3zAPlu3H6tKeV3DdXWk+tt5LdcgjD8+Vpo0fkA5LiAkrvyRD2LihpfFDX98DMD+Of49M7RWkBMzWHrmMTzyh7+J1tIFyEo1Al5D+qs3ZsswhT6kr88XUIEtCNsKqcBSEEhrgL0xXmtyGtUdV6K2ew8mdt+I6uVXd+UMnHOnUH/2cdSffwKNU8fhXDwP5Tj+nkEBzYBSnsFHlGAVGj+bdGD/gg3owCJJA/bTfm/CIbYdOCoLOspDcFojgIgc1qtNbe15zccXThYBAkURABAAzjvWlaxxVUvpcCs6dzB+HuAYb9r4tSfiwIB2FUACV/7ohzBxw8vAzRWftTU2/oGB48lUyif3uCuLmLpmD17yc78BMTENt9mCZgpVgQOFYK3NnQwIpxMj1WVfrEMpsHKhlQaEhKhOQFQnoJWL+gvHcOGf7sGJv/g4GsefSmAE+eak6is4+Td348yhv8bKU0ehVpdBVhWiNhmCw1q5hrHHpzZNdWizU0JGvU+dmGcFwD5ugxISQI7WXJVysibd6wBgYXZW9D8O7OuPc0vtnqgIW2vFAFNMpptz5KPbLOiI5JI7LOhQ0X3YXLLgfxDeyVehJDMYcBt17Hj7j2Hi+peCmyve/rfxsTaOQVpQK0uYvmYPbvzRn4dy3TBaepp7wefJYe3sGTqHETVcIuJr8rEKIq4KIzJrBkkbojYFMFB/9rHOHRi/P9k8+SzclYuQUzOgSsXjNWgX7Bt9pBQUKAD5C02CVWaclKzXGSvhdUx92hwC1uGOBB2O+ybHu7VhMzFJeh3boKQqgqAUXw8AOwoAgZ0dwJHbyBP/oKurlgQRq1KVe7jdplzOHe+N8EAdivMAAs7KEmbueD02fced4Nbq2PhHIBsgacFZWsT2V74Ou77vnWgtL4FJ+IbNxkZgHbvIdfC74Cv7GQB7jkPFggD7E3oOWAjUjz/lXSwFyoD6809Gsl9uFOV1IA7K2gg42oj2bNT+3GYXPMc7ABSMD6GQNFs7ibqk+QgiSOarUbYgiJS4SgiEggb5whE6Z+1XcrlFAfGODEJLUms9GMJgBpTrgKY24bLvnwW0m05Lx8dwDd9on5GUUPUVXP3mH0L18qvgNBq+TIkRTYPvfU2+wPCg43W29qN/+L0xkqu1CwiB1pmTcC6cbq+v5QuG1J97wqvzXdfLMpQyshTlZxzJ742MwHdc5JOfSKe3qJJ/yzQLzanfxReqJARvMnfkGNk1UL4DYMbOdhpmxcE+oHC9n+iNajbpvIbnD6J/o45Nr/hu2Nt2gd0mxhD/KDkGArsuKlu24Yo33AWnUQ8pxGZK60mFa2N3no5JdYcy3RzIdZsS3l66rhlw6iuoP/dkPpPQ/1nr/Gk0z54Ek4wej4PnUanniLIAQxAUiZXJZmHehoFNGeoplEL6c8RXc4hjflWzEwD2FWgFii6oETtSG3ljuyyydh9n7LtLbcuNL1hMpVPhyiVEipvhBROVCkorwLKx+eWv87TexsY/YtmAR6rRzSZ2vOK1sDdt8VD25Iq1sK6Fr8jLUd2vjLTcNZyBqdvv35iBlWcezQYoDadQf+5JuKur/mpvFT2Oq6LHUtFOAK0jNWA2ZpspORYf8P45IrQF6L8vq52dSXO0OzEvk+a8jdGkySunaLtfvpfgAG6/3eP6adRigGpqM0+O8Se14ZPkH0b2dh5OrrXyywuNkFkWblAFoJoNVC+/GrVd13kknzHiPxrdgNjWCwF2HUzs3IVN198Ct94AM3m1vg7WRHqOXWsdbnoOQN8wCrumYfpgoNJQvuGy8lrAq8efgW7W/WYYZ77O5WOPes+nFFTwOKbx6yjTYBWBgKmdjwb2Rd6Qs+8EopGz9Aq6tBBLegVdHn7GKTXbYOSamWsAcKCUEuDIEfZXIV/hIY1EPff3u2A7hc2BWFoR7VPT/kip9k+5clqYuPpGwKpm7oEbH2vnEMiU+GaGtG1svvFWaNc1VmfpiL7td4c0+10AA4gLor15UwGA50dw5SowyJtReOFpZA6UEHm03uePgYXwZb50+BgBzqCNPn+6G8Cx1eCUyM8pYeEmuSfuJ6mtzgSyNklmr5wn5eEAOwBg3tMEoHKowGb+P2CZ7pRYJxt79MzRUnMPvVao7rhybHEjZvxm/U2AR6xhxuQVu8GCoLT2DIf8AlZ4Mtph51z4+I+KolUEJ0soZggfACPJ/sotv7/famL5qW9j6vpbE4N7XkreOPEsmhdOewxF1w3TetPQo2UgGcBfstUdRHs2dQDj+hHklwLZzL7u6v3UX4Xgo+aBSIKF75MGbPyc7h2yse4qtghDa2gQWEjYW7aPrW7ESwMiAmuN2tbtILsCzcpTxtVenUmawMLbnRf0t4VmsPA+awJ5LBQtwP7+Pc2e4wi27RD5vXESWDr2KC5njmkIBM7g4pNH4baakNKOSD7MMcCRdTbqn+StkM/eM0VATU0wKjRf3Ifxdzmt2qMseDvh/c4aZii4lotzdvKxyfuPMQG9KTOyq2NLG8XIb/7b1zqRlaqnzaA1WEgPSBOefgD5q8QFCy/SmsIj3no8EHEIvJE/VUS+wKYQAtCeruDqyefQOHsStct2hZYfOIOlp77tYRCOT04KVpVlGT5zzPjZiPyUy96jCAw05cCMPSJEfa6g68P4u3MAyliFVXbUT835Gy5AJ2W5YDDGIupoQCUdH6PrDKJlGtGWIM8AtDdvrj2VfAjf4JW/0094xB/hb+UJCD5sOADWDCKv+8PC+0rSgru6hKUnH0Htsl1g1h77ngjNc6ex+sKzAAko1wlJPTEHYDITgz57iP6bTFjEJMCjyK6jet+QbQp9obFAgNoKYnHXSlsY9HbgwaT82aiHNqcNfeKEOXilM3zT+BjdEoASQ0MmtpNqqRv3idGGjRXd0YyAD+CFrD4XrBgXH3vYf24ROqOlp76N1sVFX5NQxW5hOWBy/w3CT2T8PsEnYfzJfQBR7d/ZSrm9cYA7GD93aQdW9+k/DwjsSy6UTAiMAIl1V/5FgYAPoMcZwAhH/mRJEAN1zcUYgVoIJdUz/N2Bfp1tbMbxuPnk7wbU/k5e8rTIWFpYeuZxqMYqZG0yTCkXnzgCpRUoMHgjAzApvhybX9ER2Mcw5v05vdGn7bwttxEI6b3ejw8pDWo1GGdow/dR7xddwx2fLzA23un4RTQ+RjwLCFd9GeJi/i4AGMbHwtdv9G/C+FvtbwkO/jbY2Cv8rUIm+5CkwMqLx7F07FFsufWVIBLQrSYWH/uWRx9vNKLZEoq/hvTuSb/mZ1NG1eT5s7H+2+zvU3rXV+YCkD6Mv8fL3+oF/yu0sKBP49cxlSETFuQYmTBrQGh8jHYWECzVDIa4hOtCgyHsKsSEJ6kljKWcItDhE4j2AxoiHpFjCdpukZOBlGAhcfHZJ7Hl1lcCRFg5+TzcVgv21h0+sciBbjWhmw2wUiApvOo4VDnWUaPdeA9kaCl7pUDa+Imjn4VOw5jSp0Htnyw/A4jGEKnElD+N8idbAjq5a8oYHeVYV2B8rAOHYGQA2nUgSMDash3Vy66AvXkLrNoELMv2dv/5xi/8KC+CTIH8qCoiSwun7DJ0CbTrwnG8Pj8JgcaFs5jYczus2oQx5ONCrS7DOXcGrdMnoRsrgLTDqRwyim+DpRAZP8Wn/cBR2WLyZrw2KLdVXS6M8nM6Sw7LmMFtBx6M8Weu5eK4ykyAxSDulCOy0NgJrAsyUNAbl1ObMLn7BlS2bIeUMjQs1i6Y/eWgQoMFgZQPq4XSXeS3/SgqSYO+Wgak3jh3Gq2L51Hdsh3Lx58FtLdyLOTpCwl701bYm7ejduU1aLzwLBrPH/O0/aT0nEBi04PX+4/APRFr/Xfu71PpKX/3BiC6qwDKYfahwxruQGCBc9IgRnxlMreRJxgfIzYf4INzojKByT0vg5zZ4in8uA7Iz/bia8CDReECJMw13QQEZUJslXj6MhNCQDcbWD11AtpxsHrmJMiy4uudmT02oNMCWTYmb7gFm17+asjqBNhxwrIjnvZT6I+EyfrloOORAPsyNQBKNP4ejECUF/m5oPH3SHhITBQajaPUYsbxMcLOwP+fp/XvGZ25SShrDDxKscnQ1ou+Rm23gJGXHKbxvl998ThWXzwOVV+FIJlcRhw5F2ag1UJl01ZsfsVrYU/NAMrxMQZf64/N5zaQ/RDjM0tlBqUUv5OIPcdF9lKTgiYtnpHuzPk4GXVnB1Y/JMCuyD19Gn/mqKGOxEDGxr8+SoFgMDYoqilDtzYQzCRDVIQMxZtklh+jpjOFxshGdBfSQv3UCahmE8J3PpThnMJaHgS4DmS1hk0vfxUuPvAVLzugeHQ3e//R69cG6J/eUk05a6jj9pSW0M9kBHDBxa9lE4H6JfekNlFnEB60UesnS5GkVNLY/NdTKZC95DEiCFGcJR8KB5ulgSnhHzmJ2L9DRSKCsGw4yxexcvwYZKVizA1Ejxfb3kteC5GUC3tyBjO33OFv+yUIipR+yeg8EHE87WcgOfpHhcg9XIDck7OCjouuBe3DAfQN9uUvpUf+AkxOlTqxpGncBlh3eEDE3Yqsnwx+fICjCTPyk2GgviEKEISPHYgQE/CNlIP7IGopBn8TY+xFeIPwvxcgCCkAt4XazitR3Xkl4JpZgFHvJ9erZhh/6fU++se+CpcA3oflTWdRH/39tu8utoY7MQyQ6vUlVVTGDmAdeYE0qsumaJ72lrbAi6gItPSZosgdugaODd0GkThYQUaUwB84vro8pOgGGIOfAgTPEPyfmDF1zY1wT5/wh5AoUe8nSvPY+8zW+i/D+JFc36MHxATUJthHAzD+ToQHZEiPjSP/uoUCyS/+44tekplAFJWjcbooZQ/afiGAZ8ZiTktCmpvfCbF/xM3d7OnDW4FDWqGyZRvszdvgnD8LsuxgsXxG1E+uWk/jDd2Te7g9Fs+DngZst6esy420PRl/hkIw2m3zHR/rIxNIrqAyGH5mByBst8VAQUISVmCKD97ENDoTa7iTdmq26mJOxW9RkLRR2b4TzrnT3uvhjECXkfJTH+SenlfOD2YYqN96P8ewOblilGNZv7lWOmj56eCW2CkyPtZXS5Bg6D4aYpmm/Hsw8hvV6NE2YCLTeXBUDERLpWPzKzF4kTMQ/MQ3ZEqbQcOe2ew5IXP4jE1uP5ef8qOo8RuSaoNjApbf30ePpQPn9Y7Hx7o4WHshPuxdcyT8TASQjC/tpMS+gWQ1GtKEfWuPjeEnAlR03wRAYGYBZJTyfltKVic8hqLZvaCUyFfpxs8d1EA6jQmX6wCGYPzcQRih046B8bFO1opnKONmTtKaLYCE4CgSgzbMbaQwTdwgtWCPYk4m1tIOhoCkjGoJ//mT1zphGMbPQP+CQN07gPjJXbvIX1iurM+V18waRGK8ZGQA54UzVmLH2oTmkk1TWCMQpmYOEftMwZHUWi7KdAyUgUfELzlD2djINJJXHBUisqEY2NdtvT/4cWBjK2oJ9X77yM/x/gMjY7VYokgs3fg1ICyQnPBegzPeNBRahV0BQQLsAI7T1RruIt7AyPpjny/F5u8NQhASuv9ktvmAfLWOTp2KuAa/STPmuKh36f39wsaf7IgFC3cHiwFwuVEfxVJ+zv0Hyjd+uwa9uozz//A3WP7W1+EuXxw7AP8zkRNTmLrl5dj6xrfB2rIDaK327gS4zSLNNmk8ZYB0YQmQnhrrjqDE2co9yYelAZJ70K3xY+B6AMUm+fpt8XVX73PbDmXPxm9V0TzxLJ7/5G+h/vTjILsSk5Ue+wDG8tEHcP4rX8Lun/4IJm98KeDUu9/GxJ1LuBillykB6sW5+Cm+fRLKL/h6Ou3tpQEz+zqBffl39FWNB94GHDHjLy0JYAaEhK6veMb/7FOwtmwHazXuMSbQdpqcgnP+LJ77o9/EDf/2o7C3XgYod2BZErPnXwJuf/bVafT3uQdsq80Fbo4ol6fcw12Re9obf2+XqOgnARik8bf3hAVAw54uMg3IKs7/wxeweuxxWJu2gF3HUyFJLi+9pG8a7LqQU9Nwzp7C2Xv+ChC2r+PQDxRYDNs1B34QApG9XxPZxk9po8+51rOHeQoYP+cYP+cYP+cYBg9DE1CnZEG6APsKaJgx53+v0eGCRPd6yJl1oABYYfnI/RCVihf5x0e+4SgXolbD8iPfBLdWQcLq0vo4dq1nfbTan/GP4F+OXV8Ubt6NI/SpzKCNhj61kfFNq1bH507WBOxLGr8pCcbclTMQfflr5tKNvz3Yx+XW+1nUVNWCu7Toy0CN0/7OV5CAXl2Crq94QGAv56wbeasuGj5FjL/4yxrCJF9X5B5uY08DcgADUS/tqt4ndDNc1BsGYENOTnmy0GPUv9A5E7VJiNqEB6B2e864HT2otwubzcE17s2JcIeB/MGAfdwF2NfO+HkwmoBra/xFZcb7xACEhalb7oBuNX3ZqvGRmzAJCd1oYHLPraDqNFi5PWqE9Q8VoAtJ+u66km2udc6p9zPrdO6u3u8F7OPuxXGs7kFATtdYBcg9w6iB+q8ABKAcbH3DW3H+K1+Ec+4M5NQ0WI2xgEzjbzUgp6ax/ft/CNDKO399c4E4Y1wo0vqP3Uzuf1IZIAXcZTgc5q5SfoxQvY8uibQlMAE5lQoNusVn7onLTBR5EBiAA2vLZdj9Ux/Bc3/0m3DOnYKo1vz6tls22Yaj7vs7LxmqtQQ5OY3d7/83qF51A+Csds8DMJh0qbhF8PT6ocEswEJ4cCAJTzLMdwDMph5PxgfUDvwTwn/NXNz4sRbkniLGzz0J41n9awIOkNyTmS9G46ID4QEKAbTqmLzxZbjh334UZ770l1h59CHo1WVkKlheagO8zBDVCUzuuRXb3/SDqF61p2cmILe7bDVgb94Ce2oaUkpIISCEtyTE3BoUk+cyJvk6GS0rBXfxPFSzkXjtwzf+flP+1J/qATuAgUf+IaX87Z3AKuxtO7Drh38B3FqFbqxe4uE/EsYQlRqoNu1daT3TgLntE1WvuArVTVshpfAdgIQgASkI5DsAxMRAIypw9kMmoHcC7C3b0TjxHJylxfiIbxeEuDUj9+TV+zzoacCECnM5xs8dhYc6pkFlS4MLAbgOmJsgaUHObB6PHYdr77XX9/eXc5SaYCgNe9tWyKlN0MqFIOmrQHOU/rPwFooGugDJ4f1Ozib4p5CoXn4VVH3F209AVBweXEtsqyTj704U1Gz7U/eGP3gAhAfCCyDy+QCuOzZ+87wMYjZCM0hKyMlpb4+fTIOAnFoImjB8onzkLwkEagVh2ZCT03AunEtsC2oT9dcc7OPS9DCs3gc3hsDnNxh+3NYhD2EvwJgTMDhgkROaeubqbC5DbaD94xBRN3SgAdX7RYyfC4jhdAcGin5P7GCHeTiX/ozxUpANmVmwUlD1VZAQsTVYxX1BYl1WKBaZsS5MCLB24a6u5GAAo0Xu4QJKWN1Wwl2tBzfEwVEeuSdHfIQTbK7gqzYGUpKzAONj/UX/pJaeEHDOn0V1agbW9Iy3rkd4m4K9WwQCRmPCJghYlGTk/bLx4nHoVsMjfbW5hkL6i1kLd5vyDxDsC3ASaBqCIMgQABCUTHgYH+vAEwTD/tpF44VngG07YE9PA0KChYAQBA6cQKAQnED/TS2/9mCjgnPhLNyVpbYdAMbo1/sMHpImICNbcLHLFh9zV54lI50ae4KNBQBklALMaJ47BbV4NuQASD8bsGDs/BMGIRDGCm7Ol9b0VH593mBA8OrB+IdD7ulU7w8LBNQDrveZ86cBU/ZOpYz/jo9RLgfgjReHM//CR/9FnAoscoYLKKnuQxnAHw/M+Esn9wzA+LteDTZI428P8nABbHMMBm4Ew+fUQE8RhJ4yv20/Vsxd+CIuSaa7vHofa6MJaO5s5tGpgQJq8NgDrHvjL35hc8raCxl+17/ieGMBa0vuaW/8FNthMBgHMGRyT2EAZHxsDF9QmIdPXXfrO+mMrAuwj9vhc91HQatrBJAz0qw+6v18lL/PE1K2IuX4GBgxqmcyp7+lO6XUW7Lxp1zOmpB72k82diqiS2UCllHvF2Iacg5QHOiy8RAMnwiwbfTEmdrI8dp1fAUg0T/+32PKnz+vXL7xr90wT1HjHxIGkLcZrLPxF0+DOoOBPKQNOFVAuXBOn/SmAYlwqU8DB9OA9radgD0BOI3+sgHu+qpLSIZQLxbevt7vuJBzNMA+LqENYHX9WdFa1kDmi+DBrQX0jb/x9KNYfOAf4Jw73Zvc1UY9hIS9eStm7ngdpm65o/e1aYXqfc4f5hlmvc9FKbfDIffkGv/AxoGpP3JPOQAIo0/JuIJrwSawcuRrOPvlz3m0U8sG2ZWx4Rsn27lwFmfv/Su4F89j83fd2X8mUKRFQFHN3w4QLD/lH6bx95jy5+0YKBUDyBgH7hfsi70dzl9F1S7y9wqAZL5eqwLn9HGc++o9EHbVlwLTYyAwGQ8sG2TZWPz6l1HdeSVq19wMuI2eMYGOFkdZhcAw6v0ixj8kck8740dSGm1Q04DUJ7mHc8g9nLeGupO3KzX3B8jC8iMPgp0WIEVXgxWX3JZgfxhn+egDMXFOlKwREIG+uv1N+7cMh51L7unC+Nu5lSL1Pnca5unL+HsLhD0vBx1GDcQF9ORKlroFVAutMyfaiEOMj7iAh4XWudPgxjLIrvoOk/qO/qw0ICSoUgUFeoD+IJAQiVkAptSWYDBDO01vpb2QyT3aBbtaxabiBkvu6Vzv96MM1NNy0MGrmXD3hIcStwOPZcC7dQTaU/DpuUuS+DyVgrV5K2o7d8GuViNNQJGjCcgRt98U99CtJpovHvfn/WUmnW8gxl8muadj1Edfw3Gil7UAeel618o9eZG/7QnJmkYsMa21KrBmNnup5PgoIBKsIaemIaqT/jmj/rqMSkNOTqN6xW6INsArJ7Q+sy4CWZvAxO7rIWsTACsUW8tV0Fm1NX4uCPaVaPw9amKIrpWAuZd6PwPsyzohHVY5pZ6l9AzdA5Ymb7jNWwxKY/JPJ+FUdlqYvP4WQFZ6cJqc2fGztmzzOgoZDiWbQMS5y0vJsmBv3e6tejNmA/ut97kv5Z4y6n30Bvv3zQSkIaZBKbCPO+9q6xcDcBuY3HM7po49guXHHoacnEk1H8aR30+xV5ZQveo6TN/+XYDb7F0hOKYHIkDSx18EFQ3/+XRlZgir4hGGmPtL+TsY7TDq/SLGr4exGGQoNVAqmaLMsQ8uOyVgjW373gmyK1h57GEPE6CxFzCXg0AITNxwK7a/8e0eYKrcvngAbOxn5OCxsrhesTY0FepUsNPyskvfIfRq/MydulqDJfd0rvdpkJqAwzX+6GRzAcIDF5gd7+IC1wokJbbd+QOYfskrUH/uSajVlUhE4hI2fvY3A9V2X4fa7hu8896P8XN6Gadz4RyqM5sBKdOlY1HjB0DSAisXzfNnvGyiV+Pn1ErM4ZF7CkZ9Dvky3bUCex4HLoXc0+2SD45vk8se0i5p0o014DRR2XUNKruux3gxYGpBoJf2M0qJ/JEoqIRaXULj5HOY2HklRLXakfeTd6hGHY2Tx6Ea9agLUHJ/HyNQ7/czEmB1a/xltPi4o+hnO5mYRCrFA0x1CYDTynH/l7oPCBZzoDTjN2cN3OWLqDfqsKs1QxMwzgMgECD81WAw2oA+Iq58HsCgjL9v5Z5SjX/Q48BaD6Hn2blbMMhFQLnZwHgpSPZcyACFQYPNQ7rV9L43ZMGjnYCeJiCFlQFHq8L8TUJkpv79lrfUhoI2MHJPJ+Pnvj6YPjUByzf+zmDgGIjb0EqgSb8gjBVg/mowpogJGBtSy3LWZTL7CpKHBk3u4U4TeAPdDswdRLnKMv5ue55lLwcdHyPnFzJhgC7m98swfoxMvc9tRbuG0AYsAvZ1rve5Y72fEGbMYyeOjw2fFLQjpwxsmGcdGT8whMUgZUX9XOPPGjtqV0eNI/+G3hGSTdvlGFCbr1I1HOMfBrmnY+QfzjTgcFL+DDJA9oai8WqgDZ/yc7e6fzTglJ+HTe7JAvuKzc0NZBy4k7cto97n9vINXe+LHR8bxSf4MsCJoUMaVr3PI5Typ3xCb5JA3WsCtgNumbtL+XNPCHd1QmjsDy6Nep+pz0nQPlN+GiGwL9PAaHDjwO2Nn7s3/m7BPs4nBozXBG4M489P+Tmc++ndz5dX74+m8ffmE63+67T+6/1CYN/4uDS9hB/VOA/sowGl/CND7skzfi7WCh1MF6DM/n628QftvUywj9uc1EFo342pwMilAg+sAcAxAlBsIzDM7xmD7+971zphDck9BYwfQ1kOOkxyTyEwcFDG778JuwJAjoeBhjIMFI/8rFxoFiAWQPDVYAOCCWSLNp9LieQejH7Kzz2kzD1NAzJ67+8XSflzQQcudkJKifpCAJaN1olnxuPAGOA4cJser715O+ypKVhSQpAvDErkiYMSgVtNuBfPe8pBsecvmdyDdVLvM3f9pq3uYj7nx8GSjD96D1xAkIUHgP57KrKsXJz/8ufGgiA5giAXv/mPmLj2Jmx/49shJiZLcALm8llCbdfVqG7eCikEpJCQvhMIREFBBJIC9pZtaDx/DHDd2GdUGrkHa0vuKVzv9wiUWWVmy73W++n30IXxI705qgxpsHOH/msoCUaVse1nTQPWn/o2Tjfr2Pm2H/Gn97hvXIG1gr31csjpTWDXAUsL7O8FYCGgmSD8UgCaICenUN2xC40XnvHGfkuq9/sx/nLJPYMz/t42Aw3A+LlAys9t1wWXZJ/+WrDVxx/CyhNHIKc2AVqNjT/nZIupGTSPP43lI1/DzCvfCLRWe9AFNJR6mQEpICenjLQ+DQSG04BEgFKQk1MQlgVWCtyNkGsPKT86SNKXT+7p3vh5ULLghZR6SyL3dJgxwmA0QbwUcvWpo340GUuDo4NGBNkVrB57FFCt3kRBuSjltj1PgIcA9mEIk3yZ6UTWtZ4zBceD3AswEHJPTuRn7lzvlz4OQAS4LbhLi70r3F5imQCRgFpZhm4G0Z97VgX3SgANtbri72Q014Jl3TQgJdTqCrTjFJdx5+62UGGo9X5BsC/jL3qpBKxB1PvdkXuK6Hu3kQEv2wuQAEk5Nu4u9wNQYLB90es9+a7W+TOoTE7B2rwVkAIkpH/zFIFICo8NIAXU6goap05Ez98JiOwS7MOokXvyUv4e9c6tXoyfSqn3ixg/FzT+kuyfNWDVULlsF5onnvdWgo9piG0Mn8COi8q2HaDaNOA0+1IHNrTBUT/xHHR9FZWpKWgpoUj42oCRJqBuRm1A6tLwOxp/G0yqKNhXBrmnO+Mf5DiwRt/knqJpULvSITvyl9WDJoBdTL/kFVh+5JuA0tF68PGRuXSDmTF923ckRftLaTM4i2ehl85DSuG3AAVIAAIU/WdbPRh/jyk/sHZ8/kKRf4AlQKe1XB1T/l5OSNuVUJ3+oncMwN5xFba9/k04++XPeWmnZY+FQZOfl+uAnRY2v/pO1K69BXAava1S4/a6/iSEl/ITgUiEGoGhKOh6BPu6qvdzrvV23YKBLwYpud7nbur9QRm/uR7MaWDq9ldBTs1g8YF/gHPuNNh1xoZvyHbbW7Zj5o7XYeqWO3zjp8HNYbAGIDw+Pmc47SHV+6NA7ulk/IxBawIOi9yTafwZ6CcPKL11mqhddwtqV++Bc+4UdGM1ta7qkiQAMUNUarC37QTs6uCMPzkR2I3qdQ/knuJgH0YT7BuuJmAf5J4u0qBUyp9g4w4Un/OdAIhg77iiL8rEhqwBXAdw6gPeoOwPBRk+YO1S/g4Z8DDIPSVG/r5KgEHXQLlrwjJPGA1uIjCIbM44/c9emCIGSjUMDZ+6HFQcpPGveb2fbfzocTGA1dswaIkpf0cMg1OLaZkHhgC0dwTjY2g840EP84ye8fcW9fuVx7K6lwTVuflYqfV+gR2BKY7kuGW/MYx/wMM8Xdf7GL16n/vWWOx1NViP5B7ucJa5w4fDaMOVHtv+pWv81Ce5p4eoP5rGP+hxYNYdXmzv9X5H4+f2rnps/BtDZaiMYR5qtzOgrJSfh0nu6c74eZh6AIMEQDhX4GRs9RttHVBP9T51kTmUZPy0huQeHpBartUPR2Og9X77McRx2X9J7gbIS/vRVrBzeGDf2qT8nHwcPeBx4HKNv83wd9ETMt4Quj5tn7t0Epxs/HJfNT8XNn4eeeMfOAjoPT75CtmDrfe5zafVhWzI+NiwSQP7jiCHJDDoqD9Eck9vxs+DGAYyPSGVXgMVAfvGu8HHW4M7ThyulfEPnNzDHZ5j0OPAjIJ90xJPCLep9znISYaVA/BoKnNeCisIYss5qL0yNQ3W+IFhk3u6j/rMA9wOXDbYxx1EQPJPyBB2BAfPQ3L0JMIYnmApeMB8/FGI+u0iv//zPD2Cssg9WB8pf7cJsdWfJuDg+vuMYq0PHpQXYAakBQgbcFah663RCboMQAhPjx9yCBN5a700tE3aX1bK34v1jJDxr4Em4GDJPZ3q/cFGfg3YNaiL53HxoX9C84VnoJuN0RoHJoK9ZRumbrkDkze91JvO23DGz+2NPy8xGFjKj7Un92Rk0jyMcWCKaQIOCADhYsBOuA+EB1Cn+8bfPPEszt7zl3CXFkF2pbPs1BrYiru8iPqzT2DmhWew9Q1v9UuCjWT8VISZkwQK1sb4B0TuGaTxd9cF0CXU+x2Mn3NFQLKfo/x8gAFhQS1fxNm/+2uo+grk5DQ4pEGPjhPwVHElQAIXH/4fkDObsek73jiEGf3BG38hmW7iaFNwRjYwXONfm5Q/P2DyoBeDdE/u4UwYP470d4r63OmElFL3V7Dy7QfgLp4HVWpgrYwTyqN1Ywa0hqxNYulbX4deWfRwi/XCi2D0wz/PlIPom9yzjo2f/GtCD3YxSBHj73OYJyflz3zDPXyWbeOqdtA48QzIstaJGrC3zFSvLqN56gUPtFyn1Iie13IVRPqjh1jfYF/Og3S/Hanb7cCdyQgDNP6MDKIMWeSU8Id2I8BvXdFqtadbGOqm0Trk9vUwBACjCzhS9X6Z5B50NP5e7UCU4wlRcFVRhzZfO+PvxeX3VALYXnttnTEMiQTk5Ay8SRBa3y1/FFXgXKt6vwjYx+1Fepjb7PxDdn+/jfH3mgSLvlI1zjH+buv9HHIPcbk9z2LL7ixM7N7jyYCvBzCNCFAu5MxmVC+/ElDOusleiin3YHDDPF23+Uasv8/cT/DvzQEUAvu6Tfm5U9Qv8KlzSTsBVBNTL3klKjt2QTdWvC3BRKN589mJqlnH5ld+t7eeaz23Asuu98sk92D0kP7cLHpwmoBDrPdzTj73VUei0MprUa3isu//Fzhz71+idfrEaG4GYoC1AgmBra/9Pkzd9h29b+cZuRlhzib3UAlCNb2Qe8I5ZIJq1sHKBSwb0LwG5J42UZ8HuhqsP3JP38bPOc6cuVw4gAhwHVhbt+PyH/gJLH/7G6g/9yR0o+47AR4J4ychYG/bgalb7kD1yusBdwPQgXOktrL6+zRs4/dxFmfpIrTSEHItyD3tjZ8ChaWBTQNmDFwUJfcMZMBhUECd7wTIsjDziu/BzB2v9WrrUQLXiABZ8UC/jTALUEAZqlMS0Fa2q4SUH8xonjmdvYtiSOSeDo2GQbYBdTn1fhdRn7m98fMgZwL87bdorUY196hFS6fuXYwbwvgTsd3kO7U1fkNQlLk7H92N8UsJZ3kJzdMnIZIckSHV++1Tfh4OCDhM4y8sAjJITyDE6BoYifVt/EXAPupM3iqV3JN1EWkNIW2sPvsUVL3ubSgeErmns/EnhNGGMQ68ZsZfJtg3PkZ19rfLMV7urjArWO9Hxs8gacFZWsTSk49B2FZ0gQ6B3NPZ+PuriEVPDnuA5J72PU8eywFeIv6guEZ/WVE/u+YPdiCe/8Y/QzdXvYxwiOSeosY/cCag1uWQe3oTNOBsyiePPcGGQf25SyBrgOSeIPIDBFGp4vxDX0P95PMguwJoXhtyD+cYPw9pHHgt6/18TcBxWbCeD7Jsf6KRC4Uik9zTlT5Dl0g/mEFWBcwa577+FSw99RhEpVqa8fcO9rWP+hQOBQ1AFZgoYJhwLBQP0viZObtS4ITpjzeErLM8X0A16qg//zSmrroWZFc8ICso81I371qgkCREg6n3iUCWDSKB5vkzuPDNr6Fx+mSfxj+Yej9POo2ZwGBRngO4/Whwtk8LAoipg02XYfzGBgjOhwLHcX99p/8rx56Ac+YUpq6+DhOX7QRNTkHYNkgIkJAgKSCkBEmCIAFBBCEIRARBBC8mkVemR4Eq0/ipAPioXQfNM6ew8syTWH3+GNhVEHYVrHnNyD3dGD+YWRBBAGeNRIn7cgCHjpwKzuhKQITLbM2UTO5JnbCcxyE2PviNIox5KRxCgGwb7uoylh59GI1nJlDdshXVmc2oTE1BSglJAkIICEGQvtF7hh98jRLf4KOnQmAixxJn1WjAXb6I1uJ5OIvnwcqFsCsgy85Op4dI7ilu/LH3vwoAOICO1NWODmBfcJo0nyOm9LBpt1G/mwEHyin+CQm6uEfaYdcdG9Z6SQBcx5tlkAIkhBd9T5+Ec+okLBkZPBFB+luABCE0fGIv7EeRn1M6kd2Kd5AQIClBMkj5ec3JPe37+/HFqkxgQQQCnQcAHJ0lYKG0WYAXBwr2ZZ3uPOSPKeYsiAhauWicOz3uCKyLVh9h9dxZuI0GqlPTPghIIGlDEPlEGz/Si8jwRSzdT6b+8aAQXyDMBXaIcHTfgYJ9Zab82W09ZpwCgEOnTlHfGMCh4AmFOK6YE1uZh2X8nDmMRDHRUo2l48+M7X/kS3/vGrrw7DFoxwEJz5kT4IF8hEjThBhgkSK7EFGaLkjrR7lnUMYfPoXA86XxAPYd3em9H+LnHaU9hLFMck+e8SND4ZWTSpDkU/YZwrZx4clHPY62GGMBo3oEn8yLDz/oGX+GcUalfQblljKywXWm3DNI41dgQOvnyiMC3XYbA4By8XzdcZUARGDSfZF7CgIgeaJvMbRXa1jVGi48+QhWTz4Lsqpd9ULHx/CQf7JttC6ew4mHvgGrNgFonUnlJeMr5UjAm5N/I72ZpyRyD+epfvr31wzpKA0F8TQAnN65k/t2ADQ/zwBw5uL542CctKWAZm4r1tnWE3IHNZMMbXji7IvDNHIhLbQuLuL4V+/zdvlpPTa4UbN/rQFRwTP/cB+Wjj8Hq1qNPmdus/Az4x+E9aPR3/5aLzLM04bcw9E9JIEaSjVrhGMAMLuwoMugAjPPzYk7P3O4QYQnbClA5EuPDwjs4xxeKPmRPyCMhK0f8p7Uqk3gmXv/G9xAH3+cBWDUWn/sNHHkr/4U0rYj8R9ORHzKGgXmTFmw2CjQUNdylTXJV4Tcg7YK/X5ZwLYUAOHZ0zPXnii6P7ogY+hQwAL8hiUEwMS9kXu4QM+zvehb0hOGrX/NsCpVXHzuGB776z/xyoCNoI+3QQ6tXJA9gUf+6wJOPPQN2FPTYfpPhLCll+zjx+gdjOx18DkbpDivaG9b7/P6AfticzKsK0Qgxrf2Lyyog7OQReDwQg7gUGhj9IBOnTkuzOwrSnigDN9l7uU0L5gYFUBrVKdn8Ph/+TOcf+RBUHXa028bH2ub+isFUZ3E4jNP4J/+6HdRmZ4Op8tiBJ5Egk/EnUm8hcG+7qJ+O7CP25a4Xdb7ZRh/SLAmkKYHAGDHqb1U2jTgPuzTXgbH/2O56SgQrOTL4J5roCKEh6h9RPFLBMRk/JxBQoKVwj//pzk0zr0Iqk6C1TgTWEvjJ7sKt76Kew/8ClorS5C+ok7A5CNf1Sj8JCnO7CPOCQv+RUe0Xur9ImAfdwT7OF0zA5pES2uwxD8WBQALO4AACHz4heoTSuOJmiXBPkG6CNjXqd4PQaDs+YwM70LBZRPzCEQEsIZdm8DKyRfw3+f+FzTOnQFVp6DHmcDapP3VKbiNBj7/4Z/Hi0cfRmVqxkv9fYMXSCwzIq/ep8DkmRJjIf6/O4Biw17LVYZyT6d6PxNB8xMOS5BYddUFuzp5f1EAsBs9AL5vbq+1f2FBEeGrVUkgkO4J7CtY7wdgX6rmT9WJHDLCyE+DoBQq09O4cOwJ/P1HPoBzjz0MUZ0OI9IYHBxsqy/IuER1GheOPY6/+bn34rl/+gomNm0GlPKctxnlA92NxOdLWQM9bACCfrbAuctoOpF7ygL7hlPvc85STmLWFQ+cv//O/3L4As9BUEE6nNX956u+qGH9K81MmTPZ3Q44FAX7QPET4F8NHoJMUdTwMwFWGpWpGSyfOI6/+8jP4KXv+Wnc8gPvgahOAeyAHSdSfME6W6W3Flt5izD8CCC7AiIb7DTxrYXP4n988mNoLS+htnkzWKuIy2+m/hRldGR2AmIeobOE2CCiPjoJ1Qwb7Mt4HE1giwjEfA8AHDq0VwCHdakOYN/8YQUAjmvfd7HurFhCTLnMHMPiSjB+ApBKLWI8bzMZpLBECKOKHyqEYCjlolKbgKtc3H/37+DYoc/jprfPYvdr34CJ7VeMtcVQHrcvuAga50/j2H+/D0f+5s9w4qFvoDo1jerUtAcEhsaebvsRsfG7sMCL7peh+MspTGi0ZLp7CXQdU/7saUe54ji6yfT/AcChfYc1DnfHzCzm5efmBM3P6yM//64vTletNy21HE0gmZvyI6e/3+GEcMbJYQ1oMDT7m3DZcxRaMzQzlP+9ywzNGkp7/1bs/w0IrdUVOM0mJi67HDtuvwM7b38FNu2+BlPbd0DYvazV7s1p9OxqeBTrfIWVM6dx/tljOPnQgzjx0AO4+MJzkHYF1akpD+0nrzQLor850iuDQR8iyGDiT3iDP0KQX9b55R3FR3/BZCRwPEIy3UX0+nqr9zP2HuqqFKLhqqP/+Pp3vOzA/DxTF1dKlyXAIeF1A/lPBdGbc99w5ovlrj0htRMhNVNFAxAkMIg9cIkpmI5iMCtYtQnI2iSclYt4+vCX8NTffx4kJUSl5k0UwkBZmVMXQc+r0QqCVT1JO+fNZeSEJ+5BpJdSQlAcG8N2Gw1o14EQAlZtAhNbtnoRW6sI7EtEdwFvZIPI/z5M+ynK7ELDpjjpK6UXPkpruQaf8ptXDIN1RQjRhFqYn5/X+/butXD4sDsYB+CXAYLlf73YbC1agja7ys+/S633TcSXYwCIl/JTeGEEF0kEAgbXB0H4Xlb4v/FOvIK0bExsqniTn1pDawWtOXQaprhC8O/YeCllfyCZeiRdKN1S5jd9bIClrPVReRceZbqH5GtKCswQEapT09Fgj9aAUmFXhoyxXQpKANPwObpfkgxEiMqC1LAQElOha7yWa1jGz/E7M4HkiuNqJvxZt+l/1w6AAOaDs5L2L5w98vPv+G9TFftHF5WjYo9Teg0UIf0mcEvGFCiZSLKfFnrm7qWUTBw6B/aNSmsdwsdEAkJyXIeQKHZBxD849pdwcv7KKo6j1Cm1GuIClRiHiy+oza4skw5L7dKAHMUk9ofj49V5+Ivoc6SgNWeC8BROooRZmTANn2LGL4j9lB/xboBRJiAw/FiBn/ZmJkNwpOr9gRq/yYNmPWlbYtVRh99yz/2P8BwEzUMPVhV4IVAIwt0tpX+UwYJyhrHLMv54BDOQvgD8Q2TgpuEKX75MkPmaKDQcTQzBQbsxiuKBQWkj4pFpCOH7NfIQytAz9P+GjCgbGT51jjhBnpM3+UIJXYSMzZlsfjaU3aqlLANLPDGZzfoMFibCVh4lvnp3MOv/QNxDJPAACrM5s1wwMgLKdrSjsJaLh1HvZ+gSCK8ff3e36H9PIGBwzM3NiQPz8/zwz73z69MV+crVlqu9Ebxi9X5R9JOTY5D+lyQYyAHQxxHop3QAFGoPLGSG1sF9OQQRvYjPYM2xaB+SscLXmfbwjKJXY4cOVjv5tKLpZregIXdGmNs/SCLrCLMxs36Pp/tkKPuE9X/gGAxcIN4qjDiARAlMoMDS2FFV7unX+AFoWwjR0voF4tbNb77noVXqASruaS/APhwSBLgPs/6YRfZnonb6YKJ+LLKFtFAdsgO8C8K7k/BrWUGUCntEMPIjL9KwRx4ECz8T8HeChrV/sCQ0FrHzWlJtJFgp/e4oFbGDmQrK987GH7VfhJt88Li2AhNnzlwghrFFyB/lxg2O1+8xvb4oxReBrp9p/KCQvCUMDof5Ok3wL8gOGBm4DNahck939X7ysXVNCtFy9Sfuuvehlfu6BP/6ygCC6+HQT+ytbp+aeawm5e6mqzhgdpZl/DHBQwOV10HU9n+v/RRe+dE9ivJ+pNccZgmaOcogtA4fN0wymEO5E+Z0pOABL0lBlr9LiWL03m0p0ls2iqXsxwkns9iI/obTMhF/v+YPDD0w8hAEpITgpwH0CgNjCNP/OPMkU/dvI5B72hu/J/7JWi8rqfa89QsPnjkA0Dygh7IdmAA+NLdX3vmZww1i/k+TtiSdi5T0EflzzCOVahpkPrOmFOFF5qPPIhKZlACkIEgR6c0HF6EUFH31b5Kir9EN3s/9Gje8r3k/gdTjSP+xoxs8CWz/Jv1b+D2M9xN7b/HnFcLvoacen8KfC/81x26Iy24H94k/NvkS3SKWqnuPK/yevqHfT94avdjrjH02gfH7j2XOdrCZ+htU77xVwetMuSdzZCgT7OM856KmpSQGPvW2Lzx4GrOzohfj72M1mMcMZAZ988da/9d5wi/VLHl109GaKO1UejV+U/rRm/PhmAIsfECQtRdpyP8QBQEaBJFoYhPYKxzYT/0DoC9I+0Ge1IFBEWamECVPadIx5e8spJzPl3JacJQlt54F6iGBwpsRJ5/WzFkIIeKKa2bWnzQ2NmW9DDQuWUZQDAsw6L1GSzA0/ARgGDxv4BTikT+pCYjw895w5J422YNmsEVCLLvuBRb4DwzQgdsWeqaICfROAOVDB/bKV/zne1bA+I0JS1Ly7WcN86S1GVISL4VOSCwlRBRJiAz2WFBr+sslhBF9w4hoRrAgQgsRZgFRNBXGjbzIHERE83dk3MeImpKybhRGd5l5Q5hlBDeLCJaIbl7UR0ZWEb2fMOonfi4pivzxjEBE2YB5HgixcyfJkOwm8/kSGYqZFYTEHwP8Sxh/vP2HtOWvZ+WePozfC1KspiwhFPPvvPWL9584tHevnJ+H7lektee/57k5wtGj9PBlq1+btK1X1h1XASRLS/k5uQM9ruoSaJMF8wNmR0CHIi9sIP7hiQzvxyHyHxc20VkXGHcAkfIuyrKk07p+nI67XSNgkdsRDTnngomzMIEEek9IIPpIAX6xlp8BTlJSIMZotRIuDbAvsQpd25LIVep5kHvrm1//UB3z6Ir6W1oGEL62o0eJFhYUk/xgtFuhPOPPHhM2eTYcixrx1pMfdYAY51zEfh/V8mZkFGRE/eA+QDpqikTENmpuKfKieruoH/DjM7IFIwMJ6/JExhHcJ12/J7KeGP4Q4QCpzAAUz0JimYXwsZHo/EqIaKuPiQH4F5swQMB+jX89Kvd0X+8bAYG0rkoiDfrwXfc8tLJwdJaozwmRUoZgfXagevBn3vbprROVn7hQd1yiBL7Qp/FzTLaNM7XYNeIRPozuid6+ZpP1l9f/T3pmg5dQBMXvOeKg2EXXFnBtTzzo9Bl0/AXHF/FReluDUaZRKOAaIwcZOENU86cvSooBHZzNxN5A5J5c42dW07Yllx33nrfe+8CbD87Oyv0LC31LXVllOIADRxaY5+bEN879868sN923VaTY3lIGIFjCCfHGhOOof3KJcBQtOGQNevmRvzaZvLJABiAgcdhzD/kAFC85OSAFJF0tJW0owUulzDt5vIIkwmfwCrIvTUqYLbVv8VEWcpgc5qEc5qD5vzRTwKBExJdzcsbPQtImxQQ/Ykg/JQ1+kMY/8uSejErSezaLCE2lWxL65/sF/krPAACAZ2clLSyob/7MW/7lTLW2sNx03MDBFIk43K6YNc4TxyJ/YmuLySLkuIfWxv19GnUs0rPB9+cML89t+/4cv+g41qowZgkoIXMTnzRiRNz79IbU7KqICkb9TC55h3o/cyww2VlJq7VlUneTU3wp40+cmqQzRwej3Sj1ftL4/ed0N9u2daHlfOht9z7wu2VF/9J1cO6b22vdOX/YffADb/2/t03U3ne+3nRBZPVa76d/nE7LUugrx402/L2hMc+mRDlHYF/K8POaE/EnjPPtY5ZiOpEsRh5nt+g4TgXqOCbMRYUjOhh/FsuxjcWkjT+u12fiMpzIEtpG/Y4lyMYj9+Q5YGZWM7Yllx31pbfce/9dQaBFyavaylKaooXZWfGymeakquivV6S4edV1FAVzAn0af7qtYt5Xx+9i3seY8Y8ZNGch/cbFwsjuQPQbcbpA+ovV+xnkg8xUlBNz9FkXJKeSf85ap8uZLi33wqLUUBFSfP5ejX/9KPd0l32xj/qz5hebtnjl2z/3tRcP9Mj4G1QXIItPgls/9bdLq3Dfo1g3bEFgziuJuIDxcwHAKoPXTlENapJRQs46R8zBiKEGg5+OkLQSdRLiCjaUYLmZXQaBBCPR7I0nhmHiPzdZc8j8uYmsx7kCfqcC0euW5g0Rt0Ak3lv0b6O/b7TtBHGE5JvsSvP1mm2+EPEPzinFmX1Gyk+GBFg+/3ik13J1UL7OiVqp1QbxNygI2gJRU6sfe8fnvnZyoQ/G31AygGQpcP8H3vLerdXqnyw3HZe965K6BUDa9q8z0rJYScDZiK3O+uBMfKBDetfpgmmfbnJx5Z5Bp/xt6n3OOfGU85IptbcvPqxElBbwSF2C1B4HWs/KPd1e68xe3X++2frw2//+G79939691p09DPusiQOI4QE//dZ/t22i+uvnGy2HARsFwb68qM8d0jtOYQGct+05Dp5xABZydu+xnxHeLsk9o2r8mTlX1jlOXVycGHikPBTzkgH7uM3FpJndLbZtLTruZ9567/3vG5TxD1oMm+6b2yvvnD/sfvOn3/onmyaq773QaDrEvhPoot7PtpP0WdV5F0se6SNxsXDWw3dj/DyMen9Yxl/cAWdt5knLdlHWfhd0CggbQrmni89AM7szlmWtuOreu+69/80Ls7NidmFB90v4GQoGkHyf++YPq4Ozs/Lld3/+xxcbzr1bqxUbzE639T63Wehg/lW0ZTarN0W5V3tMotp/HOGrCAa1salXF9awgZx1YpFleAvvzxEmkfM4IGPqjdK3YFde5nMYL5zaPE7InMx5HJjvKfH44d+HuAHHJvrIYBVTxlmNNTZoMMa/Zmu5uqn3Cxh/3VX3nyLn3QBwZGGBB2X8g3YAIICP3LbgnbPV1rsvNp1Dm2txJ9BNvZ8zG536Ju/6iolShgJUxbjkMTAxuqwNICtxYxjPkPVzxF4Bcc5zBLqFxvsKHye2VptTP0/u1CDmjPcQn76MPQ8jreGfqt+Nv2LzUTne8qMsWT/O/PF6WsvVdb3P2X+omd0py7LqSh1dauKdP37PQyuYKxfxzzokBnwcPuxJl/3w//lU6ye/85YFVuq7Z6r2noajnEhGrDzjz1IuyVWNIdMpUGyENcb86zHlHx7YF7zgTBdltP4Sv+ekW0k/Difun1c9xjOOKIPIK72o3arvS4DcEzN+eJG/odTRVkt837u//PWTB2chX/rxwRr/UBdiBUtFvv6Bd0xWWP/tdMX6vsWG44DYLlpr9rcCmtE2O+tSuWfQ9f5wwb7i9X6vn8GlqNxT5DMwjP/rzZZ45zsOf+1kmUy/kXEAADA3BzE/D33f3r3W9psnP7upav/w+UbLZYakzA5wb1GfO0Db7SIOjwy5hzuP8XY0/nK7LZ2Mny7JtVy9OWCvScVqs21bK4760klq/dCP3/PQysFZyP0LUMNd7DZkJ3DAn2H+5k+99f+Yrlj/ZqnlsPK2jYp+jJ+549W+DtLNLi66HtiVw478G3otV48pPzM0CJixLbHquJ/+yr33/+Q8oHvR9V93DiAszefmiObn9YM/9ZaftIX4OBFV6o7yx4jLN/52bLBLndyT/5KHZfyXBrnHH0FXthRSEMHR+sN33XP/b8/5YPygAb+RcQBJnsD977/rdRUpPztpyxsXg5KAMpZCl2r8w6v3153x55F7+jD8S0q5J/saZYDVlGVZjtbH60r91Dv+7htfODg7KwfZ5x9lBwAgYgx+9SffvG2a6A8mbfs9K44LR2kliCQPsN7fWOSejZvyr3dyD2tWRCSnbQt15X6+4bo//c6//+bxQTL81o0DAAAT9Xzw/W95vyXoP1Rtedlio6W9uXIS67beH7ByD1/S9f7oKfckfqGZmSdtSzpa15n51950z/0fTV7zl7wDMEeJ9y8sqPvf/7Zrbcn/0SbxL7XWqLvKBaKyoN96f/DGv8YpfwFq9Wgb//pU7ol/vKwqQlgVIdDQ6vOrjvsrP3DfN4/MzUFgfm3q/ZF2AGFJYKRF97//rndVCP9+wrZe5pUF7DKilmG5YN+okXtGtN4vs/TacMo9Xp1vQViTlsSqq55kxvyb7/36n5iqWaNkbyPnAAC/VYg50Py8/txb3lK9apf+WRB9eNK2rlh2XCjFLsACKc3BMbmnO+MfftTfoOQezWAtSVhTUqKu3LPQ9HvLq0sfffdXH12am/NR/vnRiPoj7wCysIGvvPdNO6dt8XMa+NmpirWz4bpoukr5k2YiYwBtBJV7xvX+BiL3MNjbVVWRQtakRN1R5wj82RXGR9917/3PjlKtvy4dQIANHNq7VwZlwYPvfdNOURHvZeafqUp5MwNYcVwww2WwiJZMjck9Y3JP6fW+pyRPWhPImrAkBICmq59m8GcqAp/Y+8X7TwSl7L7Dh9Vatfc2jAPIcwT3/cTe2haaeCeRfp9m/v7pil1puRp1VwFgl70F2IKQt7N7TO4Zk3s6G7+3SZ21pxhPVlUSKkJg1XEVEe4TEJ++uGz/7bu/+tWloM7HGvb1N6wDyHMEAPDN9991i9L4F2D9Axr8XTO2TS4zGq6Cq7QmkGbiYL28J0d3yZF7yjf8jQb2sRc1PL4egcEkpCBRFQKSgGXXZQF6GMx/DQt/+abP3/8wDPB6PUT8de8AYnTi2VmB225jmp8PwZUH3/+ml7Ki7wf4TS7za6pSbq9IAc0MRyk4muF6q4E0MZkTLOTztKn3VJFy1YPjclicAJrSy0I4odTbi+JvmdqLvbDfsv6EEqk6Z4xvm++ME1KBlFTM55yFy5wSbY+BBEwJ1IFJSgJZJGD7K9RaWqOp9FmAH7QJX9Kkv/B9X/jGw4GRzwHi9tlZml1HEX/DOAAkRo0PHTokkqyqoz/2fdubAi/TSryaiV8N8EuU5usqlpyqSm9/XnJ5qMs8JvesV3IP53ADOXoL0lhKKijK1FqK4WhVB+g5AEck0QNE+Efl4ME3/d3XziLRqt6377CmEUT1L0kHkOUM9u3bp83MIAgwD7zn+3dxFdeQouu04GtZ8W4CLmPwTg1Uwbgs+wLW7S/sDtG2SMqv2/cqwRod5bMKGT+61V/MeWKNrsk9Gp2Auk6ZXw/kHg0QgYlAWvN5IloF+BwzzhD4eYJ4Wkr9NLF8Zt/MtSeSvfo5QOzbu1f4Rs9Yp9H+knAAWezCHadO0emdO7lIO4Y20qc7Pnr6bA/OzsrgmlnP6f0l7wCy3i8zsLDfcwrYB+AQsG/nTsZtt/EBzI8kWWN8lD2KDlo4Oks7Tp0Kr//TO3fykYUFnsfGivBjBzA+J+Oj0M7z8TE+xsf4GB/jY3yMj/ExPsbH+Bgf42N8jI/xMT7Gx/gYH+NjfIyP8TE+xsf42BDH/w/ubilGmLFJigAAAABJRU5ErkJggg=="
ICON_64 = "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"
ICON_32 = "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"

LOCAL_COMMAND = re.compile(
    r"^\s*(title|subject|role|my role|name|my name|goal|goals|agenda|participant|participants|people|todo|action|ask|q)\s*:\s*(.+)$",
    re.IGNORECASE | re.DOTALL)


def set_app_id():
    """Give Sidenote its own taskbar identity (so it shows its own icon)."""
    try:
        import ctypes
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("Sidenote.MeetingAssistant")
    except Exception:
        pass


# ---------------------------------------------------------------------------
# Drawing helpers for the window (rounded pills, icon tabs, rounded input)
# ---------------------------------------------------------------------------
SERIF = "Georgia"            # ships with Windows and macOS
UI_SCALE = [1.0]             # display scaling (200% on a high-DPI screen = 2.0)


def px(n):
    """Pixels at the current display scaling (Tk scales fonts, not pixel sizes)."""
    return int(round(n * UI_SCALE[0]))


def round_rect(canvas, x1, y1, x2, y2, r, **kw):
    r = max(1, min(r, (x2 - x1) / 2, (y2 - y1) / 2))
    pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2, x2 - r, y2,
           x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
    return canvas.create_polygon(pts, smooth=True, **kw)


class Tooltip:
    """A small label next to the pointer after a short hover."""

    def __init__(self, widget, text):
        self.widget, self.text, self.win, self.job = widget, text, None, None
        widget.bind("<Enter>", self._schedule, add="+")
        widget.bind("<Leave>", self._hide, add="+")
        widget.bind("<Button-1>", self._hide, add="+")

    def _schedule(self, _e=None):
        self.job = self.widget.after(500, self._show)

    def _show(self):
        if self.win is not None:
            return
        x = self.widget.winfo_rootx() + 4
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
        self.win = tk.Toplevel(self.widget)
        self.win.wm_overrideredirect(True)
        self.win.attributes("-topmost", True)
        self.win.geometry(f"+{x}+{y}")
        tk.Label(self.win, text=self.text, bg=SURFACE_HI, fg=FG, font=(FONT, 8),
                 padx=8, pady=3).pack()

    def _hide(self, _e=None):
        if self.job:
            self.widget.after_cancel(self.job)
            self.job = None
        if self.win is not None:
            self.win.destroy()
            self.win = None


class Pill(tk.Canvas):
    """A small rounded label, e.g. '● 12 min' or '3 people'."""

    def __init__(self, parent, text="", fg=MUTED, bg=SURFACE, parent_bg=BG, size=8,
                 command=None, height=22):
        height = px(height)
        super().__init__(parent, height=height, width=10, bg=parent_bg,
                         highlightthickness=0, bd=0)
        import tkinter.font as tkfont
        self.font = tkfont.Font(family=FONT, size=size)
        self.h, self.state_ = height, None
        self.pill_bg = bg
        self.command = command
        if command:
            self.configure(cursor="hand2")
            self.bind("<Button-1>", lambda e: self.command())
        self.set(text, fg)

    def set(self, text, fg=None, bg=None, clickable=None):
        fg = fg or MUTED
        bg = bg or self.pill_bg
        if (text, fg, bg) == self.state_:
            return
        self.state_ = (text, fg, bg)
        self.delete("all")
        if not text:
            self.configure(width=1)
            return
        w = self.font.measure(text) + px(22)
        self.configure(width=w)
        round_rect(self, 1, 1, w - 1, self.h - 1, self.h // 2, fill=bg, outline="")
        self.create_text(w // 2, self.h // 2, text=text, fill=fg, font=self.font)
        if clickable is not None:
            self.configure(cursor="hand2" if clickable else "")


class IconTab(tk.Canvas):
    """A tab drawn as an icon: 'plus' (new meeting) or 'history' (past meetings,
    a clock inside a counter-clockwise arrow, like a browser's History)."""

    def __init__(self, parent, kind, tip, command):
        super().__init__(parent, width=px(40), height=px(32), bg=BG, highlightthickness=0,
                         bd=0, cursor="hand2")
        self.kind, self.command = kind, command
        self.selected = self.hover = False
        self.badge = False
        self.bind("<Enter>", lambda e: self._set_hover(True))
        self.bind("<Leave>", lambda e: self._set_hover(False))
        self.bind("<Button-1>", lambda e: self.command())
        Tooltip(self, tip)
        self.draw()

    def _set_hover(self, on):
        self.hover = on
        self.draw()

    def set(self, selected=None, badge=None):
        if selected is not None:
            self.selected = selected
        if badge is not None:
            self.badge = badge
        self.draw()

    _glyphs = None

    @classmethod
    def _glyph(cls, kind):
        """Windows: the system icon font (smooth at any size). None elsewhere:
        the drawn icon is used (macOS draws canvas lines smoothly)."""
        if IS_MAC:
            return None
        if cls._glyphs is None:
            import tkinter.font as tkfont
            fams = set(tkfont.families())
            fam = next((f for f in ("Segoe Fluent Icons", "Segoe MDL2 Assets") if f in fams), None)
            cls._glyphs = {} if fam is None else {
                "plus": ((fam, 13), ""), "history": ((fam, 13), "")}
        return cls._glyphs.get(kind)

    def draw(self):
        k = UI_SCALE[0]
        self.delete("all")
        w, h = int(float(self.cget("width"))), int(float(self.cget("height")))
        c = FG if (self.selected or self.hover) else MUTED
        if self.selected or self.hover:                    # crisp underline, no rounded box
            self.create_rectangle(px(9), h - px(3), w - px(9), h - px(1),
                                  fill=ACCENT if self.selected else LINE, outline="")
        glyph = self._glyph(self.kind)
        if glyph:
            font, ch = glyph
            self.create_text(w / 2, h / 2 - px(2), text=ch, fill=c, font=font)
        elif self.kind == "plus":
            cx, cy, lw = w / 2, h / 2 - px(2), max(1.5, 1.8 * k)
            self.create_line(cx - 7 * k, cy, cx + 7 * k, cy, fill=c, width=lw, capstyle="round")
            self.create_line(cx, cy - 7 * k, cx, cy + 7 * k, fill=c, width=lw, capstyle="round")
        else:
            cx, cy, lw, r = w / 2, h / 2 - px(2), max(1.5, 1.8 * k), 8 * k
            self.create_arc(cx - r, cy - r, cx + r, cy + r, start=210, extent=-300,
                            style="arc", outline=c, width=lw)
            ax, ay = cx - r * 0.87, cy + r * 0.5
            self.create_polygon(ax - 4 * k, ay - 1 * k, ax + 3 * k, ay - 2 * k, ax - 1 * k,
                                ay + 4 * k, fill=c, outline=c)
            self.create_line(cx, cy, cx, cy - 4.5 * k, fill=c, width=lw * 0.85, capstyle="round")
            self.create_line(cx, cy, cx + 3.5 * k, cy + 2 * k, fill=c, width=lw * 0.85,
                             capstyle="round")
        if self.badge:                                     # a meeting is recording
            self.create_text(w - px(9), px(8), text="●", fill=ACCENT, font=(FONT, 6))


class InputPill(tk.Canvas):
    """A rounded input box with a round send button, holding an Entry or Text.
    set_enabled(False) greys the send button out and ignores clicks on it."""

    def __init__(self, parent, command, parent_bg=BG, radius=21):
        super().__init__(parent, height=px(44), bg=parent_bg, highlightthickness=0, bd=0)
        self.command, self.r = command, px(radius)
        self.inner, self._win = None, None
        self.enabled = True
        self.bind("<Configure>", lambda e: self._draw())

    def hold(self, widget):
        """widget must be created with this pill as its parent."""
        self.inner = widget
        self._win = self.create_window(px(18), px(8), window=widget, anchor="nw")
        widget.bind("<Configure>", lambda e: self.after_idle(self._draw), add="+")
        self._draw()

    def set_enabled(self, on):
        if on != self.enabled:
            self.enabled = on
            self._draw()

    def _send(self):
        if self.enabled:
            self.command()

    def _draw(self):
        w = max(px(80), self.winfo_width())
        ih = self.inner.winfo_reqheight() if self.inner else px(22)
        h = max(px(44), ih + px(18))
        if int(float(self.cget("height"))) != h:
            self.configure(height=h)
        self.delete("shape")
        round_rect(self, 1, 1, w - 2, h - 2, min(self.r, h // 2), fill=SURFACE, outline=LINE,
                   tags="shape")
        cx, cy, rr = w - px(23), h - px(22), px(14)
        self.create_oval(cx - rr, cy - rr, cx + rr, cy + rr,
                         fill=ACCENT if self.enabled else SURFACE_HI, outline="",
                         tags=("shape", "send"))
        self.create_text(cx, cy, text="↑", fill="#ffffff" if self.enabled else FAINT,
                         font=(FONT, 11, "bold"), tags=("shape", "send"))
        self.tag_bind("send", "<Button-1>", lambda e: self._send())
        self.tag_bind("send", "<Enter>",
                      lambda e: self.configure(cursor="hand2" if self.enabled else ""))
        self.tag_bind("send", "<Leave>", lambda e: self.configure(cursor=""))
        if self._win is not None:
            self.coords(self._win, px(18), (h - ih) // 2)
            self.itemconfigure(self._win, width=max(px(40), w - px(18) - px(48)))

def fmt_day_iso(iso):
    """'2026-11-12' -> 'Thu 12 Nov' (with the year if it isn't this year)."""
    try:
        d = datetime.date.fromisoformat(iso)
    except Exception:
        return iso or ""
    return fmt_day(d) + ("" if d.year == datetime.date.today().year else f" {d.year}")


class Overlay:
    """The Sidenote window.

    Layout, by priority:
      header   meeting title + one muted line of meeting info, menu on the right
      answer   Claude's latest answer (the main content), your question above it
      hearing  one faint line of what Live Captions is hearing
      input    the question box
      status   small footer: Sidenote state on the left, captions + time on the right
    Confirmations ("saved", "added") appear briefly in the footer, never in the
    answer area.
    """

    PLACEHOLDER = "Ask Claude about the meeting..."
    MISSED_PROMPT = f"What did I miss? (last {MISSED_MINUTES} min)"
    SUGGEST_PADY = (8, 14)        # (above, below): keeps it clear of the text bar

    def __init__(self, server_thread):
        self.server_thread = server_thread
        self.toast_until = 0
        self.toast_text = ""
        self.root = tk.Tk()
        if IS_MAC:
            # macOS draws a 9 pt Tk font as 9 px; scale up to normal Mac text sizes
            self.root.tk.call("tk", "scaling", MAC_UI_SCALE)
        try:
            UI_SCALE[0] = max(1.0, self.root.winfo_fpixels("1i") / 96.0)
        except Exception:
            UI_SCALE[0] = 1.0
        self.root.title(f"Sidenote {SIDENOTE_VERSION}")
        try:
            self._icons = [tk.PhotoImage(data=ICON_256), tk.PhotoImage(data=ICON_64),
                           tk.PhotoImage(data=ICON_32)]
            self.root.iconphoto(True, *self._icons)
        except Exception as e:
            log.info("Could not set icon: %s", e)
        # Size relative to the screen: about 28% wide and 58% tall
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        w = max(400, min(int(sw * (0.38 if IS_MAC else 0.30)), 740))
        h = max(520, min(int(sh * (0.82 if IS_MAC else 0.78)), 1100))
        geometry = self._saved_geometry(sw, sh) or f"{w}x{h}+40+40"
        self.root.geometry(geometry)
        self._opened_at = time.time()
        # macOS: apply the size again once the window is really on screen, so
        # the content is laid out at the full size (otherwise part stays black)
        self.root.after(150, lambda g=geometry: self._apply_geometry(g))
        self.root.after(700, lambda g=geometry: self._apply_geometry(g))
        self.root.after(1500, lambda g=geometry: self._apply_geometry(g))
        try:
            w = int(geometry.split("x")[0])
        except Exception:
            pass
        self.root.minsize(320, 380)
        self.root.configure(bg=BG)
        self.root.attributes("-topmost", True)
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

        pad = 16
        self._build_tabs()                          # ＋ and past meetings, always on top
        self.rec = tk.Frame(self.root, bg=BG)      # the meeting being recorded

        # ---- header ---------------------------------------------------------
        header = tk.Frame(self.rec, bg=BG)
        header.pack(fill="x", padx=pad, pady=(px(12), 0))
        end_border = tk.Frame(header, bg=LINE, padx=1, pady=1)    # (moved to the tab row)
        self.end_btn = tk.Label(end_border, text="End meeting", bg=BG, fg=MUTED, cursor="hand2",
                                font=(FONT, 9), padx=10, pady=3)
        self.end_btn.pack()
        self.end_btn.bind("<Button-1>", self._end_btn_click)
        self._hover(self.end_btn, BG, SURFACE, fg_on=FG, fg_off=MUTED)

        titles = tk.Frame(header, bg=BG)
        titles.pack(side="left", fill="x", expand=True)
        self.title_label = tk.Label(titles, text="", bg=BG, fg=FG, anchor="w",
                                    justify="left", font=(SERIF, 18))
        self.title_label.pack(fill="x")
        self.title_label.bind("<Button-1>", lambda e: self._edit_info_from_click())
        self.info_label = tk.Label(titles, text="", bg=BG, fg=MUTED, anchor="w",
                                   justify="left", font=(FONT, 9))
        self.info_label.bind("<Button-1>", lambda e: self._edit_info_from_click())
        pills = tk.Frame(titles, bg=BG)            # ● 12 min · 3 people · captions source
        pills.pack(fill="x", pady=(px(12), 0))
        self.p_time = Pill(pills, "", fg=ACCENT_HI)
        self.p_time.pack(side="left")
        self.p_people = Pill(pills, "")
        self.p_people.pack(side="left", padx=(4, 0))
        self.p_source = Pill(pills, "", command=self._footer_click)
        self.p_source.pack(side="left", padx=(4, 0))

        # View toggles: open lists next to the answer when you want them
        chips = tk.Frame(self.rec, bg=BG)
        chips.pack(fill="x", padx=pad, pady=(px(18), 0))
        self.show_label = tk.Label(chips, text="", bg=BG)     # (no 'Show' label any more)
        self._compact = False
        self.chips = {}
        for key, label in (("agenda", "Agenda"), ("context", "Context"),
                           ("questions", "To ask"), ("actions", "Actions"),
                           ("transcript", "Transcript")):
            chip_border = tk.Frame(chips, bg=BG, padx=0, pady=0)    # plain text tabs
            chip_border.pack(side="left", padx=(0, 2))
            chip = tk.Frame(chip_border, bg=BG, cursor="hand2", padx=8, pady=3)
            chip.pack()
            box = tk.Label(chip, text="", bg=BG)          # (no checkbox glyph any more)
            name = tk.Label(chip, text=label, bg=BG, fg=MUTED, font=(FONT, 9), cursor="hand2")
            name.pack(side="left")
            badge = tk.Label(chip, text="", bg=SURFACE_HI, fg=FG, font=(FONT, 7, "bold"),
                             padx=5, pady=0, cursor="hand2")
            parts = (chip, box, name, badge)
            for part in parts:
                part.bind("<Button-1>", lambda e, k=key: self.toggle_panel(k))
                part.bind("<Enter>", lambda e, k=key: self._chip_hover(k, True))
                part.bind("<Leave>", lambda e, k=key: self._chip_hover(k, False))
            self.chips[key] = {"frame": chip, "border": chip_border, "box": box,
                               "name": name, "badge": badge}

        self._divider = tk.Frame(self.rec, bg=LINE, height=1)
        self._divider.pack(fill="x", padx=pad, pady=(px(10), 0))

        # ---- name question: asked once, inline (no popup, never takes focus) --
        self.name_bar = tk.Frame(self.rec, bg=SURFACE, padx=10, pady=6)
        tk.Label(self.name_bar, text="What name should Sidenote use for you?", bg=SURFACE,
                 fg=FG, font=(FONT, 9), anchor="w").pack(fill="x")
        row = tk.Frame(self.name_bar, bg=SURFACE)
        row.pack(fill="x", pady=(4, 0))
        close = tk.Label(row, text="✕", bg=SURFACE, fg=MUTED, font=(FONT, 9),
                         cursor="hand2", padx=4)
        close.pack(side="right")
        close.bind("<Button-1>", lambda e: self._name_later())
        save = tk.Label(row, text="Save", bg=ACCENT, fg="#ffffff", font=(FONT, 9, "bold"),
                        padx=10, pady=2, cursor="hand2")
        save.pack(side="right", padx=(6, 4))
        save.bind("<Button-1>", lambda e: self._name_save())
        self._hover(save, ACCENT, ACCENT_HI)
        self.name_entry = tk.Entry(row, bg=BG, fg=FG, insertbackground=FG, relief="flat",
                                   font=(FONT, 10), borderwidth=0, highlightthickness=1,
                                   highlightbackground=LINE, highlightcolor=ACCENT)
        self.name_entry.pack(side="left", fill="x", expand=True, ipady=3)
        self.name_entry.insert(0, os_full_name())          # pre-filled guess
        self.name_entry.bind("<Return>", lambda e: self._name_save())
        self._name_bar_shown = False

        # ---- footer (packed before the body so it always stays visible) -----
        footer = tk.Frame(self.root, bg=BG)
        footer.pack(side="bottom", fill="x", padx=pad, pady=(6, 10))
        self.state_dot = tk.Label(footer, text="●", bg=BG, fg=FAINT, font=(FONT, 8))
        self.state_dot.pack(side="left")
        self.state_label = tk.Label(footer, text="", bg=BG, fg=MUTED, font=(FONT, 8), anchor="w")
        self.state_label.pack(side="left", padx=(4, 0))
        self.right_label = tk.Label(footer, text="", bg=BG, fg=FAINT, font=(FONT, 8), anchor="e")
        self.right_label.pack(side="right")
        self.right_label.bind("<Button-1>", lambda e: self._footer_click())
        self.footer = footer
        self.caption_dot = tk.Label(footer, text="●", bg=BG, fg=FAINT, font=(FONT, 8))

        # ---- input ----------------------------------------------------------
        self.input_pill = InputPill(self.rec, self.send)
        self.input_pill.pack(side="bottom", fill="x", padx=pad, pady=(4, 0))
        # Grows from 1 to 4 lines as you type, then scrolls (Shift+Enter = new line)
        self.entry = tk.Text(self.input_pill, bg=SURFACE, fg=FG, insertbackground=FG,
                             relief="flat", font=(FONT, 10), borderwidth=0,
                             highlightthickness=0, height=1, wrap="word",
                             padx=0, pady=2, undo=True)
        self.input_pill.hold(self.entry)
        self.entry.bind("<Return>", self._on_return)
        self.entry.bind("<KeyRelease>", lambda e: self._grow_input())
        self.entry.bind("<FocusIn>", self._clear_placeholder)
        self.entry.bind("<FocusOut>", self._show_placeholder)
        self.send_btn = self.input_pill
        self._placeholder_on = False
        self._show_placeholder()

        # ---- suggested prompt (just above the input; click = as if typed) ------
        self.suggest_row = tk.Frame(self.rec, bg=BG)
        self.suggest_row.pack(side="bottom", fill="x", padx=pad, pady=self.SUGGEST_PADY)
        # Looks like an autosuggestion: faint italic text with a sparkle, no box
        self.missed_btn = tk.Label(self.suggest_row, text="\u2726  " + self.MISSED_PROMPT,
                                   bg=BG, fg=FAINT, cursor="hand2",
                                   font=(FONT, 9, "italic"), padx=4, pady=2)
        self.missed_btn.pack(side="left")
        self.missed_btn.bind("<Button-1>", self.what_did_i_miss)
        self._hover(self.missed_btn, BG, BG, fg_on=FG, fg_off=FAINT)
        self.entry.bind("<KeyRelease>", lambda e: (self._grow_input(), self._update_suggestions()),
                        add=False)

        # ---- hearing line -----------------------------------------------------
        self.tail = tk.Label(self.rec, text="", bg=BG, fg=FAINT, font=(FONT, 8, "italic"),
                             justify="left", anchor="w", wraplength=w - 2 * pad)
        self.tail.pack(side="bottom", fill="x", padx=pad, pady=(8, 0))

        # ---- answer (main content) -------------------------------------------
        self.paned = tk.PanedWindow(self.rec, orient="vertical", bg=BG, bd=0,
                                    sashwidth=px(16), sashrelief="flat", showhandle=False,
                                    opaqueresize=True)
        self.paned.pack(fill="both", expand=True, padx=pad, pady=(8, 0))
        self.panels = {}
        self.panel_text = {}
        self.panel_count = {}
        for key, title in (("agenda", "Agenda"), ("context", "Context"),
                           ("questions", "To ask"), ("actions", "Action items"),
                           ("transcript", "Transcript")):
            frame = tk.Frame(self.paned, bg=BG)
            head = tk.Frame(frame, bg=BG)
            head.pack(fill="x", pady=(px(10), 0))
            tk.Label(head, text=title, bg=BG, fg=FG, font=(FONT, 9, "bold"),
                     anchor="w").pack(side="left")
            count = tk.Label(head, text="", bg=BG, fg=FAINT, font=(FONT, 8), anchor="w")
            count.pack(side="left", padx=(8, 0))
            self.panel_count[key] = count
            tk.Frame(frame, bg=LINE, height=1).pack(fill="x", pady=(px(7), px(4)))
            text = tk.Text(frame, wrap="word", bg=BG, fg=FG, relief="flat",
                           font=(FONT, 9), padx=px(4), pady=px(4), borderwidth=0,
                           highlightthickness=0, spacing1=px(4), spacing3=px(4),
                           cursor="arrow", height=3, selectbackground=SURFACE_HI)
            text.pack(fill="both", expand=True)
            text.tag_configure("muted", foreground=MUTED)
            text.tag_configure("faint", foreground=FAINT)
            text.tag_configure("done", foreground=FAINT, overstrike=True)
            text.tag_configure("box", foreground=MUTED)
            text.tag_configure("check", foreground=OK)
            text.tag_configure("meta", foreground=FAINT, font=(FONT, 8))
            text.tag_configure("speaker", foreground=MUTED, font=(FONT, 9, "bold"))
            text.tag_configure("time", foreground=FAINT, font=(FONT, 8))
            text.tag_configure("note", foreground=ACCENT_HI)
            text.tag_configure("ask_owner", foreground=WARN, font=(FONT, 8, "bold"))
            text.tag_configure("hover", background=SURFACE)
            text.configure(state="disabled")
            self.panels[key] = frame
            self.panel_text[key] = text
        self.visible = []          # open panels, in display order
        self._last_transcript_count = -1

        body = tk.Frame(self.paned, bg=BG)
        self.paned.add(body, minsize=60, stretch="always")
        self.body = body
        card = tk.Frame(body, bg=BG)                 # answers sit on the background
        card.pack(fill="both", expand=True, pady=(8, 0))
        # The conversation, like in Claude: your message, then Claude's reply.
        # Newest exchange on top; scroll down for the earlier ones.
        self.answer = tk.Text(card, wrap="word", bg=BG, fg=FG, relief="flat",
                              font=(FONT, 10), padx=4, pady=10, borderwidth=0,
                              highlightthickness=0, spacing2=2, spacing3=5, cursor="arrow",
                              height=3)
        self.answer.pack(side="left", fill="both", expand=True)
        self.answer.tag_configure("hint", foreground=FAINT, font=(FONT, 9))
        self.answer.tag_configure("muted", foreground=MUTED)
        self.answer.tag_configure("you_name", foreground=MUTED, font=(FONT, 8, "bold"),
                                  spacing3=2)
        self.answer.tag_configure("claude_name", foreground=ACCENT, font=(FONT, 8, "bold"),
                                  spacing1=6, spacing3=2)
        self.answer.tag_configure("time", foreground=FAINT, font=(FONT, 8))
        self.answer.tag_configure("you", foreground=FG, background=SURFACE,
                                  lmargin1=0, lmargin2=0)
        self.answer.tag_configure("claude", foreground=FG)
        self.answer.tag_configure("divider", foreground=LINE, font=(FONT, 6),
                                  spacing1=6, spacing3=6)
        self.answer.tag_configure("notice_name", foreground=MUTED, font=(FONT, 8, "bold"),
                                  spacing3=2)
        self.answer.tag_configure("notice", foreground=MUTED)
        self._notice = None            # status shown above the conversation (or None)
        self._pending_hint = "Thinking…"   # under a question Claude hasn't answered yet
        self._feed_sig = None          # what the conversation view shows now

        self.root.bind("<Configure>", self._on_resize)
        self._set_answer("", empty=True)
        self.screen = None
        self._build_start()
        self._build_history()
        if live.record_on_open:                  # the user asked Claude to record right away
            self.start_recording()
        else:
            live.mode = "home"
            self.select_tab("live")
        self.root.after(300, self.refresh)

    # ---- remembered window size and position -------------------------------------
    GEOMETRY_FILE = os.path.join(SAVE_DIR, ".window.json")

    def _saved_geometry(self, sw, sh):
        try:
            import json
            with open(self.GEOMETRY_FILE) as f:
                g = json.load(f)
            w, h, x, y = int(g["w"]), int(g["h"]), int(g["x"]), int(g["y"])
            if 300 <= w <= sw and 360 <= h <= sh and -50 <= x < sw - 100 and -50 <= y < sh - 100:
                return f"{w}x{h}+{x}+{y}"
        except Exception:
            pass
        return None

    def _apply_geometry(self, geometry):
        try:
            if time.time() - self._opened_at < 3:      # only during start-up
                # macOS Tk can keep laying out at the first tiny size while the
                # real window is bigger (black area). Setting the same size is a
                # no-op, so change it by 1 px and back to force a real resize.
                size, _, pos = geometry.partition("+")
                w, h = (int(v) for v in size.split("x"))
                self.root.geometry(f"{w + 1}x{h + 1}+{pos}")
                self.root.update()
                self.root.geometry(geometry)
                self.root.update()
                self._layout()
        except Exception:
            pass

    def _remember_geometry(self):
        try:
            import json
            if time.time() - getattr(self, "_opened_at", 0) < 3:
                return                                  # still opening: size not final
            self.root.update_idletasks()
            g = {"w": self.root.winfo_width(), "h": self.root.winfo_height(),
                 "x": self.root.winfo_x(), "y": self.root.winfo_y()}
            if g["w"] < 300 or g["h"] < 360:
                return
            os.makedirs(SAVE_DIR, exist_ok=True)
            with open(self.GEOMETRY_FILE, "w") as f:
                json.dump(g, f)
        except Exception:
            pass

    # ---- small helpers --------------------------------------------------------
    def _hover(self, widget, bg_off, bg_on, fg_on=None, fg_off=None):
        widget.bind("<Enter>", lambda e: widget.configure(bg=bg_on, **({"fg": fg_on} if fg_on else {})))
        widget.bind("<Leave>", lambda e: widget.configure(bg=bg_off, **({"fg": fg_off} if fg_off else {})))

    def _input_text(self):
        return self.entry.get("1.0", "end-1c")

    def _clear_placeholder(self, _e=None):
        if self._placeholder_on:
            self.entry.delete("1.0", "end")
            self.entry.configure(fg=FG)
            self._placeholder_on = False

    def _show_placeholder(self, _e=None):
        if not self._input_text().strip():
            self.entry.delete("1.0", "end")
            self.entry.insert("1.0", self.PLACEHOLDER)
            self.entry.configure(fg=FAINT)
            self._placeholder_on = True
            self.entry.configure(height=1)

    def _update_suggestions(self):
        """Hide the suggested prompt while you are typing your own question."""
        typing = not self._placeholder_on and bool(self._input_text().strip())
        shown = bool(self.suggest_row.winfo_manager())
        if typing and shown:
            self.suggest_row.pack_forget()
        elif not typing and not shown:
            self.suggest_row.pack(side="bottom", fill="x", padx=16, pady=self.SUGGEST_PADY,
                                  before=self.tail)

    def _on_return(self, event):
        if event.state & 0x0001:          # Shift+Enter: new line
            self.root.after(1, self._grow_input)
            return None
        self.send()
        return "break"                    # don't add a newline

    def _grow_input(self):
        """1 line by default, up to 4 lines, then the box scrolls."""
        try:
            lines = int(self.entry.count("1.0", "end", "displaylines")[0])
        except Exception:
            lines = 1
        height = max(1, min(4, lines))
        if int(self.entry.cget("height")) != height:
            self.entry.configure(height=height)
        self.entry.see("insert")

    def toast(self, text, seconds=4):
        """Short confirmation shown in the footer instead of the answer area."""
        self.toast_text = text
        self.toast_until = time.time() + seconds

    def _set_compact(self, compact):
        self._compact = compact
        size = 8 if compact else 9
        for chip in self.chips.values():
            chip["frame"].configure(padx=4 if compact else 6)
            chip["box"].configure(font=(FONT, size))
            chip["name"].configure(font=(FONT, size))
        self.show_label.pack_forget()

    def _fit_chips(self, width=None):
        """If the four switches don't fit, hide 'Show' and use smaller switches."""
        try:
            self.root.update_idletasks()
            width = width or self.root.winfo_width()
            row = sum(c["border"].winfo_reqwidth() + 4 for c in self.chips.values())
            margin = 2 * 16 + 12
            if not self._compact:
                need = row + self.show_label.winfo_reqwidth() + 6 + margin
                if need > width:
                    self._set_compact(True)
            else:
                need_full = int(row * 1.25) + 50 + margin     # estimate at full size
                if need_full < width:
                    self._set_compact(False)
                    self.root.after(50, self._fit_chips)      # re-check at full size
        except Exception:
            pass

    def _on_resize(self, event):
        if event.widget is self.root:
            self._fit_chips(event.width)
            if getattr(self, "_last_size", None) != (event.width, event.height):
                self._last_size = (event.width, event.height)
                self.root.after(50, self._layout)
            if getattr(self, "_geo_job", None):
                self.root.after_cancel(self._geo_job)
            self._geo_job = self.root.after(800, self._remember_geometry)
            width = max(200, event.width - 32)
            for label in (self.tail, self.info_label, self.title_label):
                label.configure(wraplength=width - (40 if label is self.title_label else 0))

    def _set_answer(self, text, empty=False, label=""):
        """Show a status (e.g. 'Meeting ended...', the recap) above the
        conversation, or clear it (empty=True)."""
        self._notice = None if empty or not text else (label, text)
        self._render_feed(force=True)

    def _exchanges(self):
        """The conversation grouped as [{'q': (time, text) or None, 'a': [(time, text)]}],
        oldest first. A Claude message with no question before it gets q=None."""
        out = []
        for t, who, body in transcript.conversation():
            if who == "you":
                out.append({"q": (t, body), "a": []})
            else:
                if not out:
                    out.append({"q": None, "a": []})
                out[-1]["a"].append((t, body))
        return out

    def _render_feed(self, force=False):
        exchanges = self._exchanges()
        sig = (tuple((e["q"], tuple(e["a"])) for e in exchanges[-1:]), len(exchanges),
               self._notice, self._pending_hint)
        if not force and sig == self._feed_sig:
            return
        self._feed_sig = sig
        a = self.answer
        a.configure(state="normal")
        a.delete("1.0", "end")
        if self._notice:
            label, text = self._notice
            if label:
                a.insert("end", label + "\n", "notice_name")
            a.insert("end", text + "\n", "notice")
        for i, ex in enumerate(reversed(exchanges)):      # newest first
            if i or self._notice:
                a.insert("end", "\u2500" * 12 + "\n", "divider")
            if ex["q"]:
                t, text = ex["q"]
                a.insert("end", "You", "you_name")
                a.insert("end", f"  {t.strftime('%H:%M')}\n", "time")
                a.insert("end", text + "\n", "you")
            for t, text in ex["a"]:
                a.insert("end", "Claude", "claude_name")
                a.insert("end", f"  {t.strftime('%H:%M')}\n", "time")
                a.insert("end", text + "\n", "claude")
            if ex["q"] and not ex["a"]:
                a.insert("end", "Claude\n", "claude_name")
                a.insert("end", self._pending_hint + "\n", "hint")
        if a.get("end-2c", "end-1c") == "\n":
            a.delete("end-2c", "end-1c")      # no empty line at the very bottom
        a.configure(state="disabled")
        a.yview_moveto(0)                 # newest is on top
        self.root.after(30, self._layout)

    def _answer_lines(self):
        try:
            self.answer.update_idletasks()
            return int(self.answer.count("1.0", "end", "displaylines")[0])
        except Exception:
            return 3

    def _row_height(self, size=9, spacing=None):
        import tkinter.font as tkfont
        cache = getattr(self, "_row_cache", {})
        spacing = px(9) if spacing is None else spacing
        if (size, spacing) not in cache:
            cache[(size, spacing)] = tkfont.Font(family=FONT, size=size).metrics("linespace") + spacing
            self._row_cache = cache
        return cache[(size, spacing)]

    def _head_height(self, key):
        """Height of a list's title row and divider, measured on screen."""
        frame = self.panels[key]
        try:
            text = self.panel_text[key]
            return max(px(30), frame.winfo_reqheight() - text.winfo_reqheight()) + px(12)
        except Exception:
            return px(44)

    def _content_height(self, key, max_rows=None):
        """Height that shows every row of a list (measured with the real font,
        so it works with any Windows display scaling)."""
        text = self.panel_text[key]
        try:
            text.update_idletasks()
            rows = int(text.count("1.0", "end", "displaylines")[0])
            if text.get("end-2c", "end-1c") == "\n":
                rows -= 1                     # the empty line after the last item
        except Exception:
            rows = 3
        if key == "transcript":
            rows = 8                          # the transcript scrolls; show ~8 lines
        rows = max(1, rows)
        if max_rows:
            rows = min(rows, max_rows)
        return self._head_height(key) + rows * self._row_height() + px(10)

    def _answer_needed(self, total):
        return max(self._row_height(10, 8) * 2 + 40,
                   min(40 + self._answer_lines() * self._row_height(10, 7), int(total * 0.40)))

    def _layout(self):
        """Fit everything into the window.
        - No list open: the answer fills the window.
        - Lists open and they fit: each list is as tall as its content, the answer
          gets the rest.
        - Not enough room: the answer keeps what its text needs, lists share the rest
          (and scroll)."""
        try:
            if not self.visible:
                self.paned.paneconfigure(self.body, stretch="always")
                return
            self.paned.update_idletasks()
            total = max(300, self.paned.winfo_height())
            answer_needed = max(self._answer_needed(total), int(total * 0.34))
            wanted = {k: self._content_height(k) for k in self.visible}
            gaps = px(16) * len(self.visible)
            free = total - answer_needed - gaps
            if sum(wanted.values()) <= free:
                # everything fits: lists show all rows, the answer gets the rest
                for k in self.visible:
                    self.paned.paneconfigure(self.panels[k], stretch="never", height=wanted[k])
                self.paned.paneconfigure(self.body, stretch="always",
                                         height=total - sum(wanted.values()) - gaps)
            else:
                # not enough room: the answer keeps a third of the window; open
                # lists share the rest (at least two rows each) and scroll inside
                floor = {k: self._content_height(k, max_rows=2) for k in self.visible}
                if sum(floor.values()) > free:     # many lists, small window: equal shares
                    share = max(px(60), free // len(self.visible))
                    heights = {k: share for k in self.visible}
                else:
                    extra = free - sum(floor.values())
                    need_more = {k: wanted[k] - floor[k] for k in self.visible}
                    more_total = sum(need_more.values()) or 1
                    heights = {k: floor[k] + int(extra * need_more[k] / more_total)
                               for k in self.visible}
                self.paned.paneconfigure(self.body, stretch="never", height=answer_needed)
                for k in self.visible:
                    self.paned.paneconfigure(self.panels[k], stretch="always",
                                             height=heights[k])
        except Exception:
            pass

    # kept for the server's "suggestion" messages
    def _set_suggestion(self, text):
        self._set_answer(text)

    # ---- meeting info -----------------------------------------------------------
    def update_info(self):
        with transcript.lock:
            c = dict(transcript.context)
        title = c["title"] or c["subject"]
        if live.mode != "record":
            self.root.title(f"Sidenote {SIDENOTE_VERSION}" + (
                " - Past meetings" if getattr(self, "screen", None) == "meetings" else ""))
            return
        self.title_label.configure(text=title or "Untitled meeting",
                                   fg=FG if title else MUTED, cursor="hand2")
        # Version in the window title is a testing aid (remove before release)
        self.root.title(f"Sidenote {SIDENOTE_VERSION}" + (f" - {title}" if title else ""))

    # ---- the user's name ------------------------------------------------------------
    def _update_name_bar(self):
        """Ask for the user's name once: only while no name is known and the
        user hasn't answered or dismissed the question."""
        want = not profile.name and not profile.data["name_asked"]
        if want and not self._name_bar_shown:
            self.name_bar.pack(fill="x", padx=16, pady=(8, 0), after=self._divider)
        elif not want and self._name_bar_shown:
            self.name_bar.pack_forget()
        self._name_bar_shown = want

    def _name_save(self):
        name = self.name_entry.get().strip()
        if not name:
            self.toast("Type a name, or close this with ✕")
            return
        set_user_name(name, "typed")
        profile.mark_asked()
        self._update_name_bar()
        self.toast(f"Sidenote will call you {profile.name}")

    def _name_later(self):
        profile.mark_asked()          # asked once: don't ask again (editable in Meeting info)
        self._update_name_bar()
        self.toast("You can add your name later in ⋯ > Meeting info")

    MENU_GLYPHS = {"info": "", "captions": "", "folder": "", "new": ""}

    def open_menu(self, event=None):
        """The ⋯ menu: a small dark panel under the button (not the system menu)."""
        if getattr(self, "_menu_win", None) is not None:
            self._close_menu()
            return
        recording = live.mode == "record" and not transcript.ended_at
        meeting = live.mode == "record"
        items = [
            ("info", "Meeting info", self.edit_info, meeting),
            ("captions", "Show Live Captions" if captions_win.hide_wanted else "Hide Live Captions",
             self.toggle_captions, recording),
            ("folder", "Open meetings folder", self.open_folder, True),
            None,
            ("new", "New meeting", self.new_meeting, True),
        ]
        win = tk.Toplevel(self.root)
        win.wm_overrideredirect(True)
        win.attributes("-topmost", True)
        win.configure(bg=LINE)
        panel = tk.Frame(win, bg=SURFACE, padx=px(6), pady=px(6))
        panel.pack(padx=1, pady=1)
        glyph_font = IconTab._glyph("plus")
        for item in items:
            if item is None:
                tk.Frame(panel, bg=LINE, height=1).pack(fill="x", pady=px(5), padx=px(6))
                continue
            key, label, command, enabled = item
            row = tk.Frame(panel, bg=SURFACE, padx=px(10), pady=px(7),
                           cursor="hand2" if enabled else "")
            row.pack(fill="x")
            parts = [row]
            fg = FG if enabled else FAINT
            if glyph_font:
                ic = tk.Label(row, text=self.MENU_GLYPHS[key], bg=SURFACE, fg=MUTED if enabled else FAINT,
                              font=(glyph_font[0][0], 10), width=2, anchor="w")
                ic.pack(side="left", padx=(0, px(8)))
                parts.append(ic)
            lab = tk.Label(row, text=label, bg=SURFACE, fg=fg, font=(FONT, 10), anchor="w")
            lab.pack(side="left", fill="x", expand=True)
            parts.append(lab)
            if not enabled:
                continue
            for w in parts:
                w.bind("<Enter>", lambda e, ps=parts: [p.configure(bg=SURFACE_HI) for p in ps])
                w.bind("<Leave>", lambda e, ps=parts: [p.configure(bg=SURFACE) for p in ps])
                w.bind("<ButtonRelease-1>", lambda e, c=command: (self._close_menu(), c()))
        win.update_idletasks()
        x = self.menu_btn.winfo_rootx() + self.menu_btn.winfo_width() - win.winfo_reqwidth()
        y = self.menu_btn.winfo_rooty() + self.menu_btn.winfo_height() + px(4)
        win.geometry(f"+{max(0, x)}+{y}")
        self._menu_win = win
        win.bind("<Escape>", lambda e: self._close_menu())
        win.bind("<Button-1>", self._menu_click)
        win.grab_set()                               # a click anywhere else closes it
        win.focus_force()

    def _menu_click(self, event):
        win = self._menu_win
        if win is None:
            return
        x, y = event.x_root, event.y_root
        inside = (win.winfo_rootx() <= x < win.winfo_rootx() + win.winfo_width()
                  and win.winfo_rooty() <= y < win.winfo_rooty() + win.winfo_height())
        if not inside:
            self._close_menu()

    def _close_menu(self):
        win = getattr(self, "_menu_win", None)
        self._menu_win = None
        self._menu_closed_at = time.time()
        if win is not None:
            try:
                win.grab_release()
                win.destroy()
            except Exception:
                pass

    def _edit_info_from_click(self):
        # A click outside the open menu closes it; don't let that same click
        # also open Meeting info.
        if time.time() - getattr(self, "_menu_closed_at", 0) < 0.6:
            return
        self.edit_info()

    def open_folder(self):
        try:
            os.makedirs(SAVE_DIR, exist_ok=True)
            if IS_MAC:
                import subprocess
                subprocess.Popen(["open", SAVE_DIR])
            else:
                os.startfile(SAVE_DIR)
        except Exception as e:
            self.toast(f"Could not open folder: {e}")

    def edit_info(self):
        """Form to set the meeting title, role, goals, participants and agenda."""
        with transcript.lock:
            c = dict(transcript.context)
        win = tk.Toplevel(self.root)
        win.title("Meeting info")
        win.configure(bg=BG)
        win.attributes("-topmost", True)
        win.transient(self.root)
        win.geometry(f"+{self.root.winfo_x() + 24}+{self.root.winfo_y() + 70}")
        win.resizable(True, False)
        try:
            win.iconphoto(False, *self._icons)
        except Exception:
            pass
        fields = {}
        tk.Label(win, text="Meeting info", bg=BG, fg=FG, font=(FONT, 12, "bold"),
                 anchor="w").pack(fill="x", padx=18, pady=(16, 0))
        tk.Label(win, text="Claude uses this for every answer. Anything left empty stays "
                 "empty in the meeting file.", bg=BG, fg=MUTED, font=(FONT, 8), anchor="w",
                 justify="left", wraplength=380).pack(fill="x", padx=18, pady=(2, 6))

        def row(label, key, value, multiline=False):
            tk.Label(win, text=label, bg=BG, fg=MUTED, font=(FONT, 9),
                     anchor="w").pack(fill="x", padx=18, pady=(8, 3))
            frame = tk.Frame(win, bg=SURFACE, highlightthickness=1,
                             highlightbackground=LINE, highlightcolor=ACCENT)
            frame.pack(fill="x", padx=18)
            if multiline:
                box = tk.Text(frame, height=5, width=44, bg=SURFACE, fg=FG,
                              insertbackground=FG, relief="flat", font=(FONT, 10),
                              wrap="word", borderwidth=0, padx=8, pady=6,
                              highlightthickness=0)
                box.insert("1.0", value)
                box.pack(fill="x")
            else:
                box = tk.Entry(frame, width=44, bg=SURFACE, fg=FG, insertbackground=FG,
                               relief="flat", font=(FONT, 10), borderwidth=0,
                               highlightthickness=0)
                box.insert(0, value)
                box.pack(fill="x", padx=8, ipady=6)
            fields[key] = box

        row("Meeting title", "title", c["title"])
        row("My name  (used instead of “You”, kept for next meetings)", "name",
            profile.name)
        row("My role  (kept for next meetings)", "role", c["role"])
        row("My goals", "goals", c["goals"])
        row("Participants  (comma separated)", "participants", ", ".join(c["participants"]))
        row("Agenda  (one item per line)", "agenda", "\n".join(c["agenda"]), multiline=True)

        def save(_e=None):
            def get(k):
                box = fields[k]
                return (box.get("1.0", "end") if isinstance(box, tk.Text) else box.get()).strip()
            with transcript.lock:
                cc = transcript.context
                cc["title"] = get("title")
                cc["role"] = get("role")
                cc["goals"] = get("goals")
                cc["participants"] = parse_list(get("participants"))
                cc["agenda"] = parse_list(get("agenda"), commas=False) if get("agenda") else []
                cc["agenda_done"] = [a for a in cc["agenda_done"] if a in cc["agenda"]]
            profile.set_role(get("role"))         # an empty field clears the saved role
            if get("name") != profile.name:
                set_user_name(get("name"), "typed")
                profile.mark_asked()
                self._update_name_bar()
            transcript.save_now()
            self.update_info()
            self.refresh_lists()
            if not self.answer.get("1.0", "end").strip() or self._answer_is_empty_state():
                self._set_answer("", empty=True)
            self.toast("Meeting info saved")
            win.destroy()

        buttons = tk.Frame(win, bg=BG)
        buttons.pack(fill="x", padx=18, pady=16)
        save_btn = tk.Label(buttons, text="Save", bg=ACCENT, fg="#ffffff", font=(FONT, 9, "bold"),
                            padx=18, pady=6, cursor="hand2")
        save_btn.pack(side="right")
        save_btn.bind("<Button-1>", save)
        self._hover(save_btn, ACCENT, ACCENT_HI)
        cancel = tk.Label(buttons, text="Cancel", bg=BG, fg=MUTED, font=(FONT, 9),
                          padx=12, pady=6, cursor="hand2")
        cancel.pack(side="right", padx=(0, 6))
        cancel.bind("<Button-1>", lambda e: win.destroy())
        self._hover(cancel, BG, SURFACE, fg_on=FG, fg_off=MUTED)
        win.bind("<Escape>", lambda e: win.destroy())
        fields["title"].focus_set()

    def _answer_is_empty_state(self):
        return not self._notice and not transcript.conversation()

    def handle_local_command(self, text):
        """'agenda: X', 'role: X', 'title: X', 'participants: X' are saved directly."""
        m = LOCAL_COMMAND.match(text)
        if not m:
            return False
        key, value = m.group(1).lower(), m.group(2).strip()
        if key in ("todo", "action"):
            transcript.add_action(value)
            self.refresh_lists(flash="actions")
            msg = "Action item saved"
        elif key in ("ask", "q"):
            transcript.add_question(value)
            self.refresh_lists(flash="questions")
            msg = "Question saved to To ask"
        elif key == "agenda":
            added = transcript.add_agenda_items(value)
            self.refresh_lists(flash="agenda" if added else None)
            msg = ("Added to agenda: " + ", ".join(added)) if added else "Already on the agenda"
        elif key in ("participant", "participants", "people"):
            added = transcript.add_participants(value)
            msg = "Added: " + ", ".join(added)
        elif key in ("name", "my name"):
            set_user_name(value, "typed")
            profile.mark_asked()
            self._update_name_bar()
            msg = f"Sidenote will call you {profile.name}"
        else:
            field = {"my role": "role", "goal": "goals"}.get(key, key)
            transcript.update_context(**{field: value})
            msg = f"{field.capitalize()} saved"
        self.update_info()
        if self._answer_is_empty_state():
            self._set_answer("", empty=True)
        self.toast(msg)
        return True

    # ---- actions ------------------------------------------------------------------
    def send(self, _event=None):
        if self._placeholder_on:
            return
        text = self._input_text().strip()
        if not text:
            return
        self.entry.delete("1.0", "end")
        self.entry.configure(height=1)
        self._update_suggestions()
        if self.handle_local_command(text):
            return
        self._ask(text, text, "Thinking\u2026")

    def _ask(self, shown, token, working):
        """Put the question in the conversation right away (newest on top) and
        hand it to Claude. working: shown under it until Claude replies."""
        transcript.add_note("YOU ASKED", shown)
        question_queue.put(token)
        if live.waiting or live.label().startswith("Claude"):
            self._pending_hint = working
        else:
            self._pending_hint = ("Saved. Claude will answer as soon as Sidenote is connected "
                                  "(type 'continue' in the Claude app if it stays paused).")
        self._set_answer("", empty=True)      # a new question clears old status notes

    def what_did_i_miss(self, _event=None):
        if transcript.ended_at:
            self.toast("This meeting has already ended")
            return
        if not transcript.since(MISSED_MINUTES):
            self.toast(f"Nothing captured in the last {MISSED_MINUTES} minutes")
            return
        self._ask("What did I miss?", MISSED_TOKEN, "Catching you up\u2026")

    def new_meeting(self):
        from tkinter import messagebox
        if live.mode == "record" and not transcript.ended_at and transcript.count_lines() and \
                not messagebox.askyesno(
                    "New meeting",
                    "Start a new meeting?\n\nThe current meeting is saved, then the transcript "
                    "and meeting info are cleared.", parent=self.root):
            return
        self.start_recording()

    def _reset_view(self, message):
        self.end_btn.configure(text="End meeting", fg=MUTED, cursor="hand2")
        self._hover(self.end_btn, BG, SURFACE, fg_on=FG, fg_off=MUTED)
        self.update_info()
        self.refresh_lists()
        self._set_answer("", empty=True)
        self.toast(message, seconds=8)

    def on_close(self):
        """X ends the meeting (after a confirmation if a meeting is in progress)."""
        count, _ = transcript.stats()
        if count and not transcript.ended_at:
            from tkinter import messagebox
            if not messagebox.askyesno(
                    "End meeting and close",
                    "Close Sidenote and end the meeting?\n\nEverything is saved in the "
                    "meeting file, and Claude writes the recap.\n\nTip: to step away "
                    "without ending, minimize the window instead.", parent=self.root):
                return
            transcript.end_meeting()
        self.root.destroy()

    def end_meeting(self, _e=None):
        if transcript.ended_at:
            self.toast("This meeting has already ended")
            return
        from tkinter import messagebox
        if not messagebox.askyesno(
                "End meeting",
                "End the meeting?\n\nSidenote stops recording, Claude writes a quick recap, "
                "and everything is saved in the meeting file.", parent=self.root):
            return
        transcript.end_meeting()
        self.end_btn.configure(text="New meeting", fg=MUTED, cursor="hand2")
        connected = live.waiting or live.label().startswith("Claude")
        if connected:
            question_queue.put(END_TOKEN)
            self._set_answer("Meeting ended. Claude is writing the recap...")
        else:
            self._set_answer("Meeting ended and saved.\n\nClaude isn't connected right now, "
                             "so there's no recap yet. Type 'recap the meeting' in the "
                             "Claude app to add one.")

    # ---- tabs: ＋ (new / current meeting) and past meetings --------------------------
    MEETINGS_MIN_WIDTH = 760      # the past-meetings tab needs room for the side list

    def _build_tabs(self):
        bar = tk.Frame(self.root, bg=BG)
        bar.pack(side="top", fill="x", padx=12, pady=(10, 0))
        self.tab_live = IconTab(bar, "plus", "New meeting", lambda: self.select_tab("live"))
        self.tab_live.pack(side="left")
        self.tab_past = IconTab(bar, "history", "Past meetings",
                                lambda: self.select_tab("meetings"))
        self.tab_past.pack(side="left", padx=(4, 0))
        self.menu_btn = tk.Label(bar, text="⋯", bg=BG, fg=MUTED, cursor="hand2",
                                 font=(FONT, 15), padx=6)
        self.menu_btn.pack(side="right")
        self.menu_btn.bind("<Button-1>", self.open_menu)
        self._hover(self.menu_btn, BG, SURFACE, fg_on=FG, fg_off=MUTED)
        # End meeting (dark red) while recording; New meeting after it ended
        self.top_btn = Pill(bar, "", fg="#ffffff", bg=END_RED, size=9, height=28,
                            command=self._top_btn_click)
        self.top_btn.bind("<Enter>", lambda e: self._sync_top_btn(hover=True))
        self.top_btn.bind("<Leave>", lambda e: self._sync_top_btn(hover=False))
        self._top_state = None
        self.tab_bar = bar

    def _top_btn_click(self):
        if live.mode == "record" and not transcript.ended_at:
            self.end_meeting()
        elif live.mode == "record":
            self.start_recording()

    def _sync_top_btn(self, hover=False):
        if live.mode == "record" and not transcript.ended_at:
            state = ("End meeting", "#ffffff", END_RED_HI if hover else END_RED)
        elif live.mode == "record" and self.screen == "live":
            state = ("New meeting", FG, SURFACE_HI if hover else SURFACE)
        else:
            state = None
        if state == self._top_state:
            return
        self._top_state = state
        if state is None:
            self.top_btn.pack_forget()
            return
        self.top_btn.set(*state)
        if not self.top_btn.winfo_ismapped():
            self.top_btn.pack(side="right", padx=(0, px(8)))

    def select_tab(self, name):
        """'live' (the ＋ tab) or 'meetings'. Recording goes on in the background."""
        recording = live.mode == "record"
        for frame in (self.rec, self.start, self.hist):
            frame.pack_forget()
        if name == "live":
            (self.rec if recording else self.start).pack(fill="both", expand=True)
            if not recording:
                live.mode = "home"
        else:
            self.hist.pack(fill="both", expand=True)
            if not recording:
                live.mode = "history"
        prev = getattr(self, "screen", None)
        self.screen = name
        self.tab_live.set(selected=name == "live")
        self.tab_past.set(selected=name == "meetings")
        live.last_activity = time.time()
        if name == "meetings":
            self._widen()
            self.history_render(reload=True)
        elif prev == "meetings":
            self._narrow()
        self.update_info()

    def _widen(self):
        self.root.update_idletasks()
        w, h = self.root.winfo_width(), self.root.winfo_height()
        if w >= px(self.MEETINGS_MIN_WIDTH):
            self._narrow_to = None
            return
        x, y = self.root.winfo_x(), self.root.winfo_y()
        new_w = px(self.MEETINGS_MIN_WIDTH)
        x = max(0, min(x, self.root.winfo_screenwidth() - new_w - 10))
        self._narrow_to = (w, self.root.winfo_x())
        self.root.geometry(f"{new_w}x{h}+{x}+{y}")

    def _narrow(self):
        back = getattr(self, "_narrow_to", None)
        self._narrow_to = None
        if not back:
            return
        self.root.update_idletasks()
        if abs(self.root.winfo_width() - px(self.MEETINGS_MIN_WIDTH)) > px(4):
            return                                   # the user resized it: leave it
        w, x = back
        self.root.geometry(f"{w}x{self.root.winfo_height()}+{x}+{self.root.winfo_y()}")

    # ---- ＋ tab when nothing is recording -------------------------------------------
    def _build_start(self):
        self.start = tk.Frame(self.root, bg=BG)
        inner = tk.Frame(self.start, bg=BG)
        inner.place(relx=0.5, rely=0.42, anchor="center", relwidth=0.86)
        tk.Label(inner, text="New meeting", bg=BG, fg=FG, font=(SERIF, 22),
                 anchor="w").pack(fill="x")
        self.start_sub = tk.Label(
            inner, text="Sidenote reads your call's captions, keeps the agenda and action "
                        "items, and answers your questions.", bg=BG, fg=MUTED, font=(FONT, 10),
            anchor="w", justify="left", wraplength=px(330))
        self.start_sub.pack(fill="x", pady=(6, 22))
        btn = Pill(inner, "●  Start meeting", fg="#ffffff", bg=ACCENT, size=11,
                   height=40, command=self.start_recording)
        btn.pack(anchor="w")
        btn.bind("<Enter>", lambda e: btn.set("●  Start meeting", "#ffffff", ACCENT_HI))
        btn.bind("<Leave>", lambda e: btn.set("●  Start meeting", "#ffffff", ACCENT))
        tk.Label(inner, text="Works with Google Meet, Zoom (browser), Microsoft Teams and "
                             "Live Captions.", bg=BG, fg=FAINT, font=(FONT, 8), anchor="w",
                 justify="left", wraplength=px(330)).pack(fill="x", pady=(14, 0))
        self.start_offline = tk.Label(inner, text="Claude is not connected \u00b7 type "
                                                  "\u201copen Sidenote\u201d in a Claude chat",
                                      bg=BG, fg=FAINT, font=(FONT, 9), anchor="w", justify="left",
                                      wraplength=px(330))
        self._start_offline_shown = False

    def start_recording(self, info=None):
        """Start a meeting (＋ tab, the menu, or Claude when the user asked)."""
        if self._h_waiting:                          # a past-meetings question is pending
            live.answer_target = "dropped"
            self._h_waiting = False
            self._h_chat.append(("note", "A meeting started: that question was cancelled."))
            self._h_render_chat()
        kept = []
        while True:                                  # drop past-meetings questions not taken
            try:
                item = question_queue.get_nowait()
            except queue.Empty:
                break
            if not isinstance(item, dict):
                kept.append(item)
        for item in kept:
            question_queue.put(item)
        transcript.new_meeting()
        info = dict(live.pending_info, **(info or {}))
        live.pending_info = {}
        if info:
            core_update_meeting_info(**info)
        live.mode = "record"
        live.record_on_open = False
        live.last_activity = time.time()
        captions_win.hide_wanted = True
        try:
            captions_win.ensure_running()            # Live Captions only while recording
        except Exception as e:
            log.info("Could not start Live Captions: %s", e)
        self.select_tab("live")
        self._reset_view("Meeting started")

    def _end_btn_click(self, _e=None):
        if transcript.ended_at:
            self.start_recording()                   # after a meeting: start the next one
        else:
            self.end_meeting()

    @staticmethod
    def claude_connected():
        return not live.released and (live.waiting or (
            live.last_seen and time.time() - live.last_seen < PAUSED_AFTER_SECONDS))

    def _copy_open_line(self, _e=None):
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append("open Sidenote")
            self.toast("Copied “open Sidenote”: paste it into a Claude chat")
        except Exception:
            pass

    def _offline_row(self, parent, bg=BG):
        """'Claude isn't connected' + one click to copy 'open Sidenote'."""
        row = tk.Frame(parent, bg=bg)
        tk.Label(row, text="Claude isn't connected ·", bg=bg, fg=WARN,
                 font=(FONT, 9)).pack(side="left")
        copy = tk.Label(row, text="Copy “open Sidenote”", bg=bg, fg=ACCENT_HI,
                        font=(FONT, 9, "underline"), cursor="hand2")
        copy.pack(side="left", padx=(6, 0))
        copy.bind("<Button-1>", self._copy_open_line)
        Tooltip(copy, "Paste it into a Claude chat to connect")
        return row

    # ---- past meetings: list on the left, the meeting in the center ----------------------
    def _build_history(self):
        self.hist = tk.Frame(self.root, bg=BG)
        side = tk.Frame(self.hist, bg=BG, width=px(240))
        side.pack(side="left", fill="y", padx=(px(10), 0), pady=(px(8), 0))
        side.pack_propagate(False)
        self.h_list = tk.Text(side, wrap="none", bg=BG, fg=FG, relief="flat", font=(FONT, 9),
                              padx=px(4), pady=px(2), borderwidth=0, highlightthickness=0,
                              cursor="arrow")
        self.h_list.pack(fill="both", expand=True)
        L = self.h_list
        L.tag_configure("group", foreground=FAINT, font=(FONT, 8, "bold"), lmargin1=px(10),
                        spacing1=px(26), spacing3=px(8))
        L.tag_configure("row_title", foreground=FG, font=(FONT, 9, "bold"), lmargin1=px(10),
                        spacing1=px(7))
        L.tag_configure("row_meta", foreground=FAINT, font=(FONT, 8), lmargin1=px(10),
                        spacing1=px(2), spacing3=px(7))
        L.tag_configure("hover", background=SURFACE)
        L.tag_configure("picked", background=SURFACE_HI)      # the meeting shown in the center
        L.tag_raise("picked")
        L.configure(state="disabled")
        tk.Frame(self.hist, bg=LINE, width=1).pack(side="left", fill="y", padx=(px(6), 0),
                                                   pady=(px(8), 0))

        main = tk.Frame(self.hist, bg=BG)
        main.pack(side="left", fill="both", expand=True, padx=(px(22), px(16)), pady=(px(8), 0))
        self.h_main = main
        # the ask box is always at the bottom
        ask = tk.Frame(main, bg=BG)
        ask.pack(side="bottom", fill="x", pady=(px(8), 0))
        self.h_pill = InputPill(ask, self.history_ask)
        self.h_pill.pack(fill="x")
        self.h_entry = tk.Entry(self.h_pill, bg=SURFACE, fg=FG, insertbackground=FG,
                                relief="flat", font=(FONT, 10), borderwidth=0, highlightthickness=0,
                                disabledbackground=SURFACE, disabledforeground=FAINT)
        self.h_pill.hold(self.h_entry)
        self.h_entry.bind("<Return>", lambda e: self.history_ask())
        self.h_entry.bind("<FocusIn>", lambda e: self._h_placeholder(False))
        self.h_entry.bind("<FocusOut>", lambda e: self._h_placeholder(True))
        self._h_ph_on = False
        self._h_offline = False
        # the meeting (top) and the conversation with Claude (bottom, when there is one)
        self.h_paned = tk.PanedWindow(main, orient="vertical", bg=BG, bd=0, sashwidth=px(10),
                                      sashrelief="flat", showhandle=False, opaqueresize=True)
        self.h_paned.pack(fill="both", expand=True)
        self.h_text = tk.Text(self.h_paned, wrap="word", bg=BG, fg=FG, relief="flat",
                              font=(FONT, 10), padx=px(6), pady=px(4), borderwidth=0,
                              highlightthickness=0, cursor="arrow", spacing1=px(3),
                              spacing2=px(3), spacing3=px(3))
        self.h_paned.add(self.h_text, stretch="always", minsize=px(120))
        t = self.h_text
        t.tag_configure("big", font=(SERIF, 19), foreground=FG, spacing3=px(10))
        t.tag_configure("meta", foreground=FAINT, font=(FONT, 8))
        t.tag_configure("people", foreground=FAINT, font=(FONT, 8), spacing1=px(8))
        t.tag_configure("muted", foreground=MUTED)
        t.tag_configure("section", foreground=MUTED, font=(FONT, 9, "bold"), spacing1=px(24),
                        spacing3=px(8))
        t.tag_configure("item", lmargin1=px(4), lmargin2=px(28), spacing1=px(4), spacing3=px(4))
        t.tag_configure("bullet", lmargin1=px(4), lmargin2=px(20), spacing1=px(3), spacing3=px(3))
        t.tag_configure("meta_line", lmargin1=px(30), lmargin2=px(30), spacing3=px(6))
        t.tag_configure("dec_meeting", foreground=ACCENT_HI, font=(FONT, 9, "bold"),
                        spacing1=px(12), lmargin1=px(4))
        t.tag_configure("dec_date", spacing1=px(12))
        t.tag_configure("dec_item", lmargin1=px(14), lmargin2=px(30))
        t.tag_configure("link", foreground=ACCENT_HI)
        t.tag_configure("check", foreground=OK)
        t.tag_configure("box", foreground=MUTED)
        t.tag_configure("done", foreground=FAINT, overstrike=True)
        t.tag_configure("claude_badge", foreground=ACCENT_HI, font=(FONT, 8))
        t.tag_configure("hover", background=SURFACE)
        t.tag_configure("faint", foreground=FAINT)
        t.configure(state="disabled")
        # the conversation panel
        self.h_chat = tk.Frame(self.h_paned, bg=BG)
        tk.Frame(self.h_chat, bg=LINE, height=1).pack(fill="x")
        head = tk.Frame(self.h_chat, bg=BG)
        head.pack(fill="x", pady=(px(8), px(2)))
        tk.Label(head, text="Conversation", bg=BG, fg=MUTED, font=(FONT, 9, "bold")).pack(side="left")
        clear = tk.Label(head, text="Clear", bg=BG, fg=FAINT, font=(FONT, 8), cursor="hand2")
        clear.pack(side="right")
        clear.bind("<Button-1>", lambda e: self._h_clear_chat())
        self._hover(clear, BG, BG, fg_on=FG, fg_off=FAINT)
        self.h_chat_text = tk.Text(self.h_chat, wrap="word", bg=BG, fg=FG, relief="flat",
                                   font=(FONT, 10), padx=px(6), pady=px(4), borderwidth=0,
                                   highlightthickness=0, cursor="arrow", spacing2=px(3))
        self.h_chat_text.pack(fill="both", expand=True)
        c = self.h_chat_text
        c.tag_configure("you_name", foreground=MUTED, font=(FONT, 8, "bold"), spacing1=px(14))
        c.tag_configure("you", foreground=FG, font=(FONT, 10, "bold"), spacing3=px(4))
        c.tag_configure("claude_name", foreground=ACCENT, font=(FONT, 8, "bold"), spacing1=px(10))
        c.tag_configure("claude", foreground=FG, spacing3=px(4))
        c.tag_configure("hint", foreground=FAINT, spacing1=px(10))
        c.tag_configure("note", foreground=WARN, spacing1=px(10))
        self._h_chat_shown = False
        self.h_selected = None           # meeting id shown in the center (None = All meetings)
        self.h_range = "all"             # All meetings filter: all, day, 7, 30
        self.h_all_expanded = False      # show all action items, not just ten
        self.h_show_transcript = False
        self._h_chat = []                # [(who, text)] who: you, claude, note
        self._h_waiting = False
        self._h_entries = []
        self._h_pills = []
        self._h_placeholder(True)

    def _h_placeholder(self, on):
        """Placeholder in the ask box (or 'Claude is not connected', box disabled)."""
        e = self.h_entry
        if self._h_offline:
            e.configure(state="normal")
            e.delete(0, "end")
            e.insert(0, "Claude is not connected")
            e.configure(state="disabled")
            self._h_ph_on = True
            return
        text = "Ask about this meeting" if self.h_selected else "Ask about all your meetings"
        if on and (self._h_ph_on or not e.get().strip()):
            e.delete(0, "end")
            e.insert(0, text)
            e.configure(fg=FAINT)
            self._h_ph_on = True
        elif not on and self._h_ph_on:
            e.delete(0, "end")
            e.configure(fg=FG)
            self._h_ph_on = False

    def _h_set_offline(self, offline):
        """Claude not connected: the box says so and the send button is greyed out."""
        if offline == self._h_offline:
            return
        self._h_offline = offline
        self.h_pill.set_enabled(not offline)
        if not offline:
            self.h_entry.configure(state="normal")
            self.h_entry.delete(0, "end")
            self._h_ph_on = False
            if self.root.focus_get() is not self.h_entry:
                self._h_placeholder(True)
            else:
                self.h_entry.configure(fg=FG)
        else:
            self._h_placeholder(True)

    def history_render(self, reload=False):
        if reload or not self._h_entries:
            try:
                self._h_entries = history_index()
            except Exception as e:
                log.info("Past meetings not readable: %s", e)
                self._h_entries = []
        if self.h_selected and not any(e["id"] == self.h_selected for e in self._h_entries):
            self.h_selected = None
        self._h_render_list()
        if self.h_selected:
            self._h_render_detail()
        else:
            self._h_render_all()
        if self._h_ph_on:
            self._h_ph_on = False
            self.h_entry.delete(0, "end")
            self._h_placeholder(True)
        self._h_render_chat()

    def _h_bind_row(self, widget, tag, command):
        widget.tag_bind(tag, "<Button-1>", lambda e: command())
        widget.tag_bind(tag, "<Enter>", lambda e, g=tag: (
            widget.configure(cursor="hand2"), widget.tag_add("hover", f"{g}.first", f"{g}.last")))
        widget.tag_bind(tag, "<Leave>", lambda e: (
            widget.configure(cursor="arrow"), widget.tag_remove("hover", "1.0", "end")))

    @staticmethod
    def _group_of(e):
        try:
            d = datetime.date.fromisoformat(e["date"])
        except Exception:
            return "Earlier"
        days = (datetime.date.today() - d).days
        return ("Today" if days <= 0 else "Yesterday" if days == 1 else
                "This week" if days < 7 else "This month" if days < 31 else "Earlier")

    def _h_render_list(self):
        L = self.h_list
        top = L.yview()[0]
        L.configure(state="normal")
        L.delete("1.0", "end")
        L.insert("end", "All meetings\n", ("row_title", "all"))
        L.insert("end", f"{len(self._h_entries)} meetings\n", ("row_meta", "all"))
        self._h_bind_row(L, "all", lambda: self.history_open(None))
        if self.h_selected is None:
            L.tag_add("picked", "all.first", "all.last")
        group = None
        for i, e in enumerate(self._h_entries):
            g = self._group_of(e)
            if g != group:
                L.insert("end", g.upper() + "\n", "group")
                group = g
            tag = f"m{i}"
            title = e["title"] if len(e["title"]) <= 30 else e["title"][:29] + "…"
            L.insert("end", title + "\n", ("row_title", tag))
            when = e["start"] if g in ("Today", "Yesterday") else f"{_day_label(e).rsplit(' ', 1)[0]}"
            L.insert("end", when + "\n", ("row_meta", tag))
            self._h_bind_row(L, tag, lambda m=e["id"]: self.history_open(m))
            if e["id"] == self.h_selected:
                L.tag_add("picked", f"{tag}.first", f"{tag}.last")
        if not self._h_entries:
            L.insert("end", "\nNo meetings yet.\nStart one with ＋", "row_meta")
        L.configure(state="disabled")
        L.yview_moveto(top)

    def history_open(self, meeting_id):
        self.h_selected = meeting_id
        self.h_show_transcript = False
        self.history_render()
        self.h_text.yview_moveto(0)

    def _h_clear(self):
        for p in self._h_pills:
            p.destroy()
        self._h_pills = []
        t = self.h_text
        t.configure(state="normal")
        t.delete("1.0", "end")

    def _h_pill(self, text):
        p = Pill(self.h_text, text, fg=MUTED, bg=SURFACE, parent_bg=BG, size=8)
        self._h_pills.append(p)
        self.h_text.window_create("end", window=p, padx=2)

    def _h_action_row(self, a, meeting_id, source=None):
        t = self.h_text
        tag = f"act_{meeting_id}_{a['id']}"
        done = a.get("status") == "done"
        t.insert("end", "☑  " if done else "☐  ", ("check" if done else "box", "item", tag))
        t.insert("end", a["text"], ("done", "item", tag) if done else ("item", tag))
        meta = " · ".join(x for x in (a.get("owner") or "owner ?",
                                           f"due {a['due']}" if a.get("due") else "",
                                           source or "") if x)
        if source:                                   # All meetings: details on their own line
            t.insert("end", "\n")
            t.insert("end", meta, ("meta", "meta_line", tag))
        else:
            t.insert("end", f"   {meta}", ("meta", tag))
        if done and a.get("closed_by") == "claude":
            t.insert("end", "   closed by Claude · ", "claude_badge")
            t.insert("end", "undo", ("link", tag + "_undo"))
            self._h_bind_row(t, tag + "_undo", lambda: self._h_set_action(meeting_id, a["id"], "open"))
        t.insert("end", "\n", ("item",))
        self._h_bind_row(t, tag, lambda: self._h_set_action(
            meeting_id, a["id"], "open" if done else "done"))

    ALL_RANGES = (("all", "All"), ("day", "Last day"), ("7", "Last 7 days"), ("30", "Last 30 days"))
    ALL_ITEMS_SHOWN = 10

    def _h_set_range(self, key):
        self.h_range = key
        self.h_all_expanded = False
        self._h_render_all()

    def _h_toggle_more(self):
        self.h_all_expanded = not self.h_all_expanded
        top = self.h_text.yview()[0]
        self._h_render_all()
        self.h_text.yview_moveto(top)

    def _h_filter_row(self):
        """All · Last day · Last 7 days · Last 30 days (embedded under the title)."""
        row = tk.Frame(self.h_text, bg=BG)
        for key, label in self.ALL_RANGES:
            on = key == self.h_range
            p = Pill(row, label, fg=FG if on else MUTED, bg=SURFACE_HI if on else BG,
                     parent_bg=BG, size=9, height=26, command=lambda k=key: self._h_set_range(k))
            p.pack(side="left", padx=(0, px(4)))
        self._h_pills.append(row)
        self.h_text.window_create("end", window=row)

    def _h_render_all(self):
        """All meetings: open action items on top, done ones struck below them
        (first ten, then 'Show more'), then recent decisions. Filter by date."""
        self._h_clear()
        t = self.h_text
        today = datetime.date.today()
        days = {"day": 1, "7": 7, "30": 30}.get(self.h_range)
        since = (today - datetime.timedelta(days=days)).isoformat() if days else ""
        entries = [e for e in self._h_entries if not since or e["date"] >= since]
        t.insert("end", "All meetings\n", "big")
        self._h_filter_row()
        t.insert("end", "\n")
        open_items = [(a, e) for e in entries for a in e["action_items"]
                      if a.get("status") != "done"]
        done_items = [(a, e) for e in entries for a in e["action_items"]
                      if a.get("status") == "done"]
        done_items.sort(key=lambda x: x[0].get("closed_at") or "", reverse=True)
        t.insert("end", "Action items\n", "section")
        meta = f"{len(open_items)} open · {len(done_items)} done · {len(entries)} meetings"
        t.insert("end", meta + "\n", ("meta", "meta_line0"))
        items = open_items + done_items
        if not items:
            t.insert("end", "No action items in this period.\n", "faint")
        shown = items if self.h_all_expanded else items[:self.ALL_ITEMS_SHOWN]
        for a, e in shown:
            self._h_action_row(a, e["id"], source=f"{e['title']}, {fmt_day_iso(e['date'])}")
        if len(items) > self.ALL_ITEMS_SHOWN:
            label = ("Show less" if self.h_all_expanded
                     else f"Show {len(items) - self.ALL_ITEMS_SHOWN} more")
            t.insert("end", label + "\n", ("link", "more", "item"))
            self._h_bind_row(t, "more", self._h_toggle_more)
        decisions = [(x, e) for e in entries for x in e["decisions"]][:10]
        if decisions:
            t.insert("end", "Recent decisions\n", "section")
            last = None
            for i, (x, e) in enumerate(decisions):
                if e["id"] != last:                  # the meeting first (click to open it)
                    tag = f"dsrc{i}"
                    t.insert("end", e["title"], ("dec_meeting", tag))
                    t.insert("end", f"   {fmt_day_iso(e['date'])}\n", ("meta", "dec_date"))
                    self._h_bind_row(t, tag, lambda m=e["id"]: self.history_open(m))
                    last = e["id"]
                t.insert("end", "•  " + x["text"] + "\n", ("bullet", "dec_item"))
        t.configure(state="disabled")

    def _h_render_detail(self):
        e = next((x for x in self._h_entries if x["id"] == self.h_selected), None)
        self._h_clear()
        t = self.h_text
        try:
            d = load_meeting(e["path"])
        except Exception as ex:
            t.insert("end", f"Could not read this meeting: {ex}", "faint")
            t.configure(state="disabled")
            return
        t.insert("end", (d["title"] or "Untitled meeting") + "\n", "big")
        when = fmt_day_iso(d["date"]) + (f" · {d['start']}" if d["start"] else "")
        self._h_pill(when)
        if d["duration_min"]:
            self._h_pill(f"{d['duration_min']} min")
        if d["participants"]:
            n = len(d["participants"])
            self._h_pill(f"{n} {'person' if n == 1 else 'people'}")
        t.insert("end", "\n")
        if d["participants"]:
            t.insert("end", ", ".join(d["participants"]) + "\n", "meta")
        if d["summary"]:
            t.insert("end", "Summary\n", "section")
            t.insert("end", d["summary"] + "\n")
        t.insert("end", "Action items\n", "section")
        if not d["action_items"]:
            t.insert("end", "None\n", "faint")
        for a in d["action_items"]:
            self._h_action_row(a, d["id"])
        if d["decisions"]:
            t.insert("end", "Decisions\n", "section")
            for x in d["decisions"]:
                t.insert("end", "•  " + x["text"] + "\n", "bullet")
        if d["open_questions"]:
            t.insert("end", "Open questions\n", "section")
            for x in d["open_questions"]:
                t.insert("end", "•  " + x["text"] + "\n",
                         ("bullet", "done") if x.get("status") == "answered" else "bullet")
        n = len(d["transcript"])
        if n:
            t.insert("end", "Transcript\n", "section")
            label = "Hide" if self.h_show_transcript else f"Show {n} lines"
            t.insert("end", label + "\n", ("link", "tr"))
            self._h_bind_row(t, "tr", self._h_toggle_transcript)
            if self.h_show_transcript:
                for r in d["transcript"]:
                    t.insert("end", f"{r['t'][:5]}  ", "meta")
                    if r["speaker"]:
                        t.insert("end", r["speaker"] + "  ", "muted")
                    t.insert("end", r["text"] + "\n")
        if d["imported"]:
            t.insert("end", "\nSaved by an older Sidenote: some parts may be missing.\n", "meta")
        t.configure(state="disabled")

    def _h_toggle_transcript(self):
        self.h_show_transcript = not self.h_show_transcript
        top = self.h_text.yview()[0]
        self._h_render_detail()
        self.h_text.yview_moveto(top)

    def _h_set_action(self, meeting_id, item_id, status):
        """Checkbox: writes straight to the meeting file (no Claude needed)."""
        result = core_update_item(meeting_id, "action", item_id, status, by="user")
        if not result.startswith("Updated"):
            self.toast(result[:80])
        top = self.h_text.yview()[0]
        self.history_render(reload=True)
        self.h_text.yview_moveto(top)

    # -- asking Claude about past meetings ------------------------------------------------
    def history_ask(self):
        if self._h_offline:
            return
        text = "" if self._h_ph_on else self.h_entry.get().strip()
        if not text:
            return
        self.h_entry.delete(0, "end")
        question_queue.put({"text": text, "scope": "history", "meeting_id": self.h_selected})
        live.last_activity = time.time()
        self._h_chat.append(("you", text))
        self._h_waiting = True
        self._h_render_chat()

    def _h_clear_chat(self):
        self._h_chat = []
        self._h_waiting = False
        self._h_render_chat()

    def _h_render_chat(self):
        """The conversation reads top-down: your question, then Claude's answer."""
        items = list(self._h_chat[-20:])
        if self._h_waiting:
            items.append(("hint", "Claude is thinking…"))
        if not items:
            if self._h_chat_shown:
                self.h_paned.forget(self.h_chat)
                self._h_chat_shown = False
            return
        if not self._h_chat_shown:
            self.h_main.update_idletasks()
            height = max(px(160), int(self.h_paned.winfo_height() * 0.42))
            self.h_paned.add(self.h_chat, stretch="never", minsize=px(100), height=height)
            self._h_chat_shown = True
        t = self.h_chat_text
        t.configure(state="normal")
        t.delete("1.0", "end")
        for who, text in items:
            if who == "you":
                t.insert("end", "You\n", "you_name")
                t.insert("end", text + "\n", "you")
            elif who == "claude":
                t.insert("end", "Claude\n", "claude_name")
                t.insert("end", text + "\n", "claude")
            else:
                t.insert("end", text + "\n", "note" if who == "note" else "hint")
        t.configure(state="disabled")
        t.see("end")                                 # newest at the bottom

    def _offline_tick(self):
        """Claude not connected: one quiet line on the start screen; in Past meetings
        the ask box says so and its send button is greyed out."""
        offline = not self.claude_connected()
        if offline != self._start_offline_shown:
            if offline:
                self.start_offline.pack(fill="x", pady=(px(16), 0))
            else:
                self.start_offline.pack_forget()
            self._start_offline_shown = offline
        self._h_set_offline(offline)

    def toggle_captions(self):
        captions_win.hide_wanted = not captions_win.hide_wanted

    # ---- periodic refresh -------------------------------------------------------
    def _state(self):
        """Short Sidenote state for the footer: (text, dot color)."""
        label = live.label()
        if label.startswith("Sidenote listening"):
            return "Claude listening", OK
        if label.startswith("Claude is thinking"):
            return "Claude thinking...", ACCENT
        if label.startswith("Sidenote idle"):
            return "Claude idle \u00b7 type 'open Sidenote' in Claude", FAINT
        if label.startswith("Sidenote paused"):
            return "Claude paused \u00b7 type 'continue' in the Claude app", WARN
        return "Claude not connected · type 'continue' in the Claude app", FAINT

    def _mic_fixable(self):
        return IS_MAC and mic.status in MIC_NEEDS_USER and transcript.source not in NAMED_SOURCES

    def _footer_click(self):
        if self._mic_fixable():
            retry_mic()
            self.toast("Trying the microphone again…")

    def _captions_state(self):
        """Footer, right side: which transcript source is active and its health."""
        if live.mode != "record":
            return "Not recording", FAINT
        status, source = transcript.status, transcript.source
        if source in NAMED_SOURCES:
            if status.startswith(f"{source} captions connected"):
                return f"{source} captions", OK
            return f"{source} \u00b7 reconnecting", WARN
        if captions_win.note:
            return "Live Captions is docked: set it to 'Floating on screen'", WARN
        label = LC_SHORT
        if IS_MAC:
            if mic.status == "on":
                label += " + your mic"
            elif mic.status == "loading":
                label += " \u00b7 preparing mic"
            elif mic.status == "asking":
                label += " \u00b7 allow the microphone for Claude"
            elif mic.status == "blocked":
                return "Mic blocked \u00b7 click to allow Claude in Microphone settings", WARN
            elif mic.status == "silent":
                return "Mic gives only silence \u00b7 click to check Microphone settings", WARN
            elif mic.status == "missing":
                label += " \u00b7 mic not installed"
            elif mic.status == "error":
                return "Mic didn't start \u00b7 click to try again", WARN
        if status.startswith("Live Captions connected"):
            return label, OK
        if "waiting for speech" in status:
            return label + " \u00b7 waiting for speech", FAINT
        if "Accessibility" in status:
            return "Allow Claude: Privacy & Security > Device Control", WARN
        return ("Captions off \u00b7 turn on Live Captions" if IS_MAC
                else "Captions off \u00b7 " + LC_HINT), WARN

    def refresh(self):
        # Claude app closed the connection: close too (not in manual test mode)
        if self.server_thread is not None and not self.server_thread.is_alive():
            self.root.destroy()
            return
        try:
            while True:
                kind, payload = ui_queue.get_nowait()
                if kind == "close":
                    self.root.destroy()
                    return
                if kind == "record":
                    self.start_recording(payload or {})
                if kind == "history_answer":
                    self._h_waiting = False
                    self._h_chat.append(("claude", payload))
                    self._h_render_chat()
                if kind == "history_changed" and self.screen == "meetings":
                    top = self.h_text.yview()[0]
                    self.history_render(reload=True)
                    self.h_text.yview_moveto(top)
                if kind == "idle":
                    self._h_chat.append(("note", "Claude stopped listening after 15 quiet "
                                                 "minutes. Copy \u201copen Sidenote\u201d into a "
                                                 "Claude chat to reconnect."))
                    self._h_render_chat()
                if kind == "new_meeting":
                    self._reset_view("New meeting started")
                if kind == "info":
                    self.update_info()
                    if "agenda" in self.visible:
                        self.render_list("agenda")
                if kind == "toast":
                    self.toast(payload, seconds=6)
                if kind == "lists":
                    self.refresh_lists(flash=payload)
                if kind == "suggestion":
                    conv = transcript.conversation()
                    if conv and conv[-1][1] == "claude" and conv[-1][2] == payload.strip():
                        self._render_feed()            # Claude's reply: already in the feed
                    else:
                        self._set_answer(payload)      # a status message
                    self.root.deiconify()
                if kind == "recap" and transcript.ended_at:
                    self._set_answer(payload, label="Recap \u00b7 saved in the meeting file")
                    self.toast("Meeting saved", seconds=6)
        except queue.Empty:
            pass

        if time.time() < self.toast_until:
            self.state_dot.configure(fg=ACCENT)
            self.state_label.configure(text=self.toast_text, fg=FG)
        else:
            text, color = self._state()
            self.state_dot.configure(fg=color)
            self.state_label.configure(text=text, fg=MUTED)

        ctext, ccolor = self._captions_state()
        _, minutes = transcript.stats()
        recording = live.mode == "record" and not transcript.ended_at
        if live.mode == "record":
            self.p_time.set(f"\u25cf  {minutes} min" if recording else f"Ended \u00b7 {minutes} min",
                            ACCENT_HI if recording else FAINT)
            n = len(transcript.people())
            self.p_people.set(f"{n} {'person' if n == 1 else 'people'}" if n else "")
            self.p_source.set(ctext if recording else "", WARN if ccolor == WARN else MUTED,
                              clickable=self._mic_fixable())
        self.tab_live.set(badge=recording)
        self._sync_top_btn()

        if transcript.ended_at or "transcript" in self.visible:
            self.tail.configure(text="")
        else:
            self.tail.configure(text=self._two_lines(transcript.tail(3)))
        if "transcript" in self.visible:
            self.render_transcript()
        self.update_chips()
        if time.time() - getattr(self, "_last_fit", 0) > 1.5:
            self._last_fit = time.time()
            self._fit_chips()
        try:
            self._offline_tick()
            self._render_feed()
            self._update_name_bar()
        except Exception as e:
            log.info("Conversation view update failed: %s", e)
        self.root.after(300, self.refresh)

    # ---- lists: actions, questions, transcript ---------------------------------
    PANEL_ORDER = ("agenda", "context", "questions", "actions", "transcript")

    def toggle_panel(self, key):
        """The views work as tabs: one open at a time (click it again to close),
        so the open list has room and Claude's answers stay readable."""
        if key in self.visible:
            self.paned.forget(self.panels[key])
            self.visible.remove(key)
        else:
            for other in list(self.visible):
                self.paned.forget(self.panels[other])
                self.visible.remove(other)
            self.visible.append(key)
            self.visible.sort(key=self.PANEL_ORDER.index)
            # insert before the next visible panel, or before the answer
            later = [k for k in self.visible if self.PANEL_ORDER.index(k) > self.PANEL_ORDER.index(key)]
            before = self.panels[later[0]] if later else self.body
            self.paned.add(self.panels[key], before=before, minsize=64,
                           height=self._panel_height(key), stretch="always")
            if key == "transcript":
                self._last_transcript_count = -1
                self.render_transcript()
            elif key == "context":
                self.render_context()
            else:
                self.render_list(key)
        self.update_chips()
        self.root.after(30, self._layout)

    def _panel_height(self, key):
        """Fit the list to its content, up to about a third of the window."""
        total = max(300, self.paned.winfo_height())
        share = int(total * 0.6 / max(1, len(self.visible)))
        if key == "transcript":
            return max(120, share)
        with transcript.lock:
            n = len(transcript.context[key])
        return max(70, min(40 + max(1, n) * 24, share))

    def _chip_hover(self, key, on):
        chip = self.chips[key]
        if key in self.visible:
            return
        bg = SURFACE if on else BG
        for part in ("frame", "border", "box", "name"):
            chip[part].configure(bg=bg)
        chip["name"].configure(fg=FG if on else MUTED)

    def update_chips(self):
        with transcript.lock:
            n_actions = sum(1 for a in transcript.context["actions"] if not a["done"])
            n_agenda = sum(1 for a in transcript.context["agenda"]
                           if a not in transcript.context["agenda_done"])
            n_context = len(transcript.context["context"])
            n_questions = sum(1 for q in transcript.context["questions"] if not q["done"])
        counts = {"agenda": n_agenda, "actions": n_actions, "questions": n_questions,
                  "context": n_context, "transcript": 0}
        flash_until = getattr(self, "_flash", {})
        for key, chip in self.chips.items():
            on = key in self.visible
            flashing = flash_until.get(key, 0) > time.time()
            bg = SURFACE_HI if on else BG                      # open views are highlighted
            fg = FG if on else MUTED
            for part in ("frame", "border", "box", "name"):
                chip[part].configure(bg=bg)
            chip["name"].configure(fg=fg)
            n = counts[key]
            badge = chip["badge"]
            if n:
                badge.configure(text=str(n),
                                bg=ACCENT if (on or flashing) else SURFACE_HI,
                                fg="#ffffff" if (on or flashing) else FG)
                if not badge.winfo_ismapped():
                    badge.pack(side="left", padx=(4, 0))
                    self.root.after(20, self._fit_chips)
            elif badge.winfo_ismapped():
                badge.pack_forget()
                self.root.after(20, self._fit_chips)

    def refresh_lists(self, flash=None):
        """Re-draw open lists; briefly highlight the chip that got a new item."""
        if flash in ("agenda", "actions", "questions", "context"):
            self._flash = getattr(self, "_flash", {})
            self._flash[flash] = time.time() + 4
        for key in ("agenda", "actions", "questions"):
            if key in self.visible:
                self.render_list(key)
        if "context" in self.visible:
            self.render_context()
        self.update_chips()

    def render_list(self, key):
        text = self.panel_text[key]
        with transcript.lock:
            if key == "agenda":
                items = [{"text": a, "done": a in transcript.context["agenda_done"],
                          "index": n} for n, a in enumerate(transcript.context["agenda"])]
            else:
                items = [dict(i, index=n) for n, i in enumerate(transcript.context[key])]
        if key != "agenda":                          # agenda keeps its order
            items.sort(key=lambda i: i["done"])      # open items first
        text.configure(state="normal")
        text.delete("1.0", "end")
        if not items:
            empty = {"agenda": "  Nothing yet \u00b7 type agenda: \u2026",
                     "actions": "  Nothing yet \u00b7 type todo: \u2026",
                     "questions": "  Nothing yet \u00b7 type ask: \u2026"}[key]
            text.insert("end", empty, "faint")
        for item in items:
            tag = f"item{item['index']}"
            text.insert("end", "  \u2713   " if item["done"] else "  \u25cb   ",
                        ("check" if item["done"] else "box", tag))
            text.insert("end", item["text"], ("done", tag) if item["done"] else (tag,))
            if key == "actions":
                # Owner after the task: "(Leon)". Unknown or unsure owners are
                # one click to fix: "Owner: ?" / "Leon?" open a list of names.
                who = owner_text(item.get("owner", ""))
                sure = item.get("sure", True)
                otag = f"owner{item['index']}"
                if who and sure:
                    text.insert("end", f"  ({who})", ("meta", tag))
                else:
                    text.insert("end", "  ")
                    text.insert("end", f"{who}?" if who else "Owner: ?", ("ask_owner", otag))
                    text.tag_bind(otag, "<Button-1>",
                                  lambda e, i=item["index"]: self.pick_owner(i, e))
                    text.tag_bind(otag, "<Enter>", lambda e, t=text: t.configure(cursor="hand2"))
                    text.tag_bind(otag, "<Leave>", lambda e, t=text: t.configure(cursor="arrow"))
                if item.get("due"):
                    text.insert("end", "  \u00b7 " + item["due"], ("meta", tag))
            text.insert("end", "\n", (tag,))
            text.tag_bind(tag, "<Button-1>",
                          lambda e, k=key, i=item["index"], d=item["done"]: self.check_item(k, i, not d))
            text.tag_bind(tag, "<Enter>", lambda e, t=text, g=tag: (
                t.configure(cursor="hand2"), t.tag_add("hover", f"{g}.first", f"{g}.last")))
            text.tag_bind(tag, "<Leave>", lambda e, t=text: (
                t.configure(cursor="arrow"), t.tag_remove("hover", "1.0", "end")))
        text.configure(state="disabled")
        total_n, done_n = len(items), sum(1 for i in items if i["done"])
        if key == "agenda":
            summary = f"{done_n} of {total_n} covered" if total_n else ""
        elif key == "actions":
            summary = f"{total_n - done_n} open" + (f" \u00b7 {done_n} done" if done_n else "") if total_n else ""
        else:
            summary = f"{total_n - done_n} to ask" + (f" \u00b7 {done_n} asked" if done_n else "") if total_n else ""
        self.panel_count[key].configure(text=summary)
        count = len(items)
        last = getattr(self, "_list_counts", {})
        if key in self.visible and last.get(key) != count:
            self.root.after(60, self._layout)
        last[key] = count
        self._list_counts = last

    def render_context(self):
        """Jira / Confluence items related to the meeting (read-only, click to open)."""
        text = self.panel_text["context"]
        with transcript.lock:
            items = [dict(i) for i in transcript.context["context"]]
        sources = transcript.sources
        text.configure(state="normal")
        text.delete("1.0", "end")
        if not items:
            if sources is None:
                msg = "  Checking for Jira and Confluence\u2026"
            elif not any(sources.values()):
                msg = "  Jira and Confluence aren't connected \u00b7 connect them in Claude to see context"
            else:
                msg = "  No context available yet"
            text.insert("end", msg, "faint")
        for n, item in enumerate(items):
            tag = f"ctx{n}"
            src = (item["source"] or "").lower()
            mark = "  \u25c6   " if "jira" in src else "  \u25a1   "
            text.insert("end", mark, ("box", tag))
            text.insert("end", item["title"], (tag,))
            meta = " \u00b7 ".join(x for x in (item["source"], item["detail"]) if x)
            if meta:
                text.insert("end", "    " + meta, ("meta", tag))
            text.insert("end", "\n", (tag,))
            if item["url"]:
                text.tag_bind(tag, "<Button-1>", lambda e, u=item["url"]: self._open_url(u))
                text.tag_bind(tag, "<Enter>", lambda e, t=text, g=tag: (
                    t.configure(cursor="hand2"), t.tag_add("hover", f"{g}.first", f"{g}.last")))
                text.tag_bind(tag, "<Leave>", lambda e, t=text: (
                    t.configure(cursor="arrow"), t.tag_remove("hover", "1.0", "end")))
        text.configure(state="disabled")
        if items:
            names = sorted({i["source"] for i in items if i["source"]})
            self.panel_count["context"].configure(
                text=f"{len(items)} from {' and '.join(names)}" if names else f"{len(items)}")
        else:
            self.panel_count["context"].configure(text="")
        last = getattr(self, "_list_counts", {})
        if "context" in self.visible and last.get("context") != len(items):
            self.root.after(60, self._layout)
        last["context"] = len(items)
        self._list_counts = last

    def _open_url(self, url):
        try:
            import webbrowser
            webbrowser.open(url)
        except Exception:
            pass

    def pick_owner(self, index, event=None):
        """One click: a short list of the people in the meeting (the user by
        name, participants, names heard), plus Team and Other."""
        menu = tk.Menu(self.root, tearoff=0, bg=SURFACE, fg=FG, activebackground=ACCENT,
                       activeforeground="#ffffff", bd=0, font=(FONT, 9))
        for person in transcript.people():
            menu.add_command(label=person, command=lambda p=person: self._set_owner(index, p))
        menu.add_command(label="Team", command=lambda: self._set_owner(index, "Team"))
        menu.add_separator()
        menu.add_command(label="Other…", command=lambda: self._other_owner(index))
        x = event.x_root if event else self.root.winfo_pointerx()
        y = event.y_root if event else self.root.winfo_pointery()
        try:
            menu.tk_popup(x, y)
        finally:
            menu.grab_release()
        return "break"

    def _set_owner(self, index, owner):
        transcript.set_owner(index, owner)
        self.render_list("actions")
        self.toast(f"Owner: {owner}")

    def _other_owner(self, index):
        from tkinter import simpledialog
        name = simpledialog.askstring("Owner", "Who owns this action item?", parent=self.root)
        if name and name.strip():
            self._set_owner(index, name.strip())

    def check_item(self, key, index, done):
        transcript.set_done(key, index, done)
        self.render_list(key)
        self.update_chips()

    def render_transcript(self):
        count = transcript.count_lines()
        pending = transcript.pending
        signature = (count, pending)
        if signature == getattr(self, "_transcript_sig", None):
            return
        self._transcript_sig = signature
        text = self.panel_text["transcript"]
        at_bottom = text.yview()[1] > 0.98
        with transcript.lock:
            entries = list(transcript.entries[-300:])
        text.configure(state="normal")
        text.delete("1.0", "end")
        if not entries and not pending:
            text.insert("end", "Nothing captured yet.", "faint")
        self.panel_count["transcript"].configure(
            text=f"{transcript.source or ''}".replace(LC_NAME, LC_SHORT))
        for t, line in entries:
            text.insert("end", t.strftime("%H:%M   "), "time")
            if line.startswith(("YOU ASKED:", "CLAUDE:")):
                text.insert("end", line + "\n", "note")
                continue
            if line == "MEETING ENDED":
                text.insert("end", "Meeting ended\n", "faint")
                continue
            speaker, sep, rest = line.partition(": ")
            if sep and len(speaker) <= 40:
                text.insert("end", speaker_name(speaker) + "  ", "speaker")
                text.insert("end", rest + "\n")
            else:
                text.insert("end", line + "\n")
        if pending:
            text.insert("end", "now     ", "time")
            text.insert("end", pending + "\n", "muted")
        text.configure(state="disabled")
        if at_bottom or count != self._last_transcript_count:
            text.see("end")
        self._last_transcript_count = count

    def _two_lines(self, text):
        """Keep only the end of the text that fits on two lines of the hearing label."""
        if not text:
            return ""
        import tkinter.font as tkfont
        if not hasattr(self, "_tail_font"):
            self._tail_font = tkfont.Font(family=FONT, size=8, slant="italic")
        width = max(150, int(self.tail.cget("wraplength") or 300))
        budget = width * 2 * 0.85            # two lines, with a safety margin for wrapping
        words = text.split()
        out = []
        for word in reversed(words):
            candidate = " ".join([word] + out)
            if self._tail_font.measure("\u2026\u201c" + candidate + "\u201d") > budget:
                break
            out.insert(0, word)
        prefix = "\u2026" if len(out) < len(words) else ""
        return f"{prefix}\u201c{' '.join(out)}\u201d"

    def run(self):
        self.root.mainloop()

    def destroy(self):
        self._remember_geometry()
        self.root.destroy()


def main():
    test_mode = sys.stdin is not None and sys.stdin.isatty()
    server = None
    if not test_mode:
        server = threading.Thread(target=lambda: mcp.run(transport="stdio"), daemon=True)
        server.start()
    else:
        log.info("Test mode: overlay only. Close the window or press Ctrl+C to stop.")
    # Only one copy can show the overlay. Others forward calls to it, and
    # take over if the primary copy goes away (or has older code).
    reopen = False
    if not try_become_primary():
        took_over, reopen = take_over_from_older()
        if took_over:
            log.info("Took over from an older Sidenote")
    while not role["primary"] and not try_become_primary():
        if test_mode:
            log.info("Sidenote is already running in another copy.")
            return
        if not server.is_alive():
            return
        time.sleep(2)
    # On exit (e.g. Claude quits): put Live Captions back on screen, then close it.
    # atexit runs these in reverse order, so show_now runs before the close.
    atexit.register(captions_win.close_live_captions)
    atexit.register(captions_win.show_now)
    atexit.register(transcript.save_now)
    set_app_id()

    if test_mode or reopen:
        open_request.set()
    # The window stays hidden until someone asks to open it.
    while True:
        while not open_request.wait(0.5):
            if server is not None and not server.is_alive():
                return
        open_request.clear()
        captions_win.hide_wanted = True
        window_open.set()
        try:
            Overlay(server).run()       # returns when the window is closed
        finally:
            end_if_needed()              # closing the window ends the meeting
            window_open.clear()
            transcript.save_now()        # make sure the meeting file is complete
            captions_win.show_now()      # never leave Live Captions off-screen
            captions_win.close_live_captions()   # Sidenote closed: close Live Captions too
            while True:                  # drop questions typed into the old window
                try:
                    question_queue.get_nowait()
                except queue.Empty:
                    break
        if test_mode or (server is not None and not server.is_alive()):
            return


if __name__ == "__main__":
    main()

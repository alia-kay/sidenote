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


def parse_list(value):
    """Accept a list, or text with one item per line / separated by ; or commas."""
    if isinstance(value, (list, tuple)):
        items = value
    else:
        text = str(value or "")
        items = re.split(r"\n|;", text) if ("\n" in text or ";" in text) else text.split(",")
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
            if agenda is not None and parse_list(agenda):
                c["agenda"] = parse_list(agenda)
            if (title and str(title).strip()) or (agenda and parse_list(agenda)):
                self.context_dirty = True
        self.save_now()

    def add_agenda_items(self, items):
        """Add agenda topics, skipping anything already on the agenda (even reworded)."""
        added = []
        with self.lock:
            for item in parse_list(items):
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
        with self.lock:
            for a in self.context["actions"]:
                if _same(a["text"], text):
                    if owner and (not a["owner"] or not a.get("sure", True)) and sure:
                        a["owner"], a["sure"] = owner, True
                    if due and not a["due"]:
                        a["due"] = due
                    self.dirty = True
                    return False
            self.context["actions"].append({"text": text, "owner": owner, "sure": sure,
                                            "due": due, "done": False})
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
        words = {w for w in re.findall(r"[a-z0-9']+", task.lower())
                 if len(w) > 2 and w not in OWNER_STOPWORDS}
        if not words:
            return "", True
        with self.lock:
            lines = [s for _, s in self.entries[-80:] if not s.startswith(NOTE_PREFIXES)]
            people = [p for p in self.people()]
        best, best_score = None, 0
        for line in lines:                       # latest best match wins
            spoken = set(re.findall(r"[a-z0-9']+", line.lower()))
            score = len(words & spoken)
            if score >= min(2, len(words)) and score >= best_score:
                best, best_score = line, score
        if not best:
            return "", True
        speaker, sep, said = best.partition(": ")
        if not sep or len(speaker) > 40:
            speaker, said = "", best
        speaker = speaker_name(speaker)
        m = ADDRESSED.search(said) or ADDRESSED_END.search(said)
        if m and m.group(1).lower() not in OWNER_STOPWORDS:
            return m.group(1), True
        if COMMITMENT.search(said) and speaker and speaker != "Others":
            return normalize_owner(speaker if speaker not in ("You", "Me") else "me"), True
        for person in people:
            first = person.split()[0]
            if re.search(r"\b" + re.escape(first) + r"\b", said, re.I):
                return person, False
        return "", True

    def add_question(self, text):
        text = text.strip()
        if not text:
            return False
        with self.lock:
            if any(_same(q["text"], text) for q in self.context["questions"]):
                return False
            self.context["questions"].append({"text": text, "done": False})
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
                self.dirty = True
                return True
        return False

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


SIDENOTE_VERSION = "2026-11-12 v9"
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
    want = window_open.is_set() and on_live_captions and not transcript.ended_at
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
            if not window_open.is_set():
                for reader in named:
                    reader.reset()
                    reader.auto.clear()
                windows.reset()
                active = None
                transcript.status = "Sidenote closed"
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
        "user says 'start Sidenote' or 'open Sidenote', call open_sidenote. Pass the "
        "meeting title, agenda, role, goals and participants if the user gave them in "
        "their message. Each open starts a new meeting, unless the user says to continue "
        "the same meeting (then pass new_meeting=false). If no title or agenda was given, "
        "show a short tip in the overlay with show_suggestion, e.g. 'Tell me the meeting "
        "title, agenda and your role, or click Meeting info.'\n\n"
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
        "returns STOP or CLOSED, follow its instructions and stop the loop.\n\n"
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


def core_open_sidenote(new_meeting=True, title="", agenda="", role="", goals="",
                       participants="", user_name=""):
    if window_open.is_set() and transcript.ended_at and new_meeting:
        transcript.new_meeting()
        core_update_meeting_info(title=title, agenda=agenda, role=role, goals=goals,
                                 participants=participants, user_name=user_name)
        ui_queue.put(("new_meeting", None))
        return ("New meeting started in the open Sidenote window.\n\n"
                + transcript.context_text() + LIVE_NEXT)
    if window_open.is_set():
        if any((title, agenda, role, goals, participants, user_name)):
            core_update_meeting_info(title=title, agenda=agenda, role=role, goals=goals,
                                     participants=participants, user_name=user_name)
            return "Sidenote is already open. Meeting info updated." + LIVE_NEXT
        return "Sidenote is already open." + LIVE_NEXT
    if new_meeting:
        transcript.new_meeting()
    core_update_meeting_info(title=title, agenda=agenda, role=role, goals=goals,
                             participants=participants, user_name=user_name)
    open_request.set()
    for _ in range(50):
        if window_open.is_set():
            return "Sidenote is open.\n\n" + transcript.context_text() + LIVE_NEXT
        time.sleep(0.1)
    return "Opening Sidenote... (it may take a second to appear)" + LIVE_NEXT


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


def core_wait_for_question(timeout_seconds=WAIT_DEFAULT_SECONDS):
    timeout = max(5, min(int(timeout_seconds), 300))
    if not window_open.is_set():
        return _end_instructions("CLOSED")
    if transcript.ended_at and \
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
            if transcript.ended_at and (datetime.datetime.now() - transcript.ended_at
                                        ).total_seconds() > ENDED_GRACE_SECONDS:
                break                        # next call returns IDLE
            try:
                question = question_queue.get(timeout=0.3)
            except queue.Empty:
                scan = _scan_if_ready()
                if scan:
                    return scan
                continue
            if question == END_TOKEN:
                return _end_instructions("END")
            live.quiet_rounds = 0
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
                f"--- MEETING INFO (use it in your answer) ---\n{transcript.context_text()}\n\n"
                f"--- TRANSCRIPT, LAST 5 MIN ---\n{transcript.since(5) or '(nothing captured)'}"
                + context_guidance()
            )
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
    transcript.add_note("CLAUDE", text)
    ui_queue.put(("suggestion", text))
    return "Shown in the overlay."


def core_start_new_meeting(title=""):
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
async def open_sidenote(new_meeting: bool = True, title: str = "", agenda: str = "",
                        role: str = "", goals: str = "", participants: str = "",
                        user_name: str = "") -> str:
    """Show the Sidenote window and start reading Live Captions. Use when the user
    says 'start Sidenote' or 'open Sidenote'. Starts a new meeting unless
    new_meeting is false. Optionally pass the meeting title, agenda (one item per
    line), the user's role, goals and participants (comma separated).
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
    """Close the Sidenote window and stop reading Live Captions."""
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
FIELD = SURFACE
FONT = "Helvetica Neue" if IS_MAC else "Segoe UI"
MAC_UI_SCALE = 1.45      # text size multiplier on macOS


ICON_64 = "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAAHX0lEQVR4Xu1bb4hc1RX/nXvve/Nnd7Ob0SZYTQm0Nlas2kZUsCVZJYW2lJjKaqENRcWPFVGCgoVlPwiW0C/tp+IHUVtoXDW1gtg/mizVlkBXqQXToMWF0lIaM9nN7s7Mm3ffO3Lum2c362523r63f7LZH8zO7iwz837nnnPu791zDmEB8PCwwsgIE+RXqHvb9wwy6e9Ecfz1GNjJzLWF3rfWIKK6Aia0Un8ijl552j9ybGQEMQOE4WGikZF4/jXS/BeeHxrSd4+ORvL6B49974dK4UfMtLtsNMI4ho1iRMxrzXVBaCIYreAphZaNQMTjcYyff+HJXz8jb5jLLcV5Bjg2vMcMjozZtx/87tVbe/2nqr6/J7ARGm0rNoyImZiISP5ah2CAiZmZiMHQVd+gZDQa7fbY2Zn2A1/92Uvvpxw/ZYD0H39/5K69feXSi55WtelWaAFWRKTWId8lwcwxQHFf2TNhFNenW8FdX/7pi8fnGsGtpMS8xMd7h4b2VDzzKkDVwFpLRGbJb7kIwMy2ZIwBuNEM7beuPTw6lnKmNOGdenxop8/mHQL6AxtHRNAXAbeuwYyoZJRmYKpN9iu7nhidkMSYuLYET6ieKxvdH9jIbjTyAuEk3ISjcBXO7nX58Y9Hh35Qq1SeqzcCIb8h3H4xMMPWqiVTbzYPXvOT0V8qfn5IE9OhwEZMtD6ze5EQjo4r0yHhrk6NY48x+vpZ2eqwseJ+EWjhKpwddwYdcCInikUlZU98ThWssCxw8SqJqiABRojLRut2FB0wBHwtjGL5cMpMRCmwDcFhu0gvXQAE5fmA7GRunXKCmYSzcDcA7RR5K0I608cSIW7MwKttg799B0itnFbiyCL4zwTs9CRUuQcQfZMHROQ4g3aKBwyIts8kb0khbs2itnc/Lts3BN2zJc/ldIVw8iOcfuVZnBsfg672gHN4gnDtcB7IvOXJStvGDAZu3Ydtd96fXLxbkWwOlA0Mb+ByfPbgw4ga05g99Q5UuVpIOGT2W7G88su47PYDSVKKI4hHfJIM06RY6LNyYSCoDcr3JjmxCGQzABE4jmB6t0BvqXVIZ/uI5YJUskF5tc9Alcr580AHy7t6WfmitqSsmP+9afJ1HpedTvZ3rDNwc9Z5A4chOGhm1iSZk+CFkGTmgoLT3cB0cssiYGuxde/+Zv+t+1px0KIzvztSnT057pMLke6uo1APkB1CYrWox6LCTGm32v233NHatv++6dL2HbbyuavDqx748bnSjs9bDoOuPaFQD5h576+IZqeLEUVE6L3uZrfjfGo1ZXWJ0HfDbYHbf6OQIM7nedz7pd3tYOKUwULvWwC5DSBuT1qjfuw3+O8Lv4AuleUEJl+mUIS41UT/TYO48t5HF/6sucJVQiX15YyCNrcBUkTNWXAUAihgi2LlRI6Inv9DjFq82MptgPQe4PJv3APTX+uEgOzZOb0AQP/Nd8wxQPHkBbkNkIKMwdbbvpnP9ReDuHXesFoEhRlAICqxSCy1DRaBQg2QytWLCYUaYLWFUBEo1AAreSiyUijUAKsmhApEbgOsmRAqCLkNsCmEOvfjm0JoUwhtCqFNIZRFCq+GzO0Ghe0CgktaCsv53OSJPyx9OyxVKM93hRVX3Oic7qwVcntAKoQ++v0R/O+3T8NU+y4cCkq7g47g3x/iiu8/dPEbIIWu9IC0l/x5gfN5qcGSNlDV3rVa9POQ2wNSIVQbvBP+9quWPhTthEDvdbckF6KWedIz94BEapOuu0FnPjjJbYC56L32pmWs6jIM0Dkhmv7bW6WeL14fQDwvqZzRzMlxH57XtSEKNUD35wGU79Y5jkClCqZOvF5WfonnFkaCf/3TZCmMFGqA1T4PEPl99vjLlck/v1ZhaXhwhum+KiQo1ABrAar0uCN08iQG/MxV4+UZYDUaoxbD/MJH2inikmL2o/hstUHJ4ErDzpxDdK6eJJq8/TpdIpXZYf004qC1rFL4QshmALfFK8TtFs68cTQpQEoRRIyQ9gysyLOU3xJnrR+T7y2uSJQ5BCTT60ovpk78EbpcXaUmKfqkSWr25Nu5m6TmwjAwaYgGrMwZdFt849jp+PrxlzH97l9Wt02ukq9DTCCBa6RVjnlSeugnjNY32tBypl5BZidn7cwUwrOnu4zk5SJplBTyBTVKsjGarLUT4gFvelrd2LKUPYW60rgBmc49wEohbZXN0Rt4HojY0wpNizcVgY/KgBE4e0JM/Ela5USErOAjTbJFgaHcUBX4qNq1G2PWRu/2+C4fFlvdXJ+IhKtwFu6K7h6V5vnDJaOJZdZqg0M4Oq7Eh4W7kpmhXU+O/upMI3hrS9kzMmC0UW0g3ISjcBXOwj0RQrL/efHBlo2mSkYbGTDaaEZIhqa0EY7CNb0Ld+NyMj11zROjH7ZCux9Ao2S03kiekIzNyWkJGsJRuKajtM4DxAgyTCjzdDNB+9tEqPeVffEE0Uc5m/PXDnLtwkG4CCfhJhyFazpHvDk6O399Lunh6RSX0vj8x7cxKvXiFNXeAAAAAElFTkSuQmCC"
ICON_32 = "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAEUElEQVR4XsVXW2gcVRj+zmUum9vSGklTawlaqFVQFF8VHwWtNKgBwQcRkaL4YNAKvgqCFfVBBAUffPApVhIsvvkiIojgpcVbJYRqa5JCqmw2252dmXN++c9MttnsTHbXBPzgsMPOmfP99/8/AgBo7nElZj4x505NHxrT4QuWcNySPWIJGoDgPbsASYFUCrkoBc6up9G7d52ev7zJKTYffn555sSwr9/zlTwYpQaJsbvg7IanJEKtEBu73IjT5+94c27BcfPWX1+ZOT7q+58xaSs1KQAlxK417wARCIAJtNIsTD2OHzn2xtxZ8cur05Pa+uc9pcZbiTFCQO2p6ttABBN4SiXGrKUyvlNL482OBN54LYqNFKKTnM0gJEdJn6GQ7XPK2mIXsoJRkppq6I+vt2hWC4gTUWpICtEZbEKA0hQmboK9wUf3CxZaVobA6haBuZiTuTUR3ZIYy+TXBXDkCXT1Buy//2GoodH87c4JQTnhtd/PYf27LyH8oEwIyfHG3FpkNi6AwMEnX0Rl6rZ+FW+jeu8DsK0m6ue/gRoaAZEtdAlzd5Oz9iaFHq0imJwCWeNcwf/1XgY2jZ3WlamjIJOAmg23ysCFphicNyaFDEKgxEaF4NjLleAzqvc9FJlrdVH/8etAaK/LJeUCMPK4NBs1mGYDbLCiuOJtZC1kUIEaGXOfUivC8NG744npZ9b5pD/WVvZFfy5q4Ye8uS17qQAuoXK2vz46jcZv30OGQ45oO1gwG7cQTB7G1OxbEEHFkcjh0Xb+ysoIbSXeRKkAHO+UB/2Bx04iWf8HQnGZKEotAVgDOTQK4fn52fzfFmFL6sLOLsjTzj9ws1v9gIN2EAwSXv1hWz3rhZ0tkMfA1S/OILq0WF5Y8sLl75/A+INPAG039EYPF2RIa38juXoFglOyJA0oiSGkcn1gkAGirzScePTZ3qrkcFVvAPRlgR3RYRHKLDSACXoIkKVcvHqpMA3DQ0eyStlu11yRBsuCHoUo0331zPvXCxFZ125tK8Lh517D8LF7QJYgZIHaW1tNQdth9ChE2aE3PXVqWykm7mTQ+25074t6GmeGbdRdPeMttrkhUNB4+0pDNVJ1axBwxjQu/OBfmf9wjJtRdHlJZ/NBZ5CWC8DjmNJZZbMlgdVVdITbzy7ib/l97avPQ+c21x+6y3i3AETu47ReQ2vlYjaQDFAvhcx6QfPiBQjlQVSGM63LegER2eKpiLD88Tv/eSTb+OlbyLDiZooyMDePZEuekrcmhu2c68pW0J6rgKuffrDnQykA6ykpEmOXNIEWQq1eaqXGyq0+dUJoaI+Db+/GcsdORKFWMjZmQVqVvL0RJ2uhpxVfGjrMxWMZz4TW5r/8vNPK9pX5m8EczMWczC1vf31+xRA97UmJQCsWIs2vUXsKPpPPZg7mYk7mlnxB5DtaLYqnhcDyWOhpXxeVtd2Bz+SzmYO5mLN9Of0/r+f/AiTkZfpa/zIeAAAAAElFTkSuQmCC"

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
        self.root.title(f"Sidenote {SIDENOTE_VERSION}")
        try:
            self._icons = [tk.PhotoImage(data=ICON_64), tk.PhotoImage(data=ICON_32)]
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

        # ---- header ---------------------------------------------------------
        header = tk.Frame(self.root, bg=BG)
        header.pack(fill="x", padx=pad, pady=(14, 0))
        self.menu_btn = tk.Label(header, text="⋯", bg=BG, fg=MUTED, cursor="hand2",
                                 font=(FONT, 16), padx=6)
        self.menu_btn.pack(side="right", anchor="n")
        end_border = tk.Frame(header, bg=LINE, padx=1, pady=1)
        end_border.pack(side="right", anchor="n", padx=(0, 6), pady=(2, 0))
        self.end_btn = tk.Label(end_border, text="End meeting", bg=BG, fg=MUTED, cursor="hand2",
                                font=(FONT, 9), padx=10, pady=3)
        self.end_btn.pack()
        self.end_btn.bind("<Button-1>", self.end_meeting)
        self._hover(self.end_btn, BG, SURFACE, fg_on=FG, fg_off=MUTED)
        self.menu_btn.bind("<Button-1>", self.open_menu)
        self._hover(self.menu_btn, BG, SURFACE, fg_on=FG, fg_off=MUTED)

        titles = tk.Frame(header, bg=BG)
        titles.pack(side="left", fill="x", expand=True)
        self.title_label = tk.Label(titles, text="", bg=BG, fg=FG, anchor="w",
                                    justify="left", font=(FONT, 13, "bold"))
        self.title_label.pack(fill="x")
        self.title_label.bind("<Button-1>", lambda e: self._edit_info_from_click())
        self.info_label = tk.Label(titles, text="", bg=BG, fg=MUTED, anchor="w",
                                   justify="left", font=(FONT, 9))
        self.info_label.bind("<Button-1>", lambda e: self._edit_info_from_click())

        # View toggles: open lists next to the answer when you want them
        chips = tk.Frame(self.root, bg=BG)
        chips.pack(fill="x", padx=pad, pady=(6, 0))
        self.show_label = tk.Label(chips, text="Show", bg=BG, fg=FAINT, font=(FONT, 8))
        self.show_label.pack(side="left", padx=(0, 6))
        self._compact = False
        self.chips = {}
        for key, label in (("agenda", "Agenda"), ("context", "Context"),
                           ("questions", "To ask"), ("actions", "Actions"),
                           ("transcript", "Transcript")):
            chip_border = tk.Frame(chips, bg=LINE, padx=1, pady=1)
            chip_border.pack(side="left", padx=(0, 4))
            chip = tk.Frame(chip_border, bg=BG, cursor="hand2", padx=6, pady=2)
            chip.pack()
            box = tk.Label(chip, text="\u2610", bg=BG, fg=MUTED, font=(FONT, 9), cursor="hand2")
            box.pack(side="left", padx=(0, 3))
            name = tk.Label(chip, text=label, bg=BG, fg=MUTED, font=(FONT, 9), cursor="hand2")
            name.pack(side="left")
            badge = tk.Label(chip, text="", bg=SURFACE_HI, fg=FG, font=(FONT, 7, "bold"),
                             padx=5, pady=0, cursor="hand2")
            parts = (chip, box, name, badge)
            for part in parts:
                part.bind("<Button-1>", lambda e, k=key: self.toggle_panel(k))
                part.bind("<Enter>", lambda e, b=chip_border: b.configure(bg=MUTED))
                part.bind("<Leave>", lambda e, b=chip_border, k=key: b.configure(
                    bg=ACCENT if k in self.visible else LINE))
            self.chips[key] = {"frame": chip, "border": chip_border, "box": box,
                               "name": name, "badge": badge}

        self._divider = tk.Frame(self.root, bg=LINE, height=1)
        self._divider.pack(fill="x", padx=pad, pady=(6, 0))

        # ---- name question: asked once, inline (no popup, never takes focus) --
        self.name_bar = tk.Frame(self.root, bg=SURFACE, padx=10, pady=6)
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
        self.caption_dot.pack(side="right", padx=(0, 4))

        # ---- input ----------------------------------------------------------
        input_box = tk.Frame(self.root, bg=SURFACE, highlightthickness=1,
                             highlightbackground=LINE, highlightcolor=ACCENT)
        input_box.pack(side="bottom", fill="x", padx=pad, pady=(4, 0))
        # Grows from 1 to 4 lines as you type, then scrolls (Shift+Enter = new line)
        self.entry = tk.Text(input_box, bg=SURFACE, fg=FG, insertbackground=FG,
                             relief="flat", font=(FONT, 10), borderwidth=0,
                             highlightthickness=0, height=1, wrap="word",
                             padx=0, pady=8, undo=True)
        self.entry.bind("<Return>", self._on_return)
        self.entry.bind("<KeyRelease>", lambda e: self._grow_input())
        self.entry.bind("<FocusIn>", self._clear_placeholder)
        self.entry.bind("<FocusOut>", self._show_placeholder)
        self.send_btn = tk.Label(input_box, text="Ask", bg=ACCENT, fg="#ffffff",
                                 font=(FONT, 9, "bold"), padx=14, pady=6, cursor="hand2")
        self.send_btn.pack(side="right", anchor="s", padx=4, pady=4)
        self.entry.pack(side="left", fill="x", expand=True, padx=(10, 6))
        self.send_btn.bind("<Button-1>", self.send)
        self._hover(self.send_btn, ACCENT, ACCENT_HI)
        self._placeholder_on = False
        self._show_placeholder()

        # ---- suggested prompt (just above the input; click = as if typed) ------
        self.suggest_row = tk.Frame(self.root, bg=BG)
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
        self.tail = tk.Label(self.root, text="", bg=BG, fg=FAINT, font=(FONT, 8, "italic"),
                             justify="left", anchor="w", wraplength=w - 2 * pad)
        self.tail.pack(side="bottom", fill="x", padx=pad, pady=(8, 0))

        # ---- answer (main content) -------------------------------------------
        self.paned = tk.PanedWindow(self.root, orient="vertical", bg=BG, bd=0,
                                    sashwidth=10, sashrelief="flat", showhandle=False,
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
            head.pack(fill="x", pady=(2, 0))
            tk.Label(head, text=title, bg=BG, fg=FG, font=(FONT, 9, "bold"),
                     anchor="w").pack(side="left")
            count = tk.Label(head, text="", bg=BG, fg=FAINT, font=(FONT, 8), anchor="w")
            count.pack(side="left", padx=(8, 0))
            self.panel_count[key] = count
            tk.Frame(frame, bg=LINE, height=1).pack(fill="x", pady=(5, 0))
            text = tk.Text(frame, wrap="word", bg=BG, fg=FG, relief="flat",
                           font=(FONT, 9), padx=2, pady=4, borderwidth=0,
                           highlightthickness=0, spacing1=3, spacing3=3,
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
        card = tk.Frame(body, bg=SURFACE)
        card.pack(fill="both", expand=True, pady=(8, 0))
        # The conversation, like in Claude: your message, then Claude's reply.
        # Newest exchange on top; scroll down for the earlier ones.
        self.answer = tk.Text(card, wrap="word", bg=SURFACE, fg=FG, relief="flat",
                              font=(FONT, 10), padx=14, pady=10, borderwidth=0,
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
        self.answer.tag_configure("you", foreground=FG, background=SURFACE_HI,
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

        if transcript.ended_at:
            self.end_btn.configure(text="Ended", fg=FAINT, cursor="arrow")
            self.end_btn.unbind("<Enter>")
            self.end_btn.unbind("<Leave>")
        self.root.bind("<Configure>", self._on_resize)
        self.update_info()
        self._set_answer("", empty=True)
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
        if compact:
            self.show_label.pack_forget()
        elif not self.show_label.winfo_ismapped():
            self.show_label.pack(side="left", padx=(0, 6),
                                 before=self.chips["agenda"]["border"])

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
        if not exchanges and not self._notice:
            no_info = not (transcript.context["title"] or transcript.context["agenda"])
            hint = ("Add the title, agenda and your role from the title above.  "
                    if no_info else "")
            a.insert("end", hint + "Ask anything, e.g. \u201cWhat should I ask now?\u201d "
                     "or \u201cWhich agenda items haven't we covered?\u201d", "hint")
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

    def _row_height(self, size=9, spacing=6):
        import tkinter.font as tkfont
        cache = getattr(self, "_row_cache", {})
        if size not in cache:
            cache[size] = tkfont.Font(family=FONT, size=size).metrics("linespace") + spacing
            self._row_cache = cache
        return cache[size]

    def _head_height(self, key):
        """Height of a list's title row and divider, measured on screen."""
        frame = self.panels[key]
        try:
            text = self.panel_text[key]
            return max(24, frame.winfo_reqheight() - text.winfo_reqheight()) + 10
        except Exception:
            return 34

    def _content_height(self, key, max_rows=None):
        """Height that shows every row of a list (measured with the real font,
        so it works with any Windows display scaling)."""
        text = self.panel_text[key]
        try:
            text.update_idletasks()
            rows = int(text.count("1.0", "end", "displaylines")[0])
        except Exception:
            rows = 3
        if key == "transcript":
            rows = 8                          # the transcript scrolls; show ~8 lines
        rows = max(1, rows)
        if max_rows:
            rows = min(rows, max_rows)
        return self._head_height(key) + rows * self._row_height() + 8

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
            answer_needed = self._answer_needed(total)
            wanted = {k: self._content_height(k) for k in self.visible}
            gaps = 10 * len(self.visible)
            free = total - answer_needed - gaps
            if sum(wanted.values()) <= free:
                # everything fits: lists show all rows, the answer gets the rest
                for k in self.visible:
                    self.paned.paneconfigure(self.panels[k], stretch="never", height=wanted[k])
                self.paned.paneconfigure(self.body, stretch="always",
                                         height=total - sum(wanted.values()) - gaps)
            else:
                # not enough room: lists get priority (at least 3 rows each, they
                # scroll), the answer keeps what its text needs
                floor = {k: self._content_height(k, max_rows=3) for k in self.visible}
                extra = max(0, free - sum(floor.values()))
                need_more = {k: wanted[k] - floor[k] for k in self.visible}
                more_total = sum(need_more.values()) or 1
                heights = {k: floor[k] + int(extra * need_more[k] / more_total)
                           for k in self.visible}
                if sum(floor.values()) > free:     # very small window: shrink the answer
                    answer_needed = max(70, total - sum(floor.values()) - gaps)
                    heights = floor
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

    def open_menu(self, event=None):
        menu = tk.Menu(self.root, tearoff=0, bg=SURFACE, fg=FG, activebackground=ACCENT,
                       activeforeground="#ffffff", bd=0, font=(FONT, 9))
        menu.bind("<Unmap>", lambda e: setattr(self, "_menu_closed_at", time.time()))
        menu.add_command(label="Meeting info...", command=self.edit_info)
        menu.add_command(label="Hide Live Captions" if not captions_win.hide_wanted
                         else "Show Live Captions", command=self.toggle_captions)
        menu.add_command(label="Open meetings folder", command=self.open_folder)
        menu.add_separator()
        menu.add_command(label="New meeting...", command=self.new_meeting)
        x = self.menu_btn.winfo_rootx()
        y = self.menu_btn.winfo_rooty() + self.menu_btn.winfo_height()
        try:
            menu.tk_popup(x - 150, y)
        finally:
            menu.grab_release()
            self._menu_closed_at = time.time()

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
                cc["agenda"] = parse_list(get("agenda")) if get("agenda") else []
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
        if not messagebox.askyesno(
                "New meeting",
                "Start a new meeting?\n\nThe current meeting is saved, then the transcript "
                "and meeting info are cleared.", parent=self.root):
            return
        transcript.new_meeting()
        if live.released or not (live.waiting or live.label().startswith("Claude")):
            self._reset_view("New meeting started \u00b7 type 'open Sidenote' in Claude to connect")
        else:
            self._reset_view("New meeting started. The previous one is saved.")

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
        self.end_btn.configure(text="Ended", fg=FAINT, cursor="arrow")
        self.end_btn.unbind("<Enter>")
        self.end_btn.unbind("<Leave>")
        connected = live.waiting or live.label().startswith("Claude")
        if connected:
            question_queue.put(END_TOKEN)
            self._set_answer("Meeting ended. Claude is writing the recap...")
        else:
            self._set_answer("Meeting ended and saved.\n\nClaude isn't connected right now, "
                             "so there's no recap yet. Type 'recap the meeting' in the "
                             "Claude app to add one.")

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
        elif transcript.ended_at:
            self.state_dot.configure(fg=FAINT)
            self.state_label.configure(text="Meeting ended \u00b7 new meeting is in the \u22ef menu",
                                       fg=MUTED)
        else:
            text, color = self._state()
            self.state_dot.configure(fg=color)
            self.state_label.configure(text=text, fg=MUTED)

        ctext, ccolor = self._captions_state()
        _, minutes = transcript.stats()
        self.caption_dot.configure(fg=ccolor)
        self.right_label.configure(text=f"{ctext}  ·  {minutes} min",
                                   fg=WARN if ccolor == WARN else FAINT,
                                   cursor="hand2" if self._mic_fixable() else "")

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
            self._render_feed()
            self._update_name_bar()
        except Exception as e:
            log.info("Conversation view update failed: %s", e)
        self.root.after(300, self.refresh)

    # ---- lists: actions, questions, transcript ---------------------------------
    PANEL_ORDER = ("agenda", "context", "questions", "actions", "transcript")

    def toggle_panel(self, key):
        if key in self.visible:
            self.paned.forget(self.panels[key])
            self.visible.remove(key)
        else:
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
            bg = "#3a2a24" if on else BG                       # warm tint when on
            fg = FG if on else MUTED
            chip["frame"].configure(bg=bg)
            chip["border"].configure(bg=ACCENT if on else LINE)
            chip["box"].configure(text="\u2611" if on else "\u2610", bg=bg,
                                  fg=ACCENT if on else MUTED)
            chip["name"].configure(bg=bg, fg=fg)
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
    # take over if the primary copy goes away.
    while not try_become_primary():
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

    if test_mode:
        open_request.set()
    # The window stays hidden until someone asks to open it.
    while True:
        while not open_request.wait(0.5):
            if server is not None and not server.is_alive():
                return
        open_request.clear()
        captions_win.hide_wanted = True
        captions_win.ensure_running()    # open Live Captions if needed
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

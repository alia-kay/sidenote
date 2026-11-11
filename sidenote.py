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
# Own-mic transcription on Mac is paused: macOS gives a process launched by
# Claude only silence. Needs a separate helper app with mic permission.
MAC_MIC_ENABLED = False
CAPTIONS_WINDOW_CLASS = "LiveCaptionsDesktopWindow"
CAPTIONS_TEXT_ID = "CaptionsTextBlock"
WAIT_DEFAULT_SECONDS = 50       # how long one wait_for_question call listens
ENDED_GRACE_SECONDS = 15 * 60  # after End meeting, stay ready this long for a new one
CUE_DELAY_SECONDS = 4          # wait this long after a cue phrase (sentence may continue)
MIN_SCAN_GAP_SECONDS = 30      # at most one scan every 30 s
REGULAR_SCAN_SECONDS = 150     # safety-net scan when lots was said without cue phrases
PAUSED_AFTER_SECONDS = 120      # no wait call for this long = Sidenote paused
AUTOFILL_AFTER_SECONDS = 180    # auto title/agenda: first try after 3 min...
AUTOFILL_MIN_LINES = 30         # ...and at least 30 captured lines
AUTOFILL_RETRY_SECONDS = 600    # one retry at 10 min if still empty

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


EMPTY_CONTEXT = {"title": "", "subject": "", "role": "", "goals": "",
                 "participants": [], "agenda": [], "recap": "",
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
            live.autofill_tries = 0
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
        text = text.strip()
        if not text:
            return False
        with self.lock:
            for a in self.context["actions"]:
                if _same(a["text"], text):
                    if owner and not a["owner"]:
                        a["owner"] = owner.strip()
                    if due and not a["due"]:
                        a["due"] = due.strip()
                    return False
            self.context["actions"].append({"text": text, "owner": owner.strip(),
                                            "due": due.strip(), "done": False})
            self.dirty = True
        return True

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

    def ingest(self, raw_text, speaker=""):
        """Take the current caption block and commit any newly finished sentences.
        speaker: label added in front of each line (e.g. 'Others' on Mac when your
        own microphone is transcribed separately)."""
        if self.ended_at:
            return                        # meeting ended: stop recording
        text = " ".join(raw_text.split())
        if not text:
            return
        parts = SENTENCE_SPLIT.split(text)
        finals, pending = parts[:-1], parts[-1]

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
            for sentence in candidates:
                key = norm(sentence)
                if not key or key in self.recent:
                    continue        # duplicate or a punctuation-only revision
                self._commit(now, f"{speaker}: {sentence}" if speaker else sentence, key)
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
                    self._commit(now, f"{speaker}: {sentence}", k)
                    self._note_cues(sentence)
        return True

    def _commit(self, now, line, key):
        """Add a finished sentence. If captions extended the previous sentence
        ('I added' -> 'I added X to the agenda'), replace it instead of adding a
        second, longer copy. A shorter re-send of a sentence we have is skipped."""
        last = self.entries[-1] if self.entries else None
        last_key = getattr(self, "_last_key", "")
        if last and last_key and (now - last[0]).total_seconds() < 20:
            if key.startswith(last_key) and len(key) > len(last_key):
                self.entries[-1] = (last[0], line)
                self._last_key = key
                self.recent.append(key)
                self.dirty = True
                return True
            if last_key.startswith(key):
                self.recent.append(key)
                return False
        self.entries.append((now, line))
        self._last_key = key
        self.recent.append(key)
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
                    self._commit(now, f"{speaker}: {sentence}" if speaker else sentence, key)
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
        c = self.context
        end = self.ended_at or datetime.datetime.now()
        bullets = lambda items: "\n".join(f"- {i}" for i in items)
        lines = [
            f"MEETING: {c['title']}",
            f"Subject: {c['subject']}",
            f"Date: {self.started.strftime('%Y-%m-%d')}, "
            f"{self.started.strftime('%H:%M')} - {end.strftime('%H:%M')}",
            "",
            "AGENDA",
            "\n".join(f"- [{'x' if a in c['agenda_done'] else ' '}] {a}" for a in c["agenda"]),
            "",
            "PARTICIPANTS",
            bullets(c["participants"]),
            "",
            "MY ROLE",
            c["role"],
            "",
            "MY GOALS",
            c["goals"],
            "",
            "QUICK RECAP",
            c["recap"],
            "",
            "ACTION ITEMS",
            "\n".join(
                f"- [{'x' if a['done'] else ' '}] {a['text']}"
                + (f" (owner: {a['owner']})" if a["owner"] else "")
                + (f" (due: {a['due']})" if a["due"] else "")
                for a in c["actions"]),
            "",
            "CONTEXT (Jira / Confluence)",
            "\n".join(f"- {x['title']}" + (f" ({x['source']})" if x["source"] else "")
                      + (f": {x['detail']}" if x["detail"] else "")
                      + (f" {x['url']}" if x["url"] else "") for x in c["context"]),
            "",
            "QUESTIONS TO ASK",
            "\n".join(f"- [{'x' if q['done'] else ' '}] {q['text']}"
                      + (" (asked)" if q["done"] else "") for q in c["questions"]),
            "",
            "FULL TRANSCRIPT",
            "(Questions typed in Sidenote are marked YOU ASKED, answers are marked CLAUDE.)",
        ]
        lines += [f"[{t.strftime('%H:%M:%S')}] {s}" for t, s in self.entries]
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
        lines = [f"[{t.strftime('%H:%M:%S')}] {s}" for t, s in items]
        if self.pending:
            lines.append(f"[now, still speaking] {self.pending}")
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
        return "\n".join(f"[{t.strftime('%H:%M:%S')}] {s}" for t, s in items)

    def full(self):
        with self.lock:
            return self._format(list(self.entries))

    def tail(self, n=3):
        with self.lock:
            items = [s for _, s in self.entries
                     if not s.startswith(("YOU ASKED:", "CLAUDE:"))][-n:]
            if self.pending:
                items.append(self.pending)
        return " ".join(items[-n:])

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
            actions = "\n".join(
                f"{i}. [{'done' if a['done'] else 'open'}] {a['text']}"
                + (f" - owner: {a['owner']}" if a["owner"] else "")
                + (f" - due: {a['due']}" if a["due"] else "")
                for i, a in enumerate(c["actions"], 1))
            questions = "\n".join(
                f"{i}. [{'asked' if q['done'] else 'not asked yet'}] {q['text']}"
                for i, q in enumerate(c["questions"], 1))
            ctx = "\n".join(f"- {x['title']} ({x['source']})" + (f": {x['detail']}" if x["detail"] else "")
                            for x in c["context"])
        return (
            f"Meeting title: {c['title'] or '(not set)'}\n"
            f"Subject: {c['subject'] or '(not set)'}\n"
            f"Agenda:\n{agenda or '(not set)'}\n"
            f"Participants: {people or '(not set)'}\n"
            f"User's role: {c['role'] or '(not set)'}\n"
            f"User's goals: {c['goals'] or '(not set)'}\n"
            f"Action items so far:\n{actions or '(none)'}\n"
            f"Questions to ask (saved for the user):\n{questions or '(none)'}\n"
            f"Context already found (Jira/Confluence):\n{ctx or '(none)'}\n"
            f"Transcript source: {self.source or '(none yet)'}"
            f"{' - speaker names included' if self.source == 'Google Meet' else ''}\n"
            f"Meeting running for {minutes} min, {count} lines captured."
        )


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
        self.autofill_tries = 0  # auto title/agenda requests sent this meeting

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
        time.sleep(0.8)
        prefs = _lc_find(win, lambda c: c.ControlTypeName == "MenuItemControl"
                         and name(c).startswith("preferences"))
        if prefs is None:
            return "could not find Preferences in the Live Captions menu"
        _activate(prefs)
        time.sleep(0.8)
        mic = _lc_find(win, mic_pred)
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

    def ensure_microphone(self, win):
        try:
            handle = win.NativeWindowHandle
        except Exception:
            return
        if self.mic_done_for == handle:
            return
        self.mic_done_for = handle
        result = enable_lc_microphone()
        log.info("Live Captions microphone: %s", result)
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
                log.info("Connected to Live Captions")
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


SIDENOTE_VERSION = "2026-11-10 v6 (Mac + Windows merged)"
auto_cc_status = {"text": ""}     # shown by get_status, for troubleshooting


class AutoCaptions:
    """Turns on Meet's captions (CC) for the user. At most two tries per
    meeting, a few seconds apart. Once captions have been on in a meeting it
    never presses again, so turning them off on purpose is respected."""
    MAX_TRIES = 2
    RETRY_SECONDS = 6

    def __init__(self):
        self.clear()

    def clear(self):
        self.tries = {}          # meeting key -> (count, time of last try)
        self.seen_on = set()     # meetings where captions have been on
        auto_cc_status["text"] = ""

    def captions_on(self, key):
        if key not in self.seen_on:
            self.seen_on.add(key)
            auto_cc_status["text"] = "Meet captions on"

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
        auto_cc_status["text"] = (f"Meet CC pressed via {how}, try {attempt + 1}"
                                  + ("" if ok else " (press failed)"))
        log.info("Auto captions: %s", auto_cc_status["text"])
        if ok and attempt == 0:
            ui_queue.put(("toast", "Turning on Google Meet captions"))


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
                name = (control.Name or "").strip().lower()
            except Exception:
                continue
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


class MicTranscriber:
    """Mac fallback: transcribes your own microphone on the computer (Whisper),
    because macOS Live Captions listens to one source at a time. Lines are saved
    as 'You: ...'. Needs: pip install faster-whisper sounddevice numpy."""
    MODEL = "base"            # multilingual, ~145 MB, downloaded once
    LANGUAGE = "en"           # language you speak in meetings (None = detect)
    RATE = 16000

    def __init__(self):
        self.thread = None
        self.running = threading.Event()
        self.status = "off"
        self.model = None

    def available(self):
        try:
            import faster_whisper, sounddevice, numpy  # noqa: F401
            return True
        except Exception:
            return False

    def _dbg(self, msg):
        try:
            with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "mic_debug.txt"), "a") as f:
                f.write(time.strftime("%H:%M:%S ") + msg + "\n")
        except Exception:
            pass

    def start(self):
        if self.running.is_set():
            return
        self._dbg("start requested")
        if not self.available():
            self.status = "missing"
            self._dbg("packages missing")
            return
        self.running.set()
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def stop(self):
        self.running.clear()
        self.status = "off"

    def _load(self):
        if self.model is None:
            self.status = "loading"
            ui_queue.put(("toast", "Preparing microphone transcription (one-time download)\u2026"))
            from faster_whisper import WhisperModel
            self.model = WhisperModel(self.MODEL, device="cpu", compute_type="int8")
        return self.model

    def _transcribe(self, audio):
        segments, _ = self._load().transcribe(
            audio, language=self.LANGUAGE, beam_size=1, vad_filter=False,
            condition_on_previous_text=False)
        words = []
        for seg in segments:
            if seg.no_speech_prob > 0.6 or seg.avg_logprob < -1.0:
                continue
            words.append(seg.text.strip())
        return " ".join(w for w in words if w)

    def _run(self):
        import numpy as np
        import sounddevice as sd
        blocks = queue.Queue()
        try:
            self._load()
            self._dbg("model loaded; default input: %s" % (sd.query_devices(kind="input") or {}).get("name"))
            stream = sd.InputStream(samplerate=self.RATE, channels=1, dtype="float32",
                                    blocksize=int(self.RATE * 0.1),
                                    callback=lambda data, frames, t, st: blocks.put(data.copy()))
            stream.start()
        except Exception as e:
            log.info("Microphone transcription unavailable: %s", e)
            self._dbg("ERROR: %r" % e)
            ui_queue.put(("toast", "Mic didn't start: " + str(e)[:120]))
            self.status = "error"
            self.running.clear()
            return
        self.status = "on"
        log.info("Microphone transcription started")
        self._dbg("stream started")
        peak, peak_t = 0.0, time.time()
        noise, speech, silence, heard = 0.004, [], 0.0, 0.0
        try:
            while self.running.is_set():
                try:
                    block = blocks.get(timeout=0.5)
                except queue.Empty:
                    continue
                level = float(np.sqrt(np.mean(block ** 2)))
                peak = max(peak, level)
                if time.time() - peak_t >= 5:
                    self._dbg("peak level last 5s: %.4f" % peak)
                    peak, peak_t = 0.0, time.time()
                talking = level > max(0.012, noise * 3.0)
                if not talking and not speech:
                    noise = 0.95 * noise + 0.05 * level          # follow the room noise
                if talking:
                    speech.append(block); silence = 0.0; heard += 0.1
                    transcript.pending = "You: \u2026"
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
                    if transcript.pending == "You: \u2026":
                        transcript.pending = ""
        finally:
            try:
                stream.stop(); stream.close()
            except Exception:
                pass
            self.status = "off"
            log.info("Microphone transcription stopped")


mic = MicTranscriber()


def captions_loop():
    """Picks the best caption source and keeps reading it.

    Prefers Google Meet (has speaker names). If Meet is not available, or its
    captions are lost for a few seconds, switches to Windows Live Captions."""
    with uia_thread():
        meet = MacMeetReader() if IS_MAC else MeetReader()
        windows = MacLiveCaptionsReader() if IS_MAC else LiveCaptionsReader()
        active = None              # reader currently feeding the transcript
        meet_lost_since = None
        while True:
            if IS_MAC and MAC_MIC_ENABLED:
                want_mic = window_open.is_set() and active is not None and active is not meet \
                    and not transcript.ended_at
                if want_mic and not mic.running.is_set():
                    mic.start()
                elif not want_mic and mic.running.is_set():
                    mic.stop()
            if not window_open.is_set():
                meet.reset(); windows.reset()
                meet.auto.clear()
                active = None
                transcript.status = "Sidenote closed"
                transcript.source = ""
                time.sleep(POLL_SECONDS)
                continue

            if active is meet:
                if meet.poll():
                    meet_lost_since = None
                else:
                    meet_lost_since = meet_lost_since or time.time()
                    if time.time() - meet_lost_since > 6:
                        active = windows
                        windows.reset()
                        transcript.pending = ""
                        transcript.skip_visible = True   # don't copy old on-screen text
                        captions_win.ensure_running()
                        transcript.source_note = f"Meet captions lost, switched to {LC_SHORT}"
                        ui_queue.put(("toast", f"Meet captions lost \u00b7 switched to {LC_SHORT}"))
                        log.info("Fell back to %s", LC_NAME)
            else:
                # Try Meet every few seconds; use it as soon as it works
                if meet.poll():
                    if active is not meet:
                        transcript.pending = ""
                    active = meet
                    meet_lost_since = None
                    transcript.source_note = ""
                    ui_queue.put(("toast", "Connected to Google Meet captions"))
                else:
                    if active is None:
                        active = windows
                    windows.poll()

            if active is meet and not IS_MAC:
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
        "from Google Meet captions (lines start with the speaker's name; 'You' is the "
        "user) or, as a fallback, the computer's Live Captions (no names; on Mac the lines "
        "are 'Others' and the user's own microphone lines are 'You'). The meeting "
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
        "participants.\n\n"
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
        "commitment or task (someone will do something), save it with add_action_item, "
        "with the owner and due date only if they were said. Never duplicate items that "
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
        "AUTOFILL: if the meeting still has no title or agenda after a few minutes, "
        "wait_for_question returns AUTOFILL. Set only the missing fields (a short "
        "title, 1-2 agenda topics) with update_meeting_info, then keep listening.\n\n"
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
        "RECAP: when asked for a recap, or when the meeting ends, write a quick recap "
        "(2-3 sentence summary, decisions, action items with owners if known, open "
        "questions; plain text, under 200 words) and save it with save_recap so it "
        "goes into the meeting file."
    ),
)


# --- Core operations (run in the primary instance, which owns the overlay) ---
END_TOKEN = "\x00END_MEETING\x00"
MISSED_TOKEN = "\x00WHAT_DID_I_MISS\x00"
MISSED_MINUTES = 3


def _end_instructions(kind):
    if kind == "END":
        return ("END: the user clicked 'End meeting'. Call get_full_transcript, write the "
                "quick recap and save it with save_recap (it is shown in the Sidenote window "
                "automatically). In the recap, also list the context items used (title + "
                "link), if any. Then call wait_for_question again: for 15 minutes Sidenote "
                "stays ready in case the user starts a new meeting from the window; after that "
                "wait_for_question returns IDLE and you stop. Stop when it returns STOP, "
                "CLOSED or IDLE.")
    count, _ = transcript.stats()
    if count and not transcript.context["recap"]:
        recap = ("Before stopping: call get_full_transcript, write the quick recap (also "
                 "listing the context items used, title + link, if any) and "
                 "save it with save_recap, then tell the user in one line that the "
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
                       participants=""):
    if window_open.is_set() and transcript.ended_at and new_meeting:
        transcript.new_meeting()
        core_update_meeting_info(title=title, agenda=agenda, role=role, goals=goals,
                                 participants=participants)
        ui_queue.put(("new_meeting", None))
        return ("New meeting started in the open Sidenote window.\n\n"
                + transcript.context_text() + LIVE_NEXT)
    if window_open.is_set():
        if any((title, agenda, role, goals, participants)):
            core_update_meeting_info(title=title, agenda=agenda, role=role,
                                     goals=goals, participants=participants)
            return "Sidenote is already open. Meeting info updated." + LIVE_NEXT
        return "Sidenote is already open." + LIVE_NEXT
    if new_meeting:
        transcript.new_meeting()
    core_update_meeting_info(title=title, agenda=agenda, role=role, goals=goals,
                             participants=participants)
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


def _autofill_if_ready():
    """Once the meeting has run a while, ask Claude to fill an empty title
    and/or agenda from the transcript. First try at 3 min (30+ lines), one
    retry at 10 min if still empty. Never touches what the user already set."""
    c = transcript.context
    missing = [k for k in ("title", "agenda") if not c[k]]
    if not missing or live.autofill_tries >= 2:
        return None
    elapsed = (datetime.datetime.now() - transcript.started).total_seconds()
    wait = AUTOFILL_AFTER_SECONDS if live.autofill_tries == 0 else AUTOFILL_RETRY_SECONDS
    if elapsed < wait or transcript.count_lines() < AUTOFILL_MIN_LINES:
        return None
    live.autofill_tries += 1
    asks = []
    if "title" in missing:
        asks.append("title: a short meeting title, 8 words max")
    if "agenda" in missing:
        asks.append("agenda: 1 or 2 main topics actually discussed (one per line)")
    return ("AUTOFILL: the meeting has no " + " and no ".join(missing) + " yet. From the "
            "transcript below, call update_meeting_info with ONLY these fields: "
            + "; ".join(asks) + ". Leave every other field empty so nothing the user "
            "set is changed. If the talk is too unclear to tell, save nothing. Do not "
            "call show_suggestion. Then call wait_for_question again.\n\n"
            f"--- TRANSCRIPT, LAST 10 MIN ---\n{transcript.since(10) or '(nothing captured)'}")


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
    autofill = _autofill_if_ready()
    if autofill:
        return autofill
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
    if new_lines <= 0:
        return None
    cue = transcript.cue_at > live.last_scan and now - transcript.cue_at >= CUE_DELAY_SECONDS
    regular = new_lines >= 8 and since_scan >= REGULAR_SCAN_SECONDS
    if not ((cue and since_scan >= MIN_SCAN_GAP_SECONDS) or regular):
        return None
    start = max(0, live.scanned_upto - 2)          # 2 lines of overlap for context
    live.scanned_upto = total
    live.last_scan = now
    return ("SCAN: new transcript lines. Quickly save, if clearly present: action items "
            "(add_action_item), questions the user should ask (add_questions_to_ask), "
            "agenda topics someone stated (add_agenda_items, never duplicates), and agenda "
            "items now clearly covered (mark_done kind 'agenda'). Usually there is little or "
            "nothing to save. Do not call show_suggestion. Then call wait_for_question "
            "again.\n\n"
            f"--- CURRENT LISTS ---\n{transcript.context_text()}\n\n"
            f"--- NEW TRANSCRIPT ---\n{transcript.lines_from(start)}"
            + context_guidance())


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
                transcript.add_note("YOU ASKED", "What did I miss?")
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
            transcript.add_note("YOU ASKED", question)
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


def core_update_meeting_info(title="", subject="", role="", goals="", participants="",
                             agenda=""):
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
    return "Action item saved." if added else "Already in the list (updated if needed)."


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


def core_save_recap(recap):
    transcript.update_context(recap=recap)
    ui_queue.put(("recap", recap.strip()))
    return f"Recap saved in {transcript.file_path}"


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
                        role: str = "", goals: str = "", participants: str = "") -> str:
    """Show the Sidenote window and start reading Live Captions. Use when the user
    says 'start Sidenote' or 'open Sidenote'. Starts a new meeting unless
    new_meeting is false. Optionally pass the meeting title, agenda (one item per
    line), the user's role, goals and participants (comma separated).
    Right after this returns, call wait_for_question and keep calling it in a
    loop until it returns STOP or CLOSED; don't stop to ask for missing meeting
    info. Sidenote shows 'Claude not connected' while no one is listening."""
    return await run("open_sidenote", new_meeting=new_meeting, title=title, agenda=agenda,
                     role=role, goals=goals, participants=participants)


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
                              agenda: str = "") -> str:
    """Save or change meeting info. Empty fields keep their value. 'agenda'
    replaces the whole agenda (one item per line); use add_agenda_items to add.
    'participants' replaces the list (comma separated). 'subject' is a short topic
    used for the file name when there is no title."""
    return await run("update_meeting_info", title=title, subject=subject, role=role,
                     goals=goals, participants=participants, agenda=agenda)


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
    """Save an action item from the meeting (a task someone committed to). Add the
    owner and due date only if they were said. Duplicates are ignored."""
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
async def save_recap(recap: str) -> str:
    """Save the quick recap of the meeting into the meeting file."""
    return await run("save_recap", recap=recap)


@mcp.tool()
async def debug_meet_tree() -> str:
    """Troubleshooting: save the structure of the Google Meet window to a file in
    Documents/Sidenote, to fix reading Meet captions."""
    return await run("debug_meet_tree")


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
    r"^\s*(title|subject|role|my role|goal|goals|agenda|participant|participants|people|todo|action|ask|q)\s*:\s*(.+)$",
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
        self.root.title("Sidenote")
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
        self.info_label.pack(fill="x", pady=(2, 0))
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

        tk.Frame(self.root, bg=LINE, height=1).pack(fill="x", padx=pad, pady=(6, 0))

        # ---- footer (packed before the body so it always stays visible) -----
        footer = tk.Frame(self.root, bg=BG)
        footer.pack(side="bottom", fill="x", padx=pad, pady=(6, 10))
        self.state_dot = tk.Label(footer, text="●", bg=BG, fg=FAINT, font=(FONT, 8))
        self.state_dot.pack(side="left")
        self.state_label = tk.Label(footer, text="", bg=BG, fg=MUTED, font=(FONT, 8), anchor="w")
        self.state_label.pack(side="left", padx=(4, 0))
        self.right_label = tk.Label(footer, text="", bg=BG, fg=FAINT, font=(FONT, 8), anchor="e")
        self.right_label.pack(side="right")
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
            text.tag_configure("hover", background=SURFACE)
            text.configure(state="disabled")
            self.panels[key] = frame
            self.panel_text[key] = text
        self.visible = []          # open panels, in display order
        self._last_transcript_count = -1

        body = tk.Frame(self.paned, bg=BG)
        self.paned.add(body, minsize=60, stretch="always")
        self.body = body
        head = tk.Frame(body, bg=BG)
        head.pack(fill="x", pady=(2, 0))
        tk.Label(head, text="Claude", bg=BG, fg=FG, font=(FONT, 9, "bold"),
                 anchor="w").pack(side="left")
        self.question_label = tk.Label(head, text="", bg=BG, fg=FAINT, anchor="w",
                                       justify="left", font=(FONT, 8))
        self.question_label.pack(side="left", padx=(8, 0), fill="x", expand=True)
        card = tk.Frame(body, bg=SURFACE)
        card.pack(fill="both", expand=True, pady=(6, 0))
        self.answer = tk.Text(card, wrap="word", bg=SURFACE, fg=FG, relief="flat",
                              font=(FONT, 10), padx=14, pady=10, borderwidth=0,
                              highlightthickness=0, spacing2=2, spacing3=5, cursor="arrow",
                              height=3)
        self.answer.pack(side="left", fill="both", expand=True)
        self.answer.tag_configure("hint", foreground=FAINT, font=(FONT, 9))
        self.answer.tag_configure("muted", foreground=MUTED)

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
            for label in (self.tail, self.info_label, self.question_label, self.title_label):
                label.configure(wraplength=width - (40 if label is self.title_label else
                                                    80 if label is self.question_label else 0))

    def _set_answer(self, text, empty=False):
        self.answer.configure(state="normal")
        self.answer.delete("1.0", "end")
        if empty:
            no_info = not (transcript.context["title"] or transcript.context["agenda"])
            hint = ("Add the title, agenda and your role from the title above.  "
                    if no_info else "")
            self.answer.insert("1.0", hint + "Ask anything, e.g. \u201cWhat should I ask now?\u201d "
                               "or \u201cWhich agenda items haven't we covered?\u201d", "hint")
        else:
            self.answer.insert("1.0", text)
        self.answer.configure(state="disabled")
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
        self.root.title(f"Sidenote - {title}" if title else "Sidenote")
        # Only a setup hint under the title, and only while nothing is filled in
        empty = not any(c[k] for k in ("title", "role", "agenda", "participants", "goals"))
        if empty:
            self.info_label.configure(text="Add title, agenda and role", cursor="hand2",
                                      fg=ACCENT)
            if not self.info_label.winfo_ismapped():
                self.info_label.pack(fill="x", pady=(2, 0))
        elif self.info_label.winfo_ismapped():
            self.info_label.pack_forget()

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
        row("My role", "role", c["role"])
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
        return "Ask anything, e.g." in self.answer.get("1.0", "end")

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
        question_queue.put(text)
        short = text if len(text) <= 48 else text[:46].rstrip() + "\u2026"
        self.question_label.configure(text=f"\u2014  you asked: {short}")
        if live.waiting or live.label().startswith("Claude"):
            self._set_answer("Thinking...")
        else:
            self._set_answer("Saved. Claude will answer as soon as Sidenote is connected "
                             "(type 'continue' in the Claude app if it stays paused).")

    def what_did_i_miss(self, _event=None):
        if transcript.ended_at:
            self.toast("This meeting has already ended")
            return
        if not transcript.since(MISSED_MINUTES):
            self.toast(f"Nothing captured in the last {MISSED_MINUTES} minutes")
            return
        question_queue.put(MISSED_TOKEN)
        self.question_label.configure(text=f"\u2014  you asked: {self.MISSED_PROMPT}")
        if live.waiting or live.label().startswith("Claude"):
            self._set_answer("Catching you up...")
        else:
            self._set_answer("Saved. Claude will answer as soon as Sidenote is connected "
                             "(type 'continue' in the Claude app if it stays paused).")

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
        self.question_label.configure(text="")
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
        self.question_label.configure(text="")
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

    def _captions_state(self):
        """Footer, right side: which transcript source is active and its health."""
        status, source = transcript.status, transcript.source
        if source == "Google Meet":
            if status.startswith("Google Meet captions connected"):
                return "Google Meet captions", OK
            return "Google Meet \u00b7 reconnecting", WARN
        if captions_win.note:
            return "Live Captions is docked: set it to 'Floating on screen'", WARN
        label = LC_SHORT
        if IS_MAC:
            if mic.status == "on":
                label += " + your mic"
            elif mic.status == "loading":
                label += " \u00b7 preparing mic"
            elif mic.status == "missing":
                label += " \u00b7 mic needs setup"
            elif mic.status == "error":
                label += " \u00b7 mic blocked (Settings > Privacy > Microphone)"
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
                    self._set_answer(payload)
                    self.root.deiconify()
                if kind == "recap" and transcript.ended_at:
                    self.question_label.configure(text="\u2014  recap, saved in the meeting file")
                    self._set_answer(payload)
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
                                   fg=WARN if ccolor == WARN else FAINT)

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
            extra = []
            if key == "actions":
                if item.get("owner"):
                    extra.append(item["owner"])
                if item.get("due"):
                    extra.append(item["due"])
            if extra:
                text.insert("end", "    " + " \u00b7 ".join(extra), ("meta", tag))
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
                text.insert("end", speaker + "  ", "speaker")
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

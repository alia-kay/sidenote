# Sidenote

Version: 2026-11-10 v6 (Mac + Windows merged)

## Objective

Sidenote is a live meeting assistant that runs next to your meeting. It reads the captions of the call, keeps a running transcript, and lets you ask Claude about the meeting in a small always-on-top window. You never have to switch to the Claude app or interrupt the conversation.

The goal is to help you stay on top of a meeting while it happens: catch up when you look away, keep track of action items and open questions, follow the agenda, and pull up project context (Jira and Confluence). At the end you have a saved transcript and a quick recap.

Sidenote works on demand. Claude answers when you ask, and quietly keeps lists up to date in the background. It doesn't push suggestions while people are talking.

How it works: Sidenote is a local MCP server for the Claude desktop app, on Windows and Mac. Everything stays on your computer except what is sent to Claude.

## Getting started

- In a Claude chat, type "open Sidenote". The window appears and Claude starts listening right away, without asking for a title or agenda first.
- Claude keeps listening for your questions until the meeting ends or the window is closed.
- "open Sidenote" again brings it back at any time.

## Transcript sources

- Google Meet captions in Chrome or Edge, with speaker names (Windows and Mac). This is the preferred source.
- Sidenote turns on Meet captions by itself. It presses the CC button and the "Turn on captions" item in its menu, without moving the mouse or pressing keys. It tries at most 2 times per meeting. If you turn captions off on purpose, it leaves them off.
- Zoom meetings in the browser (Zoom's web client), Windows and Mac: Sidenote turns on Zoom's captions (Show Captions, on the bar or under More, once per meeting) and reads the rolling caption line. Speaker names are used when Zoom shows them. The Zoom tab must be in front; a toast says so if it's in a background tab.
- Microsoft Teams meetings, in the Teams app or in the browser, Windows and Mac: Sidenote turns on Teams' live captions (More > Language and speech, once per meeting) and reads them with speaker names. It uses Teams' element ids, so it works in any Teams language. The user's own Teams display name is treated as the user.
- Windows Live Captions as a fallback, for the Zoom app, videos and any other app. It can include your own microphone.
- macOS Live Captions as a fallback on Mac. Sidenote turns it on by itself, hides its window, and switches it off when Sidenote closes. It hears the other people; the user's own voice comes from the microphone, transcribed on the Mac with Whisper (through Claude's microphone permission; Sidenote asks macOS for it, and says so in the footer if access is blocked or the mic gives only silence).
- If Meet captions are lost, Sidenote switches to Live Captions automatically.

## The Sidenote window

- Always on top, sized to the screen, dark theme in Sidenote orange.
- Header: meeting title and info (click to edit), "End meeting" button and a ⋯ menu.
- Toggle chips to open side panels: Agenda, Context, To ask, Actions and Transcript, each with a count badge.
- Answer card showing Claude's latest answer and the question you asked.
- Hearing line showing the last words captured.
- Text bar to ask Claude anything. It grows to 4 lines; Shift+Enter adds a new line.
- Autosuggestion above the text bar: "✦ What did I miss? (last 3 min)". Clicking it works as if you typed it, and it hides while you type.
- Status footer showing whether Claude is listening, which caption source is active, and how long the meeting has been running.
- ⋯ menu: Meeting info, Hide/Show Live Captions, Open meetings folder, New meeting.

## Asking Claude

- Type a question; Claude answers in the window using the meeting info and the last 5 minutes of transcript.
- "What did I miss?" gives a summary of the last 3 minutes in at most 3 short lines: what was discussed, decisions, and anything asked of you.
- Typing "stop" ends live mode.

## Shortcuts in the text bar (saved without asking Claude)

- todo: or action: adds an action item
- ask: or q: adds a question to the To ask list
- agenda: adds agenda items
- participants: adds participants
- title:, role: (or my role:), goal: sets meeting info

## Automatic background work

- Scans: when a cue phrase is said (for example "need to", "next steps", "deadline", "let's discuss", or a ticket number), or after a lot of talk, Claude checks the new lines. It saves action items, questions you should ask, new agenda topics, and agenda items that are now covered.
- Automatic title and agenda: if the meeting still has no title or agenda after about 3 minutes (and 30 lines), Claude fills in a short title and 1-2 agenda topics. It tries once more at 10 minutes and never changes what you set yourself.

## Jira and Confluence context

- When Sidenote opens, Claude checks whether it has Jira or Confluence tools in the chat.
- If it does, it searches for the meeting topic and adds up to 6 useful items to the Context list, such as the project home, specs, the sprint or epic, and previous meeting notes.
- During the meeting, when a new feature, epic, ticket number or document comes up, it adds 1-2 items for that topic. Spoken requests like "pull up X" count too.
- The list holds at most 12 items. Searches are per topic and never repeated, to save Atlassian credits.
- Read only: Claude never creates or edits anything in Jira or Confluence unless you ask and confirm.

## Ending a meeting and recap

- "End meeting" or closing the window ends the meeting.
- Claude writes a quick recap and saves it into the meeting file: a 2-3 sentence summary, decisions, action items with owners, open questions and the context items used.
- After "End meeting", Sidenote stays ready for 15 minutes in case you start a new meeting from the window, then goes idle.
- New meeting (⋯ menu) saves the current meeting and starts a clean one.

## Saved files

- Each meeting is saved automatically in Documents/Sidenote as a readable text file and, next to it, a <same name>.meeting.json (schema_version 1): meeting info, summary, by person, decisions, open questions, action items (id, owner, real due date, status, where they came from, who closed them and why), questions to ask, context and the transcript with timestamps. One self-contained file per meeting; a small cache (.sidenote_index.json) keeps Past meetings fast and is rebuilt automatically.
- Meetings saved before v10 are imported once (best effort, marked imported); their .txt files are never changed. Installing or updating Sidenote never writes to or deletes anything in Documents/Sidenote.

## Window: two tabs

- Two icon tabs are always at the top: + (New meeting) and a clock (Past meetings). "open Sidenote" opens on +, where the user clicks Start meeting; captions are read only while recording, and recording goes on while the user looks at past meetings (+ shows a dot).
- Past meetings: a list by day on the left (All meetings on top) and the selected meeting in the center: summary, action items with checkboxes, decisions, open questions, transcript folded. "All meetings" shows every open action item and recent decisions. A rounded ask box asks Claude about the selected meeting or all meetings. The window widens for the list and narrows back on +.
- Browsing and ticking work without Claude; when Claude isn't connected the window says so plainly with a one-click copy of "open Sidenote".
- Claude answers past-meeting questions with list_meetings, find_items, get_meeting and search_transcripts, always naming the source meeting and date. It closes action items only on the user's explicit request (stored as closed by Claude, with the request as evidence, undoable).
- When nothing is recording, Claude listens in longer intervals and stops (IDLE) after 15 quiet minutes.
- Dark look with a serif title, rounded pills (time, people, captions source) and a rounded ask box with a round send button.

## Tools Claude can use (MCP)

open_sidenote, close_sidenote, wait_for_question, show_suggestion, update_meeting_info, add_agenda_items, add_participants, add_action_item, add_questions_to_ask, mark_done, set_context_sources, add_context_item, save_recap, get_recent_transcript, get_full_transcript, get_meeting_context, start_new_meeting, get_status (shows the source, line count, auto-captions activity and version), list_meetings, get_meeting, find_items, search_transcripts, update_item, debug_meet_tree, debug_call_window, debug_live_captions_tree.

## Technical notes

- A single Python file, sidenote.py, runs as a local MCP server started by the Claude desktop app.
- Windows requirements: pip install mcp uiautomation. Mac requirements: pip install mcp pyobjc-framework-ApplicationServices pyobjc-framework-Cocoa.
- On Mac, Claude needs permission in Privacy & Security > Device Control and Data Access (called Accessibility on older macOS).
- Only one copy of Sidenote owns the window. Other chats talk to it locally (127.0.0.1).

## Still open

- Own-microphone transcription on Mac is back (v9), not yet confirmed on a real Mac. If macOS still gives only silence with permission granted, the fallback is a separate helper app with its own mic permission.
- Old Sidenote processes on Mac can survive quitting Claude and need sudo pkill. Sidenote should exit when Claude disconnects.
- Live Captions was "not found" on the very first Mac try. Keep an eye on it.
- The Mac + Windows merged version hasn't been tested in a real meeting yet.

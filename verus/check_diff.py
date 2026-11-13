#!/usr/bin/env python3
"""Diff every function copied into conform.rs against the original source.

usage: check_diff.py            compare against expected_diff.txt (exit 1 on any difference)
       check_diff.py --update   rewrite expected_diff.txt
       check_diff.py --show     print the diff

Original = rust/automerge/src at the current checkout (includes the committed on_timeout patch).
Function text is cut by brace matching from the line matching `fn NAME(` after an optional anchor.
Blank lines and leading/trailing whitespace are ignored.
"""
import difflib, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "rust", "automerge", "src")
V = open(os.path.join(HERE, "conform.rs")).read()

# (label, original file, original anchor, original fn, verus anchor, verus fn)
ITEMS = [
    ("SyncDoc::generate_sync_message", "sync.rs", r"impl SyncDoc for Automerge", "generate_sync_message", r"impl Automerge", "generate_sync_message"),
    ("SyncDoc::receive_sync_message", "sync.rs", r"impl SyncDoc for Automerge", "receive_sync_message", r"receive_sync_message \(copied\)", "receive_sync_message"),
    ("Automerge::receive_sync_message_inner", "sync.rs", r"impl Automerge \{", "receive_sync_message_inner", r"receive_sync_message \(copied\)", "receive_sync_message_inner"),
    ("Automerge::make_bloom_filter", "sync.rs", r"impl Automerge \{", "make_bloom_filter", r"impl Automerge", "make_bloom_filter"),
    ("Message::reset", "sync.rs", r"impl Message \{", "reset", r"impl Message \{", "reset"),
    ("MessageFlags::new", "sync.rs", r"impl MessageFlags", "new", r"pub struct MessageFlags", "new"),
    ("MessageFlags::contains", "sync.rs", r"impl MessageFlags", "contains", r"pub struct MessageFlags", "contains"),
    ("MessageFlags::set", "sync.rs", r"impl MessageFlags", "set", r"pub struct MessageFlags", "set"),
    ("State::on_timeout", "sync/state.rs", r"impl State", "on_timeout", r"impl State", "on_timeout"),
    ("State::supports_v2_messages", "sync/state.rs", r"impl State", "supports_v2_messages", r"impl State", "supports_v2_messages"),
    ("State::peer_supports_sync_reset", "sync/state.rs", r"impl State", "peer_supports_sync_reset", r"impl State", "peer_supports_sync_reset"),
    ("State::is_peer_read_only", "sync/state.rs", r"impl State", "is_peer_read_only", r"impl State", "is_peer_read_only"),
    ("State::send_doc", "sync/state.rs", r"impl State", "send_doc", r"impl State", "send_doc"),
    ("State::their", "sync/state.rs", r"impl State", "their", r"impl State", "their"),
]

def cut(text, anchor, fn):
    m = re.search(anchor, text)
    if not m:
        sys.exit("anchor not found: " + anchor)
    m2 = re.compile(r"^[ \t]*(?:pub(?:\([a-z]+\))? )?fn " + re.escape(fn) + r"\b", re.M).search(text, m.start())
    if not m2:
        sys.exit("fn not found: " + fn)
    start = text.rfind("\n", 0, m2.start()) + 1
    i = text.index("{", m2.end())
    own = re.compile(r"\n[ \t]*\{[ \t]*\n").search(text, m2.end())
    if own and re.search(r"\b(requires|ensures)\b", text[m2.end():own.end()]) and own.start() < text.find("\n    pub fn ", m2.end()) if text.find("\n    pub fn ", m2.end()) > 0 else own and re.search(r"\b(requires|ensures)\b", text[m2.end():own.end()]):
        i = own.end() - 2 - (len(own.group(0)) - len(own.group(0).lstrip()) if False else 0)
        i = text.index("{", own.start())
    # skip a `{` that is inside the signature's where/ensures: take first `{` at depth 0 after the `)`/`->`
    # (copied functions have no braces in signatures except spec blocks; those are handled by the verus side skipping below)
    depth, j = 0, i
    while True:
        c = text[j]
        if c == "{": depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0: break
        j += 1
    return text[start:j + 1]

def norm(s):
    return [l.strip() for l in s.splitlines() if l.strip()]

out = []
for label, of, oa, ofn, va, vfn in ITEMS:
    o = cut(open(os.path.join(SRC, of)).read(), oa, ofn)
    v = cut(V, va, vfn)
    d = list(difflib.unified_diff(norm(o), norm(v), "original " + of + " " + ofn, "verus/conform.rs " + vfn, lineterm="", n=0))
    out.append("=== " + label)
    out.extend(d if d else ["(identical)"])
text = "\n".join(out) + "\n"
exp = os.path.join(HERE, "expected_diff.txt")
if "--update" in sys.argv:
    open(exp, "w").write(text); print("updated", exp)
elif "--show" in sys.argv:
    print(text)
else:
    if open(exp).read() == text: print("diff matches expected_diff.txt"); sys.exit(0)
    sys.stdout.writelines(difflib.unified_diff(open(exp).read().splitlines(True), text.splitlines(True), "expected", "actual"))
    sys.exit(1)

#!/usr/bin/env python3
"""github-core-clone-01: a standalone GitHub-compatible git forge in one process.

Serves, from a single Python 3.13 stdlib-only process with an in-memory store:
  * git smart HTTP (protocol v2 + v0, upload-pack / receive-pack, packs, shallow)
  * GitHub REST v3 (/api/v3): repos, branches, commits, contents, issues, labels, pulls
  * GitHub GraphQL v4 (/api/graphql): the documents gh and github-mcp-server send
  * MCP over streamable HTTP (/mcp): server/discover + legacy initialize, tools/list/call

Lifecycle (the kit's contract): bind an ephemeral port, POST {"port": N} to
$MAKEFUN_ENV_URL/register, poll $MAKEFUN_ENV_URL/done until {"done": true},
then exit 0. Without MAKEFUN_ENV_URL it serves standalone (dev / local grading).

Auth: every API/git/MCP call needs `Authorization: Bearer $MAKEFUN_SHOP_TOKEN`
(the token the trial hands this process). /healthz needs none. The token's owner
is the scenario viewer (adaiversen, id 1000); any other owner in a URL is 404.

Determinism: no wall clock in any stored state. Creation order comes from a
monotonic sequence; every timestamp rendered is the fixed FIXED_TIME.
"""

import base64
import difflib
import hashlib
import json
import os
import re
import socket
import sys
import threading
import time
import urllib.parse
import urllib.request
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# --------------------------------------------------------------------------- constants

VIEWER_LOGIN = "adaiversen"
VIEWER_ID = 1000
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = "adaiversen@example.invalid"
DEFAULT_BRANCH = "main"
FIXED_TIME = "2026-01-01T00:00:00Z"
FIXED_EPOCH = 1767225600  # 2026-01-01T00:00:00Z, + fixed per-commit offsets
SERVER_NAME = "github-core-clone-forge"
SERVER_VERSION = "1.0.0"
MCP_REVISION = "2026-07-28"
MCP_REVISIONS = ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"]
ZERO_OID = "0" * 40
AGENT = "github-core-clone-forge/1.0"

# --------------------------------------------------------------------------- git objects

_OBJ_TYPE_CODE = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
_OBJ_CODE_TYPE = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}


def hash_object(otype, data):
    """SHA-1 id of a git object: sha1("<type> <len>\\0<data>")."""
    h = hashlib.sha1()
    h.update(otype.encode("ascii"))
    h.update(b" ")
    h.update(str(len(data)).encode("ascii"))
    h.update(b"\0")
    h.update(data)
    return h.hexdigest()


def parse_tree(data):
    """Parse tree bytes -> [(mode, name, oid-hex)]."""
    entries = []
    i = 0
    n = len(data)
    while i < n:
        sp = data.index(b" ", i)
        mode = data[i:sp].decode("ascii")
        nul = data.index(b"\0", sp)
        name = data[sp + 1:nul].decode("utf-8", "surrogateescape")
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        i = nul + 21
    return entries


def _tree_sort_key(entry):
    mode, name, _oid = entry
    # git sorts directory names as if they had a trailing slash
    return name + ("/" if mode == "40000" else "")


def build_tree(entries):
    """Build tree bytes from [(mode, name, oid-hex)], git-sorted."""
    out = bytearray()
    for mode, name, oid in sorted(entries, key=_tree_sort_key):
        out += mode.encode("ascii") + b" " + name.encode("utf-8", "surrogateescape")
        out += b"\0" + bytes.fromhex(oid)
    return bytes(out)


def parse_commit(data):
    """Parse commit bytes -> dict(tree, parents, author, committer, message)."""
    text = data.decode("utf-8", "surrogateescape")
    head, _, message = text.partition("\n\n")
    out = {"tree": None, "parents": [], "author": "", "committer": "", "message": message}
    for line in head.split("\n"):
        if line.startswith("tree "):
            out["tree"] = line[5:].strip()
        elif line.startswith("parent "):
            out["parents"].append(line[7:].strip())
        elif line.startswith("author "):
            out["author"] = line[7:]
        elif line.startswith("committer "):
            out["committer"] = line[10:]
    return out


def build_commit(tree, parents, author, committer, message):
    lines = ["tree " + tree]
    for p in parents:
        lines.append("parent " + p)
    lines.append("author " + author)
    lines.append("committer " + committer)
    return ("\n".join(lines) + "\n\n" + message).encode("utf-8", "surrogateescape")


def parse_tag(data):
    text = data.decode("utf-8", "surrogateescape")
    head, _, message = text.partition("\n\n")
    out = {"object": None, "type": None, "tag": None, "tagger": "", "message": message}
    for line in head.split("\n"):
        if line.startswith("object "):
            out["object"] = line[7:].strip()
        elif line.startswith("type "):
            out["type"] = line[5:].strip()
        elif line.startswith("tag "):
            out["tag"] = line[4:].strip()
        elif line.startswith("tagger "):
            out["tagger"] = line[7:]
    return out


def ident_line(name, email, epoch):
    return "%s <%s> %d +0000" % (name, email, epoch)


# --------------------------------------------------------------------------- pkt-line

def pkt_line(payload):
    """Encode one pkt-line. payload: bytes (without length prefix)."""
    if isinstance(payload, str):
        payload = payload.encode("utf-8")
    return ("%04x" % (len(payload) + 4)).encode("ascii") + payload


def pkt_flush():
    return b"0000"


def pkt_delim():
    return b"0001"


def decode_pkt_lines(buf):
    """Decode a byte string into a list of packets.

    Returns list of ('data', bytes) | ('flush', None) | ('delim', None) |
    ('response-end', None). Raises ValueError on malformed input.
    """
    packets = []
    i = 0
    n = len(buf)
    while i < n:
        if i + 4 > n:
            raise ValueError("truncated pkt-line length")
        hexlen = buf[i:i + 4]
        try:
            ln = int(hexlen.decode("ascii"), 16)
        except ValueError:
            raise ValueError("bad pkt-line length %r" % hexlen)
        if ln == 0:
            packets.append(("flush", None))
            i += 4
        elif ln == 1:
            packets.append(("delim", None))
            i += 4
        elif ln == 2:
            packets.append(("response-end", None))
            i += 4
        else:
            if i + ln > n:
                raise ValueError("truncated pkt-line payload")
            packets.append(("data", bytes(buf[i + 4:i + ln])))
            i += ln
    return packets


# --------------------------------------------------------------------------- packfile

def _pack_obj_header(otype, size):
    code = _OBJ_TYPE_CODE[otype]
    first = (code << 4) | (size & 0x0F)
    size >>= 4
    if size:
        first |= 0x80
    out = bytearray([first])
    while size:
        b = size & 0x7F
        size >>= 7
        if size:
            b |= 0x80
        out.append(b)
    return bytes(out)


def write_pack(objects):
    """Build a pack v2 from [(otype, data)] (no deltas). Returns bytes."""
    out = bytearray()
    out += b"PACK" + (2).to_bytes(4, "big") + len(objects).to_bytes(4, "big")
    for otype, data in objects:
        out += _pack_obj_header(otype, len(data))
        out += zlib.compress(data)
    trailer = hashlib.sha1(bytes(out)).digest()
    out += trailer
    return bytes(out)


def _read_varint(buf, pos):
    first = buf[pos]
    size = first & 0x0F
    shift = 4
    pos += 1
    while buf[pos - 1] & 0x80:
        size |= (buf[pos] & 0x7F) << shift
        shift += 7
        pos += 1
    return size, pos


def _read_ofs_delta_base(buf, pos):
    b = buf[pos]
    pos += 1
    offset = b & 0x7F
    while b & 0x80:
        b = buf[pos]
        pos += 1
        offset = ((offset + 1) << 7) | (b & 0x7F)
    return offset, pos


def apply_delta(base, delta):
    """Apply a git binary delta to base bytes."""
    pos = 0

    def varint():
        nonlocal pos
        out = 0
        shift = 0
        while True:
            b = delta[pos]
            pos += 1
            out |= (b & 0x7F) << shift
            shift += 7
            if not (b & 0x80):
                return out

    src_size = varint()
    tgt_size = varint()
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            cp_off = 0
            cp_size = 0
            for i in range(4):
                if op & (1 << i):
                    cp_off |= delta[pos] << (8 * i)
                    pos += 1
            for i in range(3):
                if op & (0x10 << i):
                    cp_size |= delta[pos] << (8 * i)
                    pos += 1
            if cp_size == 0:
                cp_size = 0x10000
            out += base[cp_off:cp_off + cp_size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != tgt_size:
        raise ValueError("delta result size mismatch")
    return bytes(out)


def read_pack(pack, resolve_base=None):
    """Parse a packfile. Returns (objects, delta_count) where objects is a list
    of (oid, otype, data) in pack order. resolve_base(oid) looks up a base
    object outside the pack (thin packs). Raises ValueError on bad input.
    """
    if len(pack) < 12 or pack[:4] != b"PACK":
        raise ValueError("not a packfile")
    version = int.from_bytes(pack[4:8], "big")
    if version not in (2, 3):
        raise ValueError("unsupported pack version %d" % version)
    count = int.from_bytes(pack[8:12], "big")
    trailer = pack[-20:]
    if hashlib.sha1(pack[:-20]).digest() != trailer:
        raise ValueError("pack trailer checksum mismatch")
    pos = 12
    entries = []  # (offset, otype, data) with otype None for unresolved deltas
    offsets = {}  # offset -> index into entries
    for _ in range(count):
        start = pos
        first = pack[pos]
        code = (first >> 4) & 0x07
        size, pos = _read_varint(pack, pos)
        if code in (1, 2, 3, 4):
            otype = _OBJ_CODE_TYPE[code]
            d = zlib.decompressobj()
            data = d.decompress(pack[pos:])
            consumed = len(pack[pos:]) - len(d.unused_data)
            pos += consumed
            entries.append([start, otype, data])
            offsets[start] = len(entries) - 1
        elif code == 6:  # ofs-delta
            base_off, pos = _read_ofs_delta_base(pack, pos)
            d = zlib.decompressobj()
            delta = d.decompress(pack[pos:])
            pos += len(pack[pos:]) - len(d.unused_data)
            entries.append([start, ("ofs", start - base_off), delta])
            offsets[start] = len(entries) - 1
        elif code == 7:  # ref-delta
            base_oid = pack[pos:pos + 20].hex()
            pos += 20
            d = zlib.decompressobj()
            delta = d.decompress(pack[pos:])
            pos += len(pack[pos:]) - len(d.unused_data)
            entries.append([start, ("ref", base_oid), delta])
            offsets[start] = len(entries) - 1
        else:
            raise ValueError("unknown pack object type %d" % code)
    # resolve deltas (may chain; iterate until stable)
    resolved = {}
    delta_count = 0
    changed = True
    while changed:
        changed = False
        for idx, (off, otype, data) in enumerate(entries):
            if isinstance(otype, tuple):
                kind, base = otype
                if kind == "ofs":
                    base_idx = offsets.get(base)
                    if base_idx is None or not isinstance(entries[base_idx][1], str):
                        continue
                    base_type, base_data = entries[base_idx][1], entries[base_idx][2]
                else:
                    base_oid = base
                    if base_oid in resolved:
                        base_type, base_data = resolved[base_oid]
                    elif resolve_base is not None:
                        found = resolve_base(base_oid)
                        if found is None:
                            continue
                        base_type, base_data = found
                    else:
                        continue
                data = apply_delta(base_data, data)
                entries[idx][1] = base_type
                entries[idx][2] = data
                delta_count += 1
                changed = True
    objects = []
    for _off, otype, data in entries:
        if not isinstance(otype, str):
            raise ValueError("unresolved delta in pack")
        oid = hash_object(otype, data)
        objects.append((oid, otype, data))
        resolved[oid] = (otype, data)
    return objects, delta_count


# --------------------------------------------------------------------------- store

class NotFound(Exception):
    pass


class Conflict(Exception):
    pass


class Unprocessable(Exception):
    pass


class Repo:
    __slots__ = ("owner", "name", "id", "private", "description", "default_branch",
                 "seq", "objects", "refs", "issues", "pulls", "labels",
                 "next_number", "created_seq", "commit_seq", "commit_meta")

    def __init__(self, owner, name, rid, private, description, created_seq):
        self.owner = owner
        self.name = name
        self.id = rid
        self.private = private
        self.description = description
        self.default_branch = DEFAULT_BRANCH
        self.seq = 0
        self.objects = {}   # oid -> (otype, bytes)
        self.commit_seq = {}  # commit oid -> creation sequence
        self.commit_meta = {}  # commit oid -> parsed commit (parents/tree cache)
        self.refs = {}      # "refs/heads/x" -> oid
        self.issues = {}    # number -> dict
        self.pulls = {}     # number -> dict
        self.labels = {}    # name -> dict
        self.next_number = 1
        self.created_seq = created_seq

    @property
    def full_name(self):
        return "%s/%s" % (self.owner, self.name)

    def put_object(self, otype, data):
        oid = hash_object(otype, data)
        if oid not in self.objects:
            self.objects[oid] = (otype, data)
            if otype == "commit":
                self.seq += 1
                self.commit_seq[oid] = self.seq
                self.commit_meta[oid] = parse_commit(data)
        return oid

    def commit_parents(self, oid):
        meta = self.commit_meta.get(oid)
        if meta is None:
            obj = self.objects.get(oid)
            if obj is None or obj[0] != "commit":
                return []
            meta = parse_commit(obj[1])
            self.commit_meta[oid] = meta
        return meta["parents"]

    def commit_tree(self, oid):
        meta = self.commit_meta.get(oid)
        if meta is None:
            obj = self.objects.get(oid)
            if obj is None or obj[0] != "commit":
                return None
            meta = parse_commit(obj[1])
            self.commit_meta[oid] = meta
        return meta["tree"]

    def get_object(self, oid):
        return self.objects.get(oid)

    def ref_tip(self, branch):
        return self.refs.get("refs/heads/" + branch)

    def tree_at(self, ref):
        """Resolve a ref name / sha to (commit_oid, tree_oid)."""
        oid = self.resolve_ref(ref)
        if oid is None:
            return None
        obj = self.objects.get(oid)
        if obj is None:
            return None
        otype, data = obj
        if otype == "commit":
            return oid, parse_commit(data)["tree"]
        if otype == "tree":
            return oid, oid
        if otype == "tag":
            target = parse_tag(data)["object"]
            return self.tree_at(target)
        return None

    def resolve_ref(self, ref):
        if ref is None:
            ref = self.default_branch
        if ref in self.refs:
            return self.refs[ref]
        if ("refs/heads/" + ref) in self.refs:
            return self.refs["refs/heads/" + ref]
        if ("refs/tags/" + ref) in self.refs:
            return self.refs["refs/tags/" + ref]
        if ref in self.objects:
            return ref
        return None

    def flatten_tree(self, tree_oid):
        """tree oid -> {path: (mode, blob_oid)} recursively."""
        out = {}

        def walk(toid, prefix):
            obj = self.objects.get(toid)
            if obj is None:
                return
            otype, data = obj
            if otype != "tree":
                return
            for mode, name, oid in parse_tree(data):
                path = prefix + name
                if mode == "40000":
                    walk(oid, path + "/")
                else:
                    out[path] = (mode, oid)

        walk(tree_oid, "")
        return out

    def build_tree_from_files(self, files):
        """files: {path: (mode, blob_oid)} -> root tree oid (creates objects)."""
        # nested dict
        root = {}

        def insert(node, parts, mode, oid):
            head = parts[0]
            if len(parts) == 1:
                node[head] = (mode, oid)
            else:
                child = node.setdefault(head, {})
                if not isinstance(child, dict):
                    child = node[head] = {}
                insert(child, parts[1:], mode, oid)

        for path, (mode, oid) in files.items():
            insert(root, path.split("/"), mode, oid)

        def build(node):
            entries = []
            for name, val in node.items():
                if isinstance(val, dict):
                    entries.append(("40000", name, build(val)))
                else:
                    entries.append((val[0], name, val[1]))
            return self.put_object("tree", build_tree(entries))

        return build(root)

    def commit_for_path(self, branch, path, blob_oid, message, committer_epoch):
        """Create a commit on `branch` setting path -> blob (or deleting when
        blob_oid is None). Returns (commit_oid, blob_sha_or_None)."""
        tip = self.ref_tip(branch)
        if tip is None:
            # unborn branch: start from the default branch tip when it exists
            # (GitHub creates a new branch from the default branch), else root.
            if branch != self.default_branch:
                tip = self.ref_tip(self.default_branch)
            parents = [] if tip is None else [tip]
            base_files = {}
            if tip is not None:
                _, tree = self.tree_at(tip)
                base_files = self.flatten_tree(tree)
        else:
            parents = [tip]
            _, tree = self.tree_at(tip)
            base_files = self.flatten_tree(tree)
        files = dict(base_files)
        if blob_oid is None:
            files.pop(path, None)
        else:
            files[path] = ("100644", blob_oid)
        tree_oid = self.build_tree_from_files(files)
        ident = ident_line(VIEWER_NAME, VIEWER_EMAIL, committer_epoch)
        # the message is stored exactly as submitted (no forced newline:
        # GET /commits echoes it byte for byte)
        commit = self.put_object("commit", build_commit(tree_oid, parents, ident, ident, message))
        self.refs["refs/heads/" + branch] = commit
        return commit

    def commits_from(self, tip):
        """All commits reachable from tip, newest (creation order) first."""
        seen = {}
        order = []

        def visit(oid):
            if oid in seen or oid is None:
                return
            obj = self.objects.get(oid)
            if obj is None or obj[0] != "commit":
                return
            seen[oid] = True
            order.append(oid)
            for p in self.commit_parents(oid):
                visit(p)

        visit(tip)
        # newest first by creation sequence
        order.sort(key=lambda o: -self.commit_seq.get(o, 0))
        return order

    def ancestors(self, tip):
        out = set()
        stack = [tip]
        while stack:
            oid = stack.pop()
            if oid in out or oid is None:
                continue
            obj = self.objects.get(oid)
            if obj is None or obj[0] != "commit":
                continue
            out.add(oid)
            stack.extend(self.commit_parents(oid))
        return out

    def is_ancestor(self, maybe_ancestor, tip):
        if maybe_ancestor == tip:
            return True
        return maybe_ancestor in self.ancestors(tip)

    def merge_base(self, a, b):
        anc_a = self.ancestors(a)
        # BFS from b (parents first) to find the nearest common ancestor
        queue = [b]
        seen = set()
        while queue:
            oid = queue.pop(0)
            if oid in seen:
                continue
            seen.add(oid)
            if oid in anc_a:
                return oid
            if self.objects.get(oid, (None,))[0] == "commit":
                queue.extend(self.commit_parents(oid))
        return None


class Forge:
    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}          # (owner, name) -> Repo
        self.next_id = 10000
        self.seq = 0             # global creation sequence (deterministic order)
        self.req_seq = 0

    def next_seq(self):
        self.seq += 1
        return self.seq

    def next_id_value(self):
        self.next_id += 1
        return self.next_id

    def create_repo(self, owner, name, private, description):
        key = (owner, name)
        if key in self.repos:
            raise Unprocessable("Repository already exists")
        repo = Repo(owner, name, self.next_id_value(), private, description, self.next_seq())
        self.repos[key] = repo
        return repo

    def get_repo(self, owner, name):
        repo = self.repos.get((owner, name))
        if repo is None:
            raise NotFound("Not Found")
        return repo

    def list_repos(self, owner):
        return sorted((r for (o, _), r in self.repos.items() if o == owner),
                      key=lambda r: r.created_seq)

    # ---- git object helpers shared by REST contents and merges
    def new_commit_epoch(self):
        return FIXED_EPOCH + self.next_seq()


FORGE = Forge()


def global_id(kind, key):
    raw = ("%s:%s" % (kind, key)).encode("utf-8")
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def decode_global_id(gid):
    try:
        padded = gid + "=" * (-len(gid) % 4)
        raw = base64.urlsafe_b64decode(padded.encode("ascii")).decode("utf-8")
        kind, _, key = raw.partition(":")
        return kind, key
    except Exception:
        return None, None


def user_json():
    return {
        "login": VIEWER_LOGIN, "id": VIEWER_ID, "node_id": global_id("User", VIEWER_LOGIN),
        "avatar_url": "https://example.invalid/avatar.png", "type": "User",
        "site_admin": False, "name": VIEWER_NAME, "email": VIEWER_EMAIL,
        "html_url": "https://example.invalid/" + VIEWER_LOGIN,
        "url": "/api/v3/users/" + VIEWER_LOGIN,
    }


def repo_json(repo):
    return {
        "id": repo.id, "node_id": global_id("Repository", repo.full_name),
        "name": repo.name, "full_name": repo.full_name,
        "owner": {"login": repo.owner, "id": VIEWER_ID, "type": "User",
                  "avatar_url": "https://example.invalid/avatar.png"},
        "private": repo.private, "description": repo.description,
        "default_branch": repo.default_branch, "fork": False,
        "created_at": FIXED_TIME, "updated_at": FIXED_TIME, "pushed_at": FIXED_TIME,
        "html_url": "https://example.invalid/" + repo.full_name,
        "url": "/api/v3/repos/" + repo.full_name,
        "has_issues": True, "has_projects": True, "has_wiki": True,
        "archived": False, "disabled": False, "visibility": "private" if repo.private else "public",
    }


def issue_json(repo, issue):
    return {
        "id": issue["id"], "node_id": issue["node_id"], "number": issue["number"],
        "title": issue["title"], "body": issue["body"], "state": issue["state"],
        "labels": [{"name": n, "color": repo.labels.get(n, {}).get("color", "ededed"),
                    "description": repo.labels.get(n, {}).get("description", "")}
                   for n in issue["labels"]],
        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
        "assignees": [], "comments": len(issue["comments"]),
        "created_at": FIXED_TIME, "updated_at": FIXED_TIME, "closed_at": None,
        "html_url": "https://example.invalid/%s/issues/%d" % (repo.full_name, issue["number"]),
        "url": "/api/v3/repos/%s/issues/%d" % (repo.full_name, issue["number"]),
        "repository_url": "/api/v3/repos/" + repo.full_name,
    }


def pr_json(repo, pr):
    base = {
        "id": pr["id"], "node_id": pr["node_id"], "number": pr["number"],
        "title": pr["title"], "body": pr["body"], "state": pr["state"],
        "merged": pr["merged"], "mergeable": pr["mergeable"],
        "merge_commit_sha": pr["merge_commit_sha"],
        "merged_at": FIXED_TIME if pr["merged"] else None,
        "head": {"ref": pr["head"], "sha": pr["head_sha"],
                 "label": "%s:%s" % (repo.owner, pr["head"]),
                 "repo": {"id": repo.id, "name": repo.name, "full_name": repo.full_name}},
        "base": {"ref": pr["base"], "sha": pr["base_sha"],
                 "label": "%s:%s" % (repo.owner, pr["base"]),
                 "repo": {"id": repo.id, "name": repo.name, "full_name": repo.full_name}},
        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
        "created_at": FIXED_TIME, "updated_at": FIXED_TIME, "closed_at": None,
        "html_url": "https://example.invalid/%s/pull/%d" % (repo.full_name, pr["number"]),
        "url": "/api/v3/repos/%s/pulls/%d" % (repo.full_name, pr["number"]),
    }
    return base


def pr_files(repo, pr):
    """Diff base tip tree vs head tip tree -> pull file entries."""
    base_tip = repo.ref_tip(pr["base"])
    head_tip = repo.ref_tip(pr["head"])
    base_files = {}
    head_files = {}
    if base_tip:
        _, tree = repo.tree_at(base_tip)
        base_files = repo.flatten_tree(tree)
    if head_tip:
        _, tree = repo.tree_at(head_tip)
        head_files = repo.flatten_tree(tree)
    out = []
    for path in sorted(set(base_files) | set(head_files)):
        b = base_files.get(path)
        h = head_files.get(path)
        if b is None and h is not None:
            blob = repo.objects[h[1]][1].decode("utf-8", "surrogateescape")
            additions = len(blob.splitlines())
            out.append({"filename": path, "status": "added", "additions": additions,
                        "deletions": 0, "changes": additions})
        elif h is None and b is not None:
            blob = repo.objects[b[1]][1].decode("utf-8", "surrogateescape")
            deletions = len(blob.splitlines())
            out.append({"filename": path, "status": "removed", "additions": 0,
                        "deletions": deletions, "changes": deletions})
        elif b is not None and h is not None and b[1] != h[1]:
            old = repo.objects[b[1]][1].decode("utf-8", "surrogateescape").splitlines()
            new = repo.objects[h[1]][1].decode("utf-8", "surrogateescape").splitlines()
            sm = difflib.SequenceMatcher(a=old, b=new, autojunk=False)
            additions = deletions = 0
            for tag, i1, i2, j1, j2 in sm.get_opcodes():
                if tag in ("insert", "replace"):
                    additions += j2 - j1
                if tag in ("delete", "replace"):
                    deletions += i2 - i1
            out.append({"filename": path, "status": "modified", "additions": additions,
                        "deletions": deletions, "changes": additions + deletions})
    return out


def pr_mergeable(repo, pr):
    """Three-way merge check. Returns (ok, result_files_or_None)."""
    base_tip = repo.ref_tip(pr["base"])
    head_tip = repo.ref_tip(pr["head"])
    if base_tip is None or head_tip is None:
        return False, None
    mb = repo.merge_base(head_tip, base_tip)
    if mb is None:
        # unrelated histories: squash takes the head tree wholesale
        _, tree = repo.tree_at(head_tip)
        return True, repo.flatten_tree(tree)
    _, mb_tree = repo.tree_at(mb)
    _, base_tree = repo.tree_at(base_tip)
    _, head_tree = repo.tree_at(head_tip)
    mb_files = repo.flatten_tree(mb_tree)
    base_files = repo.flatten_tree(base_tree)
    head_files = repo.flatten_tree(head_tree)
    result = dict(base_files)
    for path in sorted(set(mb_files) | set(base_files) | set(head_files)):
        m = mb_files.get(path)
        b = base_files.get(path)
        h = head_files.get(path)
        if h == m:
            continue  # head unchanged: keep base
        if b == m:
            # base unchanged: take head (or delete)
            if h is None:
                result.pop(path, None)
            else:
                result[path] = h
            continue
        if h == b:
            continue
        return False, None  # both changed differently
    return True, result


def do_merge(repo, pr, method):
    """Perform the merge. Returns merge commit oid, or None when conflicted."""
    ok, result_files = pr_mergeable(repo, pr)
    if not ok:
        return None
    base_tip = repo.ref_tip(pr["base"])
    head_tip = repo.ref_tip(pr["head"])
    tree_oid = repo.build_tree_from_files(result_files or {})
    epoch = FORGE.new_commit_epoch()
    ident = ident_line(VIEWER_NAME, VIEWER_EMAIL, epoch)
    if method == "squash":
        parents = [base_tip] if base_tip else []
        message = "Merge pull request #%d from %s\n\n%s\n" % (pr["number"], pr["head"], pr["title"])
    else:
        parents = [p for p in (base_tip, head_tip) if p]
        message = "Merge pull request #%d from %s\n\n%s\n" % (pr["number"], pr["head"], pr["title"])
    commit = repo.put_object("commit", build_commit(tree_oid, parents, ident, ident, message))
    repo.refs["refs/heads/" + pr["base"]] = commit
    pr["state"] = "closed"
    pr["merged"] = True
    pr["merge_commit_sha"] = commit
    pr["base_sha"] = commit
    return commit


# --------------------------------------------------------------------------- HTTP layer

EXPECTED_TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")


def _json_dumps(obj):
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    def log_message(self, *args):
        pass

    def setup(self):
        super().setup()
        # Without TCP_NODELAY the server's small header writes stall behind
        # Nagle while the client delays its ACK: ~40 ms per round trip, which
        # the four timed workloads all pay. Disable it on every connection.
        try:
            self.connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass

    # ---- plumbing
    def _req_id(self):
        with FORGE.lock:
            FORGE.req_seq += 1
            return "req-%08x" % FORGE.req_seq

    def send_json(self, status, obj, extra_headers=None):
        body = _json_dumps(obj) if obj is not None else b""
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-GitHub-Request-Id", self._req_id())
        self.send_header("X-OAuth-Scopes", "repo, read:org")
        if extra_headers:
            for k, v in extra_headers.items():
                self.send_header(k, v)
        self.end_headers()
        if body and self.command != "HEAD":
            self.wfile.write(body)

    def send_bytes(self, status, body, content_type, extra_headers=None):
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-GitHub-Request-Id", self._req_id())
        if extra_headers:
            for k, v in extra_headers.items():
                self.send_header(k, v)
        self.end_headers()
        if body and self.command != "HEAD":
            self.wfile.write(body)

    def send_no_content(self, status=204):
        self.send_response(status)
        self.send_header("Content-Length", "0")
        self.send_header("X-GitHub-Request-Id", self._req_id())
        self.end_headers()

    def read_body(self):
        """Read (and cache) the request body. The dispatcher always consumes
        the body up front: on a keep-alive connection an unread body would
        corrupt the next request line."""
        if getattr(self, "_body_cache", None) is not None:
            return self._body_cache
        length = self.headers.get("Content-Length")
        if not length:
            self._body_cache = b""
            return b""
        try:
            n = int(length)
        except ValueError:
            self._body_cache = b""
            return b""
        if n <= 0:
            self._body_cache = b""
            return b""
        self._body_cache = self.rfile.read(n)
        return self._body_cache

    def json_body(self):
        raw = self.read_body()
        if not raw:
            return {}, None
        try:
            val = json.loads(raw.decode("utf-8"))
        except Exception:
            return None, {"message": "Problems parsing JSON"}
        if not isinstance(val, dict):
            return None, {"message": "JSON body must be an object"}
        return val, None

    def raw_body(self):
        return self.read_body()

    def authed(self):
        """True when the Authorization header carries the trial token."""
        auth = self.headers.get("Authorization", "")
        if not auth.startswith("Bearer "):
            return False
        token = auth[7:].strip()
        if not token:
            return False
        if EXPECTED_TOKEN:
            return token == EXPECTED_TOKEN
        return True  # dev mode: no expected token configured

    def base_url(self):
        host = self.headers.get("Host", "127.0.0.1")
        return "http://%s" % host

    # ---- entry point
    def _dispatch(self):
        try:
            # Consume the body first so the keep-alive stream stays aligned
            # even when the route below answers without reading it.
            self._body_cache = None
            if self.command in ("POST", "PUT", "PATCH", "DELETE"):
                self.read_body()
            parsed = urllib.parse.urlparse(self.path)
            path = urllib.parse.unquote(parsed.path)
            query = urllib.parse.parse_qs(parsed.query, keep_blank_values=True)
            q = {k: v[0] for k, v in query.items()}
            if path == "/healthz" and self.command == "GET":
                self.send_json(200, {"ok": True})
                return
            if not self.authed():
                self.send_json(401, {"message": "Requires authentication"})
                return
            if path == "/api/graphql" or path.startswith("/api/graphql/"):
                self.handle_graphql()
                return
            if path == "/mcp":
                self.handle_mcp()
                return
            if path.startswith("/api/v3"):
                self.handle_rest(path[len("/api/v3"):], q)
                return
            m = re.match(r"^/([^/]+)/([^/]+)\.git(/.*)?$", path)
            if m:
                self.handle_git(m.group(1), m.group(2), m.group(3) or "", q)
                return
            self.send_json(404, {"message": "Not Found"})
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as exc:  # never leak a stack trace as HTML
            try:
                self.send_json(500, {"message": "Internal Server Error: %s" % exc})
            except Exception:
                pass

    do_GET = _dispatch
    do_POST = _dispatch
    do_PUT = _dispatch
    do_PATCH = _dispatch
    do_DELETE = _dispatch

    # ---- pagination
    def paginate(self, items, q, path):
        try:
            per_page = int(q.get("per_page", "30"))
        except ValueError:
            per_page = 30
        per_page = max(1, min(100, per_page))
        try:
            page = int(q.get("page", "1"))
        except ValueError:
            page = 1
        page = max(1, page)
        total = len(items)
        start = (page - 1) * per_page
        chunk = items[start:start + per_page]
        links = []
        base = self.base_url() + path
        if start + per_page < total:
            links.append('<%s?per_page=%d&page=%d>; rel="next"' % (base, per_page, page + 1))
            last = (total + per_page - 1) // per_page
            links.append('<%s?per_page=%d&page=%d>; rel="last"' % (base, per_page, last))
        if page > 1:
            links.append('<%s?per_page=%d&page=%d>; rel="prev"' % (base, per_page, page - 1))
            links.append('<%s?per_page=%d&page=1>; rel="first"' % (base, per_page))
        headers = {"Link": ", ".join(links)} if links else None
        return chunk, headers

    # ---- REST v3
    def handle_rest(self, sub, q):
        method = self.command
        parts = [p for p in sub.split("/") if p != ""]
        with FORGE.lock:
            try:
                self._rest(method, parts, q)
            except NotFound:
                self.send_json(404, {"message": "Not Found"})
            except Unprocessable as exc:
                self.send_json(422, {"message": str(exc)})
            except Conflict as exc:
                self.send_json(409, {"message": str(exc)})

    def _rest(self, method, parts, q):
        # API root
        if not parts:
            if method == "GET":
                self.send_json(200, {
                    "current_user_url": "/api/v3/user",
                    "current_user_authorizations_html_url": "/api/v3/authorizations",
                    "authorizations_url": "/api/v3/authorizations",
                    "rate_limit_url": "/api/v3/rate_limit",
                    "repository_url": "/api/v3/repos/{owner}/{repo}",
                    "user_url": "/api/v3/users/{username}",
                })
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        if parts == ["meta"]:
            if method == "GET":
                self.send_json(200, {"installed_version": "1.0.0", "verifiable_password_authentication": True})
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        if parts == ["rate_limit"]:
            if method == "GET":
                self.send_json(200, {"resources": {"core": {"limit": 5000, "remaining": 4999, "reset": 1767225600}},
                                     "rate": {"limit": 5000, "remaining": 4999, "reset": 1767225600}})
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        if parts == ["user"]:
            if method == "GET":
                self.send_json(200, user_json())
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        if parts == ["user", "repos"]:
            if method == "POST":
                body, err = self.json_body()
                if err is not None:
                    self.send_json(400, err)
                    return
                name = body.get("name")
                if not isinstance(name, str) or not name:
                    self.send_json(422, {"message": "name is required"})
                    return
                repo = FORGE.create_repo(VIEWER_LOGIN, name, bool(body.get("private", False)),
                                         body.get("description") or "")
                self.send_json(201, repo_json(repo))
            elif method == "GET":
                repos = FORGE.list_repos(VIEWER_LOGIN)
                chunk, headers = self.paginate([repo_json(r) for r in repos], q, "/api/v3/user/repos")
                self.send_json(200, chunk, headers)
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        if parts[0] == "users" and len(parts) == 2:
            if parts[1] == VIEWER_LOGIN and method == "GET":
                self.send_json(200, user_json())
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        if parts[0] != "repos" or len(parts) < 3:
            self.send_json(404, {"message": "Not Found"})
            return
        owner, name = parts[1], parts[2]
        if owner != VIEWER_LOGIN:
            self.send_json(404, {"message": "Not Found"})
            return
        rest = parts[3:]
        if not rest:
            repo = FORGE.get_repo(owner, name)
            if method == "GET":
                self.send_json(200, repo_json(repo))
            elif method == "PATCH":
                body, err = self.json_body()
                if err is not None:
                    self.send_json(400, err)
                    return
                if "description" in body:
                    repo.description = body["description"] if isinstance(body["description"], str) else repo.description
                if "name" in body and isinstance(body["name"], str) and body["name"]:
                    FORGE.repos.pop((owner, name))
                    repo.name = body["name"]
                    FORGE.repos[(owner, repo.name)] = repo
                self.send_json(200, repo_json(repo))
            elif method == "DELETE":
                self.read_body()
                FORGE.repos.pop((owner, name), None)
                self.send_no_content(204)
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        repo = FORGE.get_repo(owner, name)
        self._rest_repo(repo, rest, method, q)

    def _rest_repo(self, repo, rest, method, q):
        head = rest[0]
        if head == "branches":
            if len(rest) == 1:
                if method != "GET":
                    self.send_json(404, {"message": "Not Found"})
                    return
                out = []
                for refname in sorted(repo.refs):
                    if refname.startswith("refs/heads/"):
                        branch = refname[len("refs/heads/"):]
                        out.append({"name": branch, "commit": {"sha": repo.refs[refname]},
                                    "protected": False})
                self.send_json(200, out)
                return
            branch = "/".join(rest[1:])
            tip = repo.ref_tip(branch)
            if tip is None:
                self.send_json(404, {"message": "Not Found"})
                return
            if method == "GET":
                self.send_json(200, {"name": branch, "commit": {"sha": tip}, "protected": False})
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        if head == "git":
            if len(rest) >= 2 and rest[1] == "refs":
                if method == "POST" and len(rest) == 2:
                    body, err = self.json_body()
                    if err is not None:
                        self.send_json(400, err)
                        return
                    ref = body.get("ref", "")
                    sha = body.get("sha", "")
                    if not ref.startswith("refs/") or sha not in repo.objects:
                        self.send_json(422, {"message": "Invalid ref or sha"})
                        return
                    if ref in repo.refs:
                        self.send_json(422, {"message": "Reference already exists"})
                        return
                    repo.refs[ref] = sha
                    self.send_json(201, {"ref": ref, "object": {"sha": sha, "type": repo.objects[sha][0]}})
                    return
                if method == "GET" and len(rest) >= 3:
                    refname = "/".join(rest[2:])
                    oid = repo.refs.get(refname)
                    if oid is None:
                        self.send_json(404, {"message": "Not Found"})
                        return
                    self.send_json(200, {"ref": refname, "object": {"sha": oid, "type": repo.objects[oid][0]}})
                    return
                if method == "GET" and len(rest) == 2:
                    out = [{"ref": r, "object": {"sha": s, "type": repo.objects[s][0]}}
                           for r, s in sorted(repo.refs.items())]
                    self.send_json(200, out)
                    return
            self.send_json(404, {"message": "Not Found"})
            return
        if head == "commits":
            if method != "GET":
                self.send_json(404, {"message": "Not Found"})
                return
            ref = q.get("sha") or repo.default_branch
            tip = repo.resolve_ref(ref)
            if tip is None:
                self.send_json(200, [])
                return
            out = []
            for oid in repo.commits_from(tip):
                c = parse_commit(repo.objects[oid][1])
                out.append({"sha": oid,
                            "commit": {"message": c["message"],
                                       "author": {"name": VIEWER_NAME, "email": VIEWER_EMAIL, "date": FIXED_TIME},
                                       "committer": {"name": VIEWER_NAME, "email": VIEWER_EMAIL, "date": FIXED_TIME},
                                       "tree": {"sha": c["tree"]}},
                            "parents": [{"sha": p} for p in c["parents"]]})
            chunk, headers = self.paginate(out, q, "/api/v3/repos/%s/%s/commits" % (repo.owner, repo.name))
            self.send_json(200, chunk, headers)
            return
        if head == "contents":
            self._rest_contents(repo, "/".join(rest[1:]), method, q)
            return
        if head == "labels":
            if method == "POST":
                body, err = self.json_body()
                if err is not None:
                    self.send_json(400, err)
                    return
                name = body.get("name")
                if not isinstance(name, str) or not name:
                    self.send_json(422, {"message": "name is required"})
                    return
                label = {"name": name, "color": body.get("color", "ededed"),
                         "description": body.get("description", "")}
                repo.labels[name] = label
                self.send_json(201, label)
            elif method == "GET":
                self.send_json(200, list(repo.labels.values()))
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        if head == "issues":
            self._rest_issues(repo, rest[1:], method, q)
            return
        if head == "pulls":
            self._rest_pulls(repo, rest[1:], method, q)
            return
        self.send_json(404, {"message": "Not Found"})

    def _rest_contents(self, repo, path, method, q):
        if method == "GET":
            ref = q.get("ref")
            resolved = repo.tree_at(ref)
            if resolved is None:
                self.send_json(404, {"message": "Not Found"})
                return
            _commit, tree_oid = resolved
            files = repo.flatten_tree(tree_oid)
            if path in files:
                _mode, blob_oid = files[path]
                data = repo.objects[blob_oid][1]
                name = path.split("/")[-1]
                self.send_json(200, {
                    "type": "file", "encoding": "base64", "size": len(data),
                    "name": name, "path": path, "sha": blob_oid,
                    "content": base64.b64encode(data).decode("ascii"),
                    "url": "/api/v3/repos/%s/%s/contents/%s" % (repo.owner, repo.name, path),
                })
                return
            # directory listing: immediate children of path ("" = root)
            prefix = "" if path == "" else path + "/"
            children = {}
            for fpath, (_mode, blob_oid) in files.items():
                if not fpath.startswith(prefix):
                    continue
                rest_path = fpath[len(prefix):]
                first = rest_path.split("/")[0]
                if "/" in rest_path:
                    children[first] = {"type": "dir", "name": first, "path": prefix + first,
                                       "sha": ""}
                else:
                    children[first] = {"type": "file", "name": first, "path": fpath,
                                       "sha": blob_oid, "size": len(repo.objects[blob_oid][1])}
            if path != "" and not children:
                self.send_json(404, {"message": "Not Found"})
                return
            # directory shas: compute the subtree oid when possible
            out = []
            for child in sorted(children.values(), key=lambda c: c["name"]):
                if child["type"] == "dir":
                    # find the subtree oid by walking the tree
                    node = tree_oid
                    for seg in (prefix + child["name"]).split("/"):
                        found = None
                        for mode, nm, oid in parse_tree(repo.objects[node][1]):
                            if nm == seg:
                                found = oid
                                break
                        if found is None:
                            break
                        node = found
                    child["sha"] = node if found else ""
                out.append(child)
            self.send_json(200, out)
            return
        if method in ("PUT", "DELETE"):
            body, err = self.json_body()
            if err is not None:
                self.send_json(400, err)
                return
            branch = body.get("branch") or repo.default_branch
            message = body.get("message") or "update"
            if method == "PUT":
                content_b64 = body.get("content")
                if not isinstance(content_b64, str):
                    self.send_json(422, {"message": "content is required"})
                    return
                try:
                    data = base64.b64decode(content_b64, validate=False)
                except Exception:
                    self.send_json(422, {"message": "content is not valid base64"})
                    return
                # current state on this branch
                tip = repo.ref_tip(branch)
                existing = None
                if tip is not None:
                    _, tree = repo.tree_at(tip)
                    existing = repo.flatten_tree(tree).get(path)
                given_sha = body.get("sha")
                if existing is not None:
                    if given_sha is None:
                        self.send_json(422, {"message": "sha is required to update a file"})
                        return
                    if given_sha != existing[1]:
                        self.send_json(409, {"message": "sha does not match the current blob"})
                        return
                    status = 200
                else:
                    if given_sha is not None:
                        self.send_json(422, {"message": "sha given but the file does not exist"})
                        return
                    status = 201
                blob_oid = repo.put_object("blob", data)
                commit = repo.commit_for_path(branch, path, blob_oid, message, FORGE.new_commit_epoch())
                self.send_json(status, {
                    "content": {"name": path.split("/")[-1], "path": path, "sha": blob_oid,
                                "size": len(data), "encoding": "base64",
                                "content": content_b64},
                    "commit": {"sha": commit, "message": message},
                })
                return
            # DELETE
            tip = repo.ref_tip(branch)
            if tip is None:
                self.send_json(404, {"message": "Not Found"})
                return
            _, tree = repo.tree_at(tip)
            existing = repo.flatten_tree(tree).get(path)
            if existing is None:
                self.send_json(404, {"message": "Not Found"})
                return
            given_sha = body.get("sha")
            if given_sha is not None and given_sha != existing[1]:
                self.send_json(409, {"message": "sha does not match the current blob"})
                return
            commit = repo.commit_for_path(branch, path, None, message, FORGE.new_commit_epoch())
            self.send_json(200, {"content": None, "commit": {"sha": commit, "message": message}})
            return
        self.send_json(404, {"message": "Not Found"})

    def _rest_issues(self, repo, rest, method, q):
        if not rest:
            if method == "GET":
                state = q.get("state", "open")
                sort = q.get("sort", "created")
                direction = q.get("direction", "desc")
                items = list(repo.issues.values())
                if state != "all":
                    items = [i for i in items if i["state"] == state]
                reverse = direction != "asc"
                items.sort(key=lambda i: i["seq"], reverse=reverse)
                chunk, headers = self.paginate([issue_json(repo, i) for i in items], q,
                                               "/api/v3/repos/%s/%s/issues" % (repo.owner, repo.name))
                self.send_json(200, chunk, headers)
            elif method == "POST":
                body, err = self.json_body()
                if err is not None:
                    self.send_json(400, err)
                    return
                title = body.get("title")
                if not isinstance(title, str) or not title:
                    self.send_json(422, {"message": "title is required"})
                    return
                labels = body.get("labels") or []
                label_names = []
                for lab in labels:
                    nm = lab.get("name") if isinstance(lab, dict) else lab
                    if nm not in repo.labels:
                        self.send_json(422, {"message": "Label '%s' does not exist" % nm})
                        return
                    label_names.append(nm)
                number = repo.next_number
                repo.next_number += 1
                issue = {"id": FORGE.next_id_value(), "node_id": global_id("Issue", "%s#%d" % (repo.full_name, number)),
                         "number": number, "title": title, "body": body.get("body") or "",
                         "state": "open", "labels": label_names, "comments": [],
                         "seq": FORGE.next_seq()}
                repo.issues[number] = issue
                self.send_json(201, issue_json(repo, issue))
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        try:
            number = int(rest[0])
        except ValueError:
            self.send_json(404, {"message": "Not Found"})
            return
        issue = repo.issues.get(number)
        if issue is None:
            self.send_json(404, {"message": "Not Found"})
            return
        if len(rest) == 1:
            if method == "GET":
                self.send_json(200, issue_json(repo, issue))
            elif method == "PATCH":
                body, err = self.json_body()
                if err is not None:
                    self.send_json(400, err)
                    return
                if body.get("state") in ("open", "closed"):
                    issue["state"] = body["state"]
                if isinstance(body.get("title"), str):
                    issue["title"] = body["title"]
                if isinstance(body.get("body"), str):
                    issue["body"] = body["body"]
                self.send_json(200, issue_json(repo, issue))
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        if rest[1] == "comments":
            if method == "GET":
                self.send_json(200, [{"id": c["id"], "node_id": c["node_id"], "body": c["body"],
                                      "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
                                      "created_at": FIXED_TIME, "updated_at": FIXED_TIME}
                                     for c in issue["comments"]])
            elif method == "POST":
                body, err = self.json_body()
                if err is not None:
                    self.send_json(400, err)
                    return
                text = body.get("body")
                if not isinstance(text, str):
                    self.send_json(422, {"message": "body is required"})
                    return
                comment = {"id": FORGE.next_id_value(),
                           "node_id": global_id("IssueComment", "%s#%d:%d" % (repo.full_name, number, len(issue["comments"]) + 1)),
                           "body": text}
                issue["comments"].append(comment)
                self.send_json(201, {"id": comment["id"], "node_id": comment["node_id"], "body": text,
                                     "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
                                     "created_at": FIXED_TIME, "updated_at": FIXED_TIME})
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        self.send_json(404, {"message": "Not Found"})

    def _rest_pulls(self, repo, rest, method, q):
        if not rest:
            if method == "GET":
                state = q.get("state", "open")
                items = list(repo.pulls.values())
                if state == "open":
                    items = [p for p in items if p["state"] == "open"]
                elif state == "closed":
                    items = [p for p in items if p["state"] == "closed"]
                items.sort(key=lambda p: p["number"])
                chunk, headers = self.paginate([pr_json(repo, p) for p in items], q,
                                               "/api/v3/repos/%s/%s/pulls" % (repo.owner, repo.name))
                self.send_json(200, chunk, headers)
            elif method == "POST":
                body, err = self.json_body()
                if err is not None:
                    self.send_json(400, err)
                    return
                head = body.get("head")
                base = body.get("base") or repo.default_branch
                title = body.get("title")
                if not isinstance(head, str) or not isinstance(title, str):
                    self.send_json(422, {"message": "head and title are required"})
                    return
                head_sha = repo.ref_tip(head)
                base_sha = repo.ref_tip(base)
                if head_sha is None or base_sha is None:
                    self.send_json(422, {"message": "head or base branch does not exist"})
                    return
                for p in repo.pulls.values():
                    if p["head"] == head and p["base"] == base and p["state"] == "open":
                        self.send_json(422, {"message": "A pull request already exists for this branch"})
                        return
                number = repo.next_number
                repo.next_number += 1
                pr = {"id": FORGE.next_id_value(), "node_id": global_id("PullRequest", "%s#%d" % (repo.full_name, number)),
                      "number": number, "title": title, "body": body.get("body") or "",
                      "state": "open", "merged": False, "mergeable": True,
                      "merge_commit_sha": None, "head": head, "base": base,
                      "head_sha": head_sha, "base_sha": base_sha}
                ok, _ = pr_mergeable(repo, pr)
                pr["mergeable"] = ok
                repo.pulls[number] = pr
                self.send_json(201, pr_json(repo, pr))
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        try:
            number = int(rest[0])
        except ValueError:
            self.send_json(404, {"message": "Not Found"})
            return
        pr = repo.pulls.get(number)
        if pr is None:
            self.send_json(404, {"message": "Not Found"})
            return
        if len(rest) == 1:
            if method == "GET":
                self.send_json(200, pr_json(repo, pr))
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        if rest[1] == "files":
            if method == "GET":
                self.send_json(200, pr_files(repo, pr))
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        if rest[1] == "merge":
            if method == "PUT":
                body, err = self.json_body()
                if err is not None:
                    self.send_json(400, err)
                    return
                if pr["state"] != "open":
                    self.send_json(405, {"message": "Pull request is not open"})
                    return
                method_name = (body.get("merge_method") or "merge").lower()
                commit = do_merge(repo, pr, method_name)
                if commit is None:
                    self.send_json(405, {"message": "Merge conflict"})
                    return
                self.send_json(200, {"sha": commit, "merged": True,
                                     "message": "Pull request successfully merged"})
            else:
                self.send_json(404, {"message": "Not Found"})
            return
        self.send_json(404, {"message": "Not Found"})


# --------------------------------------------------------------------------- git smart HTTP

def _sideband_pack(pack):
    """Wrap pack bytes in sideband-64k pkt-lines (band 1), chunked."""
    out = bytearray()
    for i in range(0, len(pack), 32768):
        out += pkt_line(b"\x01" + pack[i:i + 32768])
    return bytes(out)


def _closure(repo, tips):
    """All objects reachable from tips (commits, tags, trees, blobs)."""
    out = {}
    stack = list(tips)
    while stack:
        oid = stack.pop()
        if oid in out:
            continue
        obj = repo.objects.get(oid)
        if obj is None:
            continue
        otype, data = obj
        out[oid] = (otype, data)
        if otype == "commit":
            stack.append(repo.commit_tree(oid))
            stack.extend(repo.commit_parents(oid))
        elif otype == "tree":
            stack.extend(e[2] for e in parse_tree(data))
        elif otype == "tag":
            stack.append(parse_tag(data)["object"])
    return out


def _peel_target(repo, oid):
    """Follow tag objects to a commit oid (or return oid)."""
    seen = set()
    while oid not in seen:
        seen.add(oid)
        obj = repo.objects.get(oid)
        if obj is None or obj[0] != "tag":
            return oid
        oid = parse_tag(obj[1])["object"]
    return oid


def _compute_fetch(repo, wants, haves, shallow_known, depth):
    """Return (send_objects dict, new_shallow list, unshallow list).

    send_objects: {oid: (otype, data)} to pack.
    """
    have_set = set(haves)
    # expand tag wants to their target commits (tags themselves still sent)
    tag_wants = []
    commit_wants = []
    for w in wants:
        obj = repo.objects.get(w)
        if obj is not None and obj[0] == "tag":
            tag_wants.append(w)
            commit_wants.append(_peel_target(repo, w))
        elif obj is not None:
            commit_wants.append(w)
    included = set()       # commit oids to send
    boundary = set()       # included commits whose parents are cut
    if depth is None:
        # walk from wants, stopping at haves
        stack = list(commit_wants)
        while stack:
            c = stack.pop()
            if c in included or c in have_set:
                continue
            obj = repo.objects.get(c)
            if obj is None or obj[0] != "commit":
                continue
            included.add(c)
            stack.extend(repo.commit_parents(c))
    else:
        levels = {}
        queue = list(dict.fromkeys(commit_wants))  # dedup, keep order
        for w in queue:
            levels[w] = 0
        qi = 0
        while qi < len(queue):
            c = queue[qi]
            qi += 1
            lvl = levels[c]
            if lvl >= depth:
                continue
            obj = repo.objects.get(c)
            if obj is None or obj[0] != "commit":
                continue
            if c not in have_set:
                included.add(c)
            for p in repo.commit_parents(c):
                if p not in levels:
                    levels[p] = lvl + 1
                    queue.append(p)
        for c in included:
            for p in repo.commit_parents(c):
                if p not in included and p not in have_set:
                    boundary.add(c)
                    break
    # objects to send: closure over included commits + tag wants.
    # With a depth limit the closure must NOT walk parents: only the
    # included commits' own trees/blobs travel.
    if depth is None:
        send = _closure(repo, list(included) + tag_wants)
    else:
        send = {}
        for c in included:
            obj = repo.objects.get(c)
            if obj is None:
                continue
            send[c] = obj
            send.update(_tree_closure(repo, repo.commit_tree(c)))
        for t in tag_wants:
            obj = repo.objects.get(t)
            if obj is not None:
                send[t] = obj
    # exclude anything the client already holds
    if have_set:
        held = _held_closure(repo, [h for h in have_set if h in repo.objects], shallow_known)
        for oid in list(send):
            if oid in held:
                del send[oid]
    # unshallow: previously shallow commits now complete
    unshallow = []
    for s in shallow_known:
        obj = repo.objects.get(s)
        if obj is None or obj[0] != "commit":
            continue
        parents = repo.commit_parents(s)
        if all(p in included or p in have_set for p in parents):
            unshallow.append(s)
    return send, sorted(boundary), sorted(unshallow)


def _held_closure(repo, haves, shallow_known):
    """Objects the client already holds: the closure of its haves, but never
    descending past a commit the client named as a shallow boundary (it holds
    that commit and its tree, not its parents)."""
    out = {}
    stop = set(shallow_known)
    stack = list(haves)
    while stack:
        oid = stack.pop()
        if oid in out:
            continue
        obj = repo.objects.get(oid)
        if obj is None:
            continue
        otype, data = obj
        out[oid] = (otype, data)
        if otype == "commit":
            stack.append(repo.commit_tree(oid))
            if oid not in stop:
                stack.extend(repo.commit_parents(oid))
        elif otype == "tree":
            stack.extend(e[2] for e in parse_tree(data))
        elif otype == "tag":
            stack.append(parse_tag(data)["object"])
    return out


def _tree_closure(repo, tree_oid):
    """tree oid -> {oid: (otype, data)} for the tree and everything under it."""
    out = {}
    stack = [tree_oid]
    while stack:
        oid = stack.pop()
        if oid in out:
            continue
        obj = repo.objects.get(oid)
        if obj is None:
            continue
        otype, data = obj
        out[oid] = (otype, data)
        if otype == "tree":
            stack.extend(e[2] for e in parse_tree(data))
    return out


def _sorted_pack_objects(send):
    rank = {"commit": 0, "tag": 1, "tree": 2, "blob": 3}
    items = sorted(send.items(), key=lambda kv: (rank.get(kv[1][0], 4), kv[0]))
    return [(otype, data) for _oid, (otype, data) in items]


def _ref_lines_v0(repo, capabilities):
    """v0 advertisement ref lines (without the # service preamble)."""
    lines = []
    refs = sorted(repo.refs.items())
    head_tip = repo.refs.get("refs/heads/" + repo.default_branch)
    first = True
    if head_tip is not None:
        lines.append("%s HEAD\0%s\n" % (head_tip, capabilities))
        first = False
    for refname, oid in refs:
        if refname == "refs/heads/" + repo.default_branch and head_tip is not None:
            pass  # still listed below as its own line
        cap = ""
        if first:
            cap = "\0" + capabilities
            first = False
        lines.append("%s %s%s\n" % (oid, refname, cap))
        # peeled tag line
        obj = repo.objects.get(oid)
        if refname.startswith("refs/tags/") and obj is not None and obj[0] == "tag":
            target = _peel_target(repo, oid)
            lines.append("%s %s^{}\n" % (target, refname))
    if first:
        lines.append("%s capabilities^{}\0%s\n" % (ZERO_OID, capabilities))
    return lines


def _is_ancestor_or_equal(repo, anc, tip):
    if anc == tip:
        return True
    return repo.is_ancestor(anc, tip)


class GitMixin:
    def handle_git(self, owner, repo_name, suffix, q):
        with FORGE.lock:
            try:
                if owner != VIEWER_LOGIN:
                    raise NotFound("Not Found")
                repo = FORGE.get_repo(owner, repo_name)
            except NotFound:
                self.send_json(404, {"message": "Not Found"})
                return
            try:
                if suffix == "/info/refs":
                    self._git_info_refs(repo, q)
                elif suffix == "/git-upload-pack" and self.command == "POST":
                    self._git_upload_pack(repo)
                elif suffix == "/git-receive-pack" and self.command == "POST":
                    self._git_receive_pack(repo)
                else:
                    self.send_json(404, {"message": "Not Found"})
            except ValueError as exc:
                self.send_json(400, {"message": "bad request: %s" % exc})
            except Exception as exc:
                self.send_json(500, {"message": "Internal Server Error: %s" % exc})

    def _git_info_refs(self, repo, q):
        service = q.get("service", "")
        if service not in ("git-upload-pack", "git-receive-pack"):
            self.send_json(400, {"message": "unknown service"})
            return
        want_v2 = (self.headers.get("Git-Protocol", "") == "version=2" and service == "git-upload-pack")
        ctype = "application/x-%s-advertisement" % service
        out = bytearray()
        out += pkt_line("# service=%s\n" % service)
        out += pkt_flush()
        if want_v2:
            out += pkt_line("version 2\n")
            out += pkt_line("ls-refs=unborn\n")
            out += pkt_line("fetch=shallow wait-for-done\n")
            out += pkt_line("object-format=sha1\n")
            out += pkt_line("agent=%s\n" % AGENT)
            out += pkt_flush()
        else:
            if service == "git-upload-pack":
                caps = ("symref=HEAD:refs/heads/%s side-band-64k thin-pack ofs-delta shallow "
                        "multi_ack_detailed agent=%s" % (repo.default_branch, AGENT))
            else:
                caps = ("symref=HEAD:refs/heads/%s report-status side-band-64k delete-refs "
                        "ofs-delta agent=%s" % (repo.default_branch, AGENT))
            for line in _ref_lines_v0(repo, caps):
                out += pkt_line(line)
            out += pkt_flush()
        self.send_bytes(200, bytes(out), ctype)

    def _git_upload_pack(self, repo):
        body = self.raw_body()
        want_v2 = self.headers.get("Git-Protocol", "") == "version=2"
        ctype = "application/x-git-upload-pack-result"
        packets = decode_pkt_lines(body)
        if want_v2:
            self._git_fetch_v2(repo, packets, ctype)
        else:
            self._git_fetch_v0(repo, packets, ctype)

    def _parse_v2_command(self, packets):
        """Parse a v2 command request. Returns (command, args list of str)."""
        command = None
        args = []
        seen_delim = False
        for kind, payload in packets:
            if kind == "flush":
                break
            if kind == "delim":
                seen_delim = True
                continue
            if kind != "data":
                continue
            text = payload.decode("utf-8", "surrogateescape")
            if not seen_delim and text.startswith("command="):
                command = text[len("command="):].strip()
            elif seen_delim:
                args.append(text.strip())
        return command, args

    def _git_fetch_v2(self, repo, packets, ctype):
        command, args = self._parse_v2_command(packets)
        out = bytearray()
        if command == "ls-refs":
            peel = "peel" in args
            symrefs = "symrefs" in args
            unborn = "unborn" in args
            prefixes = [a[len("ref-prefix "):] for a in args if a.startswith("ref-prefix ")]
            lines = []
            head_tip = repo.refs.get("refs/heads/" + repo.default_branch)
            head_line = None
            if head_tip is not None:
                head_line = "%s HEAD" % head_tip
                if symrefs:
                    head_line += " symref-target:refs/heads/%s" % repo.default_branch
            elif unborn:
                head_line = "unborn HEAD"
                if symrefs:
                    head_line += " symref-target:refs/heads/%s" % repo.default_branch
            if head_line and (not prefixes or any("HEAD".startswith(p) or p == "" for p in prefixes)):
                lines.append(head_line + "\n")
            for refname in sorted(repo.refs):
                if prefixes and not any(refname.startswith(p) for p in prefixes):
                    continue
                oid = repo.refs[refname]
                line = "%s %s" % (oid, refname)
                if peel:
                    obj = repo.objects.get(oid)
                    if obj is not None and obj[0] == "tag":
                        line += " peeled:" + _peel_target(repo, oid)
                lines.append(line + "\n")
            for line in lines:
                out += pkt_line(line)
            out += pkt_flush()
            self.send_bytes(200, bytes(out), ctype)
            return
        if command != "fetch":
            # unknown command: empty result
            out += pkt_flush()
            self.send_bytes(200, bytes(out), ctype)
            return
        wants, haves, shallow_known, depth = [], [], [], None
        for a in args:
            if a.startswith("want "):
                wants.append(a[5:].strip())
            elif a.startswith("have "):
                haves.append(a[5:].strip())
            elif a.startswith("shallow "):
                shallow_known.append(a[8:].strip())
            elif a.startswith("deepen "):
                try:
                    depth = int(a[7:].strip())
                except ValueError:
                    pass
        send, new_shallow, unshallow = _compute_fetch(repo, wants, haves, shallow_known, depth)
        out += pkt_line("acknowledgments\n")
        out += pkt_line("NAK\n")
        out += pkt_delim()
        if new_shallow or unshallow:
            out += pkt_line("shallow-info\n")
            for s in new_shallow:
                out += pkt_line("shallow %s\n" % s)
            for s in unshallow:
                out += pkt_line("unshallow %s\n" % s)
            out += pkt_delim()
        if send:
            pack = write_pack(_sorted_pack_objects(send))
            out += pkt_line("packfile\n")
            out += _sideband_pack(pack)
        out += pkt_flush()
        self.send_bytes(200, bytes(out), ctype)

    def _git_fetch_v0(self, repo, packets, ctype):
        wants, haves, shallow_known, depth = [], [], [], None
        section = 0  # 0 = wants, 1 = haves
        for kind, payload in packets:
            if kind == "flush":
                section = 1
                continue
            if kind != "data":
                continue
            text = payload.decode("utf-8", "surrogateescape").strip()
            if section == 0:
                if text.startswith("want "):
                    wants.append(text[5:].split(" ")[0])
                elif text.startswith("shallow "):
                    shallow_known.append(text[8:].strip())
                elif text.startswith("deepen "):
                    try:
                        depth = int(text[7:].strip())
                    except ValueError:
                        pass
            else:
                if text.startswith("have "):
                    haves.append(text[5:].strip())
        send, new_shallow, unshallow = _compute_fetch(repo, wants, haves, shallow_known, depth)
        out = bytearray()
        out += pkt_line("NAK\n")
        for s in new_shallow:
            out += pkt_line("shallow %s\n" % s)
        for s in unshallow:
            out += pkt_line("unshallow %s\n" % s)
        if send:
            pack = write_pack(_sorted_pack_objects(send))
            out += _sideband_pack(pack)
        out += pkt_flush()
        self.send_bytes(200, bytes(out), ctype)

    def _git_receive_pack(self, repo):
        body = self.raw_body()
        ctype = "application/x-git-receive-pack-result"
        # split pkt-lines (commands) from the pack: decode until flush, rest is pack
        commands = []
        capabilities = []
        sideband = False
        pack = b""
        try:
            i = 0
            n = len(body)
            while i < n:
                if i + 4 > n:
                    raise ValueError("truncated pkt-line")
                ln = int(body[i:i + 4].decode("ascii"), 16)
                if ln == 0:
                    i += 4
                    pack = body[i:]
                    break
                if ln < 4 or i + ln > n:
                    raise ValueError("bad pkt-line")
                payload = body[i + 4:i + ln]
                i += ln
                text = payload.decode("utf-8", "surrogateescape")
                if "\x00" in text:
                    line, _, caps = text.partition("\x00")
                    capabilities = caps.strip().split(" ")
                else:
                    line = text
                line = line.rstrip("\n")
                parts = line.split(" ")
                if len(parts) >= 3:
                    commands.append((parts[0], parts[1], parts[2]))
            sideband = "side-band-64k" in capabilities
        except ValueError:
            # malformed command list: report unpack failure, keep serving
            report = "unpack bad command list\n"
            for _c in commands:
                report += "ng %s unpacker error\n" % _c[2]
            self._send_push_report(report, sideband, ctype)
            return
        unpack_error = None
        if pack:
            try:
                objects, _nd = read_pack(pack, resolve_base=lambda oid: repo.objects.get(oid))
                for oid, otype, data in objects:
                    repo.put_object(otype, data)
            except ValueError as exc:
                unpack_error = str(exc)
        report_lines = []
        if unpack_error is not None:
            report_lines.append("unpack %s\n" % unpack_error)
            for _old, _new, ref in commands:
                report_lines.append("ng %s unpacker error\n" % ref)
        else:
            report_lines.append("unpack ok\n")
            for old, new, ref in commands:
                current = repo.refs.get(ref)
                if new == ZERO_OID:
                    # delete
                    if current is None:
                        report_lines.append("ng %s remote ref does not exist\n" % ref)
                    elif old != ZERO_OID and old != current:
                        report_lines.append("ng %s stale info\n" % ref)
                    else:
                        del repo.refs[ref]
                        report_lines.append("ok %s\n" % ref)
                    continue
                if new not in repo.objects:
                    report_lines.append("ng %s missing object\n" % ref)
                    continue
                if old == ZERO_OID:
                    # create
                    if current is not None:
                        report_lines.append("ng %s already exists\n" % ref)
                    else:
                        repo.refs[ref] = new
                        report_lines.append("ok %s\n" % ref)
                    continue
                # update
                if current is None:
                    report_lines.append("ng %s remote ref does not exist\n" % ref)
                elif old != current:
                    report_lines.append("ng %s stale info\n" % ref)
                elif ref.startswith("refs/heads/"):
                    new_obj = repo.objects.get(new)
                    if new_obj is not None and new_obj[0] == "commit" and not _is_ancestor_or_equal(repo, current, new):
                        report_lines.append("ng %s non-fast-forward\n" % ref)
                    else:
                        repo.refs[ref] = new
                        report_lines.append("ok %s\n" % ref)
                else:
                    repo.refs[ref] = new
                    report_lines.append("ok %s\n" % ref)
        self._send_push_report("".join(report_lines), sideband, ctype)

    def _send_push_report(self, report, sideband, ctype):
        out = bytearray()
        if sideband:
            for line in report.splitlines(keepends=True):
                out += pkt_line(b"\x01" + line.encode("utf-8"))
        else:
            for line in report.splitlines(keepends=True):
                out += pkt_line(line)
        out += pkt_flush()
        self.send_bytes(200, bytes(out), ctype)


# --------------------------------------------------------------------------- GraphQL v4
# --- tiny GraphQL parser (documents gh / github-mcp-server send) ---

_TOKEN_RE = re.compile(r"""
    (?P<ws>\s+)
  | (?P<ellipsis>\.\.\.)
  | (?P<punct>[{}()\[\]:!$,=@])
  | (?P<string>"(?:\\.|[^"\\])*")
  | (?P<number>-?\d+(?:\.\d+)?)
  | (?P<name>[_A-Za-z][_A-Za-z0-9]*)
""", re.VERBOSE)


def _tokenize(text):
    tokens = []
    i = 0
    while i < len(text):
        m = _TOKEN_RE.match(text, i)
        if not m:
            raise ValueError("cannot tokenize GraphQL at %d" % i)
        i = m.end()
        kind = m.lastgroup
        if kind == "ws":
            continue
        tokens.append((kind, m.group()))
    tokens.append(("eof", ""))
    return tokens


class _GQLParser:
    def __init__(self, text):
        self.tokens = _tokenize(text)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def next(self):
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def expect(self, value):
        kind, text = self.next()
        if text != value:
            raise ValueError("expected %r, got %r" % (value, text))

    def parse(self):
        doc = {"operations": [], "fragments": {}}
        while self.peek()[0] != "eof":
            kind, text = self.peek()
            if text == "fragment":
                self.next()
                name = self.next()[1]
                self.expect("on")
                type_name = self.next()[1]
                sel = self.parse_selection_set()
                doc["fragments"][name] = (type_name, sel)
            else:
                op_type = "query"
                if text in ("query", "mutation", "subscription"):
                    op_type = self.next()[1]
                name = None
                if self.peek()[0] == "name":
                    name = self.next()[1]
                var_defs = {}
                if self.peek()[1] == "(":
                    var_defs = self.parse_var_defs()
                # skip directives
                while self.peek()[1] == "@":
                    self.next()
                    self.next()
                    if self.peek()[1] == "(":
                        self.parse_arguments()
                sel = self.parse_selection_set()
                doc["operations"].append({"type": op_type, "name": name,
                                          "var_defs": var_defs, "selection": sel})
        return doc

    def parse_var_defs(self):
        defs = {}
        self.expect("(")
        while self.peek()[1] != ")":
            self.expect("$")
            name = self.next()[1]
            self.expect(":")
            type_name = self.parse_type()
            default = None
            if self.peek()[1] == "=":
                self.next()
                default = self.parse_value()
            defs[name] = default
            if self.peek()[1] == ",":
                self.next()
        self.expect(")")
        return defs

    def parse_type(self):
        if self.peek()[1] == "[":
            self.next()
            inner = self.parse_type()
            self.expect("]")
            t = "[%s]" % inner
        else:
            t = self.next()[1]
        if self.peek()[1] == "!":
            self.next()
            t += "!"
        return t

    def parse_selection_set(self):
        self.expect("{")
        sels = []
        while self.peek()[1] != "}":
            sels.append(self.parse_selection())
        self.expect("}")
        return sels

    def parse_selection(self):
        if self.peek()[1] == "...":
            self.next()
            if self.peek()[1] == "on":
                self.next()
                type_name = self.next()[1]
                # directives
                while self.peek()[1] == "@":
                    self.next()
                    self.next()
                    if self.peek()[1] == "(":
                        self.parse_arguments()
                return {"kind": "inline", "type": type_name,
                        "selection": self.parse_selection_set()}
            name = self.next()[1]
            while self.peek()[1] == "@":
                self.next()
                self.next()
                if self.peek()[1] == "(":
                    self.parse_arguments()
            return {"kind": "spread", "name": name}
        name = self.next()[1]
        alias = None
        if self.peek()[1] == ":":
            self.next()
            alias = name
            name = self.next()[1]
        args = {}
        if self.peek()[1] == "(":
            args = self.parse_arguments()
        while self.peek()[1] == "@":
            self.next()
            self.next()
            if self.peek()[1] == "(":
                self.parse_arguments()
        sub = None
        if self.peek()[1] == "{":
            sub = self.parse_selection_set()
        return {"kind": "field", "name": name, "alias": alias or name,
                "args": args, "selection": sub}

    def parse_arguments(self):
        args = {}
        self.expect("(")
        while self.peek()[1] != ")":
            name = self.next()[1]
            self.expect(":")
            args[name] = self.parse_value()
            if self.peek()[1] == ",":
                self.next()
        self.expect(")")
        return args

    def parse_value(self):
        kind, text = self.next()
        if kind == "punct" and text == "$":
            return ("var", self.next()[1])
        if kind == "string":
            return json.loads(text)
        if kind == "number":
            return float(text) if "." in text else int(text)
        if kind == "punct" and text == "[":
            vals = []
            while not (self.peek()[0] == "punct" and self.peek()[1] == "]"):
                vals.append(self.parse_value())
                if self.peek()[1] == ",":
                    self.next()
            self.expect("]")
            return vals
        if kind == "punct" and text == "{":
            obj = {}
            while not (self.peek()[0] == "punct" and self.peek()[1] == "}"):
                key = self.next()[1]
                self.expect(":")
                obj[key] = self.parse_value()
                if self.peek()[1] == ",":
                    self.next()
            self.expect("}")
            return obj
        if kind == "name":
            if text == "true":
                return True
            if text == "false":
                return False
            if text == "null":
                return None
            return ("enum", text)
        raise ValueError("unexpected value token %r" % text)


def _resolve_value(value, variables):
    if isinstance(value, tuple) and value and value[0] == "var":
        return variables.get(value[1])
    if isinstance(value, tuple) and value and value[0] == "enum":
        return value[1]
    if isinstance(value, list):
        return [_resolve_value(v, variables) for v in value]
    if isinstance(value, dict):
        return {k: _resolve_value(v, variables) for k, v in value.items()}
    return value


# --- GraphQL schema data ---

_ISSUE_FIELDS = ["id", "number", "title", "state", "body", "author", "createdAt",
                 "updatedAt", "closedAt", "comments", "labels", "url", "repository"]
_PR_FIELDS = ["id", "number", "title", "body", "state", "merged", "mergeable",
              "headRefName", "baseRefName", "headRef", "baseRef", "files",
              "author", "createdAt", "updatedAt", "url", "repository"]
_REPO_FIELDS = ["id", "databaseId", "name", "nameWithOwner", "owner", "defaultBranchRef",
                "viewerPermission", "hasIssuesEnabled", "issue", "issues",
                "pullRequests", "pullRequest", "description", "private", "url",
                "createdAt", "updatedAt"]
_SEARCH_ENUMS = ["ISSUE", "PULL_REQUEST", "REPOSITORY", "USER", "DISCUSSION", "COMMIT"]
_USER_FIELDS = ["id", "login", "name", "email", "url"]


def _cursor_for(seq):
    return base64.urlsafe_b64encode(("c:%d" % seq).encode()).decode().rstrip("=")


def _seq_from_cursor(cursor):
    try:
        padded = cursor + "=" * (-len(cursor) % 4)
        raw = base64.urlsafe_b64decode(padded.encode()).decode()
        if raw.startswith("c:"):
            return int(raw[2:])
    except Exception:
        pass
    return None


class GraphQLExecutor:
    def __init__(self):
        self.errors = []

    # -- object model: values are (typename, python value)
    def execute(self, doc, variables, operation_name=None):
        self.errors = []
        op = None
        for candidate in doc["operations"]:
            if operation_name is None or candidate["name"] == operation_name:
                op = candidate
                break
        if op is None:
            self.errors.append({"message": "Unknown operation"})
            return None
        if op["type"] == "mutation":
            data = self._resolve(op["selection"], "Mutation", None, doc, variables)
        else:
            data = self._resolve(op["selection"], "Query", None, doc, variables)
        return data

    def _resolve(self, selections, typename, value, doc, variables):
        out = {}
        for sel in selections:
            if sel["kind"] == "spread":
                frag = doc["fragments"].get(sel["name"])
                if frag is None:
                    self.errors.append({"message": "Unknown fragment %r" % sel["name"]})
                    continue
                ftype, fsel = frag
                if ftype == typename:
                    out.update(self._resolve(fsel, typename, value, doc, variables))
                continue
            if sel["kind"] == "inline":
                if sel["type"] == typename:
                    out.update(self._resolve(sel["selection"], typename, value, doc, variables))
                continue
            field = sel["name"]
            alias = sel["alias"]
            args = {k: _resolve_value(v, variables) for k, v in sel["args"].items()}
            result = self._field(typename, value, field, args, doc, variables)
            if result is _UNKNOWN:
                self.errors.append({"message": 'Cannot query field "%s" on type "%s".' % (field, typename)})
                out[alias] = None
                continue
            if result is None or sel["selection"] is None:
                if isinstance(result, tuple):
                    # object value requested without a sub-selection: not JSON-able
                    out[alias] = None
                else:
                    out[alias] = result
            else:
                child_type, child_value = result
                if isinstance(child_value, list):
                    out[alias] = [self._resolve(sel["selection"], child_type, item, doc, variables)
                                  if item is not None else None for item in child_value]
                else:
                    out[alias] = self._resolve(sel["selection"], child_type, child_value, doc, variables)
        return out

    # -- field resolvers; return scalar, None, or (typename, value)
    def _field(self, typename, value, field, args, doc, variables):
        if typename == "Query":
            if field == "viewer":
                return ("User", {"login": VIEWER_LOGIN})
            if field == "repository":
                return self._repository(args.get("owner"), args.get("name"))
            if field == "node":
                return self._node(args.get("id"))
            if field == "__type":
                return self._introspect(args.get("name"))
            return _UNKNOWN
        if typename == "Mutation":
            if field == "createIssue":
                return ("CreateIssuePayload", self._m_create_issue(args.get("input") or {}))
            if field == "closeIssue":
                return ("CloseIssuePayload", self._m_close_issue(args.get("input") or {}))
            if field == "createPullRequest":
                return ("CreatePullRequestPayload", self._m_create_pr(args.get("input") or {}))
            if field == "mergePullRequest":
                return ("MergePullRequestPayload", self._m_merge_pr(args.get("input") or {}))
            if field == "addComment":
                return ("AddCommentPayload", self._m_add_comment(args.get("input") or {}))
            return _UNKNOWN
        if typename == "User":
            if field in ("login", "name", "email", "url"):
                return {"login": VIEWER_LOGIN, "name": VIEWER_NAME,
                        "email": VIEWER_EMAIL, "url": "/api/v3/users/" + VIEWER_LOGIN}.get(field)
            if field == "id":
                return global_id("User", VIEWER_LOGIN)
            return _UNKNOWN
        if typename == "Repository":
            return self._repo_field(value, field, args)
        if typename == "Issue":
            return self._issue_field(value, field, args)
        if typename == "PullRequest":
            return self._pr_field(value, field, args)
        if typename == "IssueConnection":
            if field == "nodes":
                return ("Issue", value["nodes"])
            if field == "pageInfo":
                return ("PageInfo", value["pageInfo"])
            if field == "totalCount":
                return value["total"]
            return _UNKNOWN
        if typename == "PullRequestConnection":
            if field == "nodes":
                return ("PullRequest", value["nodes"])
            if field == "pageInfo":
                return ("PageInfo", value["pageInfo"])
            if field == "totalCount":
                return value["total"]
            return _UNKNOWN
        if typename == "PullRequestChangedFileConnection":
            if field == "nodes":
                return ("PullRequestChangedFile", value["nodes"])
            if field == "pageInfo":
                return ("PageInfo", value["pageInfo"])
            return _UNKNOWN
        if typename == "PullRequestChangedFile":
            if field == "path":
                return value["filename"]
            return _UNKNOWN
        if typename == "PageInfo":
            return value.get(field)
        if typename == "__Type":
            if field == "name":
                return value["name"]
            if field == "fields":
                return ("__Field", [{"name": n} for n in value.get("fields", [])])
            if field == "enumValues":
                return ("__EnumValue", [{"name": n} for n in value.get("enumValues", [])])
            return _UNKNOWN
        if typename == "__Field" or typename == "__EnumValue":
            if field == "name":
                return value["name"]
            return _UNKNOWN
        if typename == "CreateIssuePayload":
            if field == "issue":
                issue = value.get("issue")
                return ("Issue", issue) if issue else None
            return _UNKNOWN
        if typename == "CloseIssuePayload":
            if field == "issue":
                issue = value.get("issue")
                return ("Issue", issue) if issue else None
            return _UNKNOWN
        if typename == "CreatePullRequestPayload":
            if field == "pullRequest":
                pr = value.get("pullRequest")
                return ("PullRequest", pr) if pr else None
            return _UNKNOWN
        if typename == "MergePullRequestPayload":
            if field == "pullRequest":
                pr = value.get("pullRequest")
                return ("PullRequest", pr) if pr else None
            return _UNKNOWN
        if typename == "AddCommentPayload":
            if field == "commentEdge":
                return ("IssueCommentEdge", value.get("commentEdge"))
            return _UNKNOWN
        if typename == "IssueCommentEdge":
            if field == "node":
                node = value.get("node")
                return ("IssueComment", node) if node else None
            return _UNKNOWN
        if typename == "IssueComment":
            if field == "id":
                return value["node_id"]
            if field == "body":
                return value["body"]
            return _UNKNOWN
        if typename == "Ref":
            if field == "name":
                return value
            return _UNKNOWN
        return _UNKNOWN

    def _repository(self, owner, name):
        if not isinstance(owner, str) or not isinstance(name, str):
            return None
        if owner != VIEWER_LOGIN:
            return None
        repo = FORGE.repos.get((owner, name))
        if repo is None:
            return None
        return ("Repository", repo)

    def _node(self, gid):
        if not isinstance(gid, str):
            return None
        kind, key = decode_global_id(gid)
        if kind == "Repository":
            owner, _, name = key.partition("/")
            repo = FORGE.repos.get((owner, name))
            return ("Repository", repo) if repo else None
        if kind == "Issue":
            full, _, num = key.rpartition("#")
            owner, _, name = full.partition("/")
            repo = FORGE.repos.get((owner, name))
            if repo is None:
                return None
            issue = repo.issues.get(int(num)) if num.isdigit() else None
            return ("Issue", (repo, issue)) if issue else None
        if kind == "PullRequest":
            full, _, num = key.rpartition("#")
            owner, _, name = full.partition("/")
            repo = FORGE.repos.get((owner, name))
            if repo is None:
                return None
            pr = repo.pulls.get(int(num)) if num.isdigit() else None
            return ("PullRequest", (repo, pr)) if pr else None
        return None

    def _introspect(self, name):
        table = {
            "Issue": ("__Type", {"name": "Issue", "fields": _ISSUE_FIELDS}),
            "PullRequest": ("__Type", {"name": "PullRequest", "fields": _PR_FIELDS}),
            "Repository": ("__Type", {"name": "Repository", "fields": _REPO_FIELDS}),
            "SearchType": ("__Type", {"name": "SearchType", "enumValues": _SEARCH_ENUMS}),
            "User": ("__Type", {"name": "User", "fields": _USER_FIELDS}),
            "IssueState": ("__Type", {"name": "IssueState", "enumValues": ["OPEN", "CLOSED"]}),
            "PullRequestState": ("__Type", {"name": "PullRequestState",
                                            "enumValues": ["OPEN", "CLOSED", "MERGED"]}),
            "MergeableState": ("__Type", {"name": "MergeableState",
                                          "enumValues": ["MERGEABLE", "CONFLICTING", "UNKNOWN"]}),
            "IssueOrderField": ("__Type", {"name": "IssueOrderField",
                                           "enumValues": ["CREATED_AT", "UPDATED_AT", "COMMENTS"]}),
            "OrderDirection": ("__Type", {"name": "OrderDirection", "enumValues": ["ASC", "DESC"]}),
            "PullRequestMergeMethod": ("__Type", {"name": "PullRequestMergeMethod",
                                                  "enumValues": ["MERGE", "SQUASH", "REBASE"]}),
            "RepositoryPermission": ("__Type", {"name": "RepositoryPermission",
                                                "enumValues": ["ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"]}),
        }
        return table.get(name)

    def _repo_field(self, repo, field, args):
        if field == "id":
            return global_id("Repository", repo.full_name)
        if field == "databaseId":
            return repo.id
        if field == "name":
            return repo.name
        if field == "nameWithOwner":
            return repo.full_name
        if field == "owner":
            return ("User", {"login": repo.owner})
        if field == "defaultBranchRef":
            tip = repo.ref_tip(repo.default_branch)
            if tip is None:
                return None
            return ("Ref", repo.default_branch)
        if field == "viewerPermission":
            return "ADMIN"
        if field == "hasIssuesEnabled":
            return True
        if field == "description":
            return repo.description
        if field == "private":
            return repo.private
        if field == "url":
            return "/api/v3/repos/" + repo.full_name
        if field == "createdAt" or field == "updatedAt":
            return FIXED_TIME
        if field == "issue":
            issue = repo.issues.get(args.get("number"))
            return ("Issue", (repo, issue)) if issue else None
        if field == "issues":
            return ("IssueConnection", self._issue_connection(repo, args))
        if field == "pullRequest":
            pr = repo.pulls.get(args.get("number"))
            return ("PullRequest", (repo, pr)) if pr else None
        if field == "pullRequests":
            return ("PullRequestConnection", self._pr_connection(repo, args))
        return _UNKNOWN

    def _issue_connection(self, repo, args):
        items = [(repo, i) for i in repo.issues.values()]
        states = args.get("states")
        if states:
            wanted = set(s.upper() for s in states)
            items = [it for it in items if it[1]["state"].upper() in wanted]
        order = args.get("orderBy") or {}
        direction = (order.get("direction") or "DESC").upper()
        items.sort(key=lambda it: it[1]["seq"], reverse=(direction != "ASC"))
        after = args.get("after")
        if after:
            seq = _seq_from_cursor(after)
            if seq is not None:
                idx = next((k for k, it in enumerate(items) if it[1]["seq"] == seq), None)
                if idx is not None:
                    items = items[idx + 1:]
        first = args.get("first")
        total = len(items)
        if isinstance(first, int):
            items = items[:first]
        has_next = len(items) < total
        end_cursor = _cursor_for(items[-1][1]["seq"]) if items else None
        return {"nodes": items, "total": total,
                "pageInfo": {"hasNextPage": has_next, "endCursor": end_cursor}}

    def _pr_connection(self, repo, args):
        items = [(repo, p) for p in repo.pulls.values()]
        states = args.get("states")
        if states:
            wanted = set(s.upper() for s in states)
            items = [it for it in items
                     if ("MERGED" if it[1]["merged"] else it[1]["state"].upper()) in wanted]
        items.sort(key=lambda it: it[1]["number"])
        first = args.get("first")
        total = len(items)
        if isinstance(first, int):
            items = items[:first]
        has_next = len(items) < total
        end_cursor = _cursor_for(items[-1][1]["number"]) if items else None
        return {"nodes": items, "total": total,
                "pageInfo": {"hasNextPage": has_next, "endCursor": end_cursor}}

    def _issue_field(self, value, field, args):
        repo, issue = value
        if field == "id":
            return issue["node_id"]
        if field == "number":
            return issue["number"]
        if field == "title":
            return issue["title"]
        if field == "body":
            return issue["body"]
        if field == "state":
            return issue["state"].upper()
        if field == "author":
            return ("User", {"login": VIEWER_LOGIN})
        if field == "createdAt" or field == "updatedAt":
            return FIXED_TIME
        if field == "closedAt":
            return None
        if field == "url":
            return "/api/v3/repos/%s/issues/%d" % (repo.full_name, issue["number"])
        if field == "repository":
            return ("Repository", repo)
        if field == "comments":
            return ("IssueCommentConnection",
                    {"nodes": issue["comments"], "total": len(issue["comments"]),
                     "pageInfo": {"hasNextPage": False, "endCursor": None}})
        if field == "labels":
            return ("LabelConnection",
                    {"nodes": [{"name": n} for n in issue["labels"]], "total": len(issue["labels"]),
                     "pageInfo": {"hasNextPage": False, "endCursor": None}})
        return _UNKNOWN

    def _pr_field(self, value, field, args):
        repo, pr = value
        if field == "id":
            return pr["node_id"]
        if field == "number":
            return pr["number"]
        if field == "title":
            return pr["title"]
        if field == "body":
            return pr["body"]
        if field == "state":
            return "MERGED" if pr["merged"] else pr["state"].upper()
        if field == "merged":
            return pr["merged"]
        if field == "mergeable":
            ok, _ = pr_mergeable(repo, pr)
            return "MERGEABLE" if ok else "CONFLICTING"
        if field == "headRefName":
            return pr["head"]
        if field == "baseRefName":
            return pr["base"]
        if field == "headRef":
            return ("Ref", pr["head"])
        if field == "baseRef":
            return ("Ref", pr["base"])
        if field == "author":
            return ("User", {"login": VIEWER_LOGIN})
        if field == "createdAt" or field == "updatedAt":
            return FIXED_TIME
        if field == "url":
            return "/api/v3/repos/%s/pull/%d" % (repo.full_name, pr["number"])
        if field == "repository":
            return ("Repository", repo)
        if field == "files":
            first = args.get("first")
            files = pr_files(repo, pr)
            if isinstance(first, int):
                files = files[:first]
            return ("PullRequestChangedFileConnection",
                    {"nodes": files, "total": len(files),
                     "pageInfo": {"hasNextPage": False, "endCursor": None}})
        return _UNKNOWN

    # -- mutations
    def _m_create_issue(self, inp):
        gid = inp.get("repositoryId", "")
        kind, key = decode_global_id(gid) if isinstance(gid, str) else (None, None)
        if kind != "Repository":
            self.errors.append({"message": "createIssue: unknown repositoryId"})
            return {}
        owner, _, name = key.partition("/")
        repo = FORGE.repos.get((owner, name))
        if repo is None:
            self.errors.append({"message": "createIssue: unknown repository"})
            return {}
        title = inp.get("title") or ""
        number = repo.next_number
        repo.next_number += 1
        issue = {"id": FORGE.next_id_value(), "node_id": global_id("Issue", "%s#%d" % (repo.full_name, number)),
                 "number": number, "title": title, "body": inp.get("body") or "",
                 "state": "open", "labels": [], "comments": [], "seq": FORGE.next_seq()}
        repo.issues[number] = issue
        return {"issue": (repo, issue)}

    def _m_close_issue(self, inp):
        gid = inp.get("issueId", "")
        kind, key = decode_global_id(gid) if isinstance(gid, str) else (None, None)
        if kind != "Issue":
            self.errors.append({"message": "closeIssue: unknown issueId"})
            return {}
        full, _, num = key.rpartition("#")
        owner, _, name = full.partition("/")
        repo = FORGE.repos.get((owner, name))
        issue = repo.issues.get(int(num)) if repo and num.isdigit() else None
        if issue is None:
            self.errors.append({"message": "closeIssue: unknown issue"})
            return {}
        issue["state"] = "closed"
        return {"issue": (repo, issue)}

    def _m_create_pr(self, inp):
        gid = inp.get("repositoryId", "")
        kind, key = decode_global_id(gid) if isinstance(gid, str) else (None, None)
        if kind != "Repository":
            self.errors.append({"message": "createPullRequest: unknown repositoryId"})
            return {}
        owner, _, name = key.partition("/")
        repo = FORGE.repos.get((owner, name))
        if repo is None:
            self.errors.append({"message": "createPullRequest: unknown repository"})
            return {}
        head = inp.get("headRefName")
        base = inp.get("baseRefName")
        head_sha = repo.ref_tip(head) if head else None
        base_sha = repo.ref_tip(base) if base else None
        if head_sha is None or base_sha is None:
            self.errors.append({"message": "createPullRequest: head or base branch does not exist"})
            return {}
        for p in repo.pulls.values():
            if p["head"] == head and p["base"] == base and p["state"] == "open":
                self.errors.append({"message": "createPullRequest: a pull request already exists"})
                return {}
        number = repo.next_number
        repo.next_number += 1
        pr = {"id": FORGE.next_id_value(), "node_id": global_id("PullRequest", "%s#%d" % (repo.full_name, number)),
              "number": number, "title": inp.get("title") or "", "body": inp.get("body") or "",
              "state": "open", "merged": False, "mergeable": True,
              "merge_commit_sha": None, "head": head, "base": base,
              "head_sha": head_sha, "base_sha": base_sha}
        ok, _ = pr_mergeable(repo, pr)
        pr["mergeable"] = ok
        repo.pulls[number] = pr
        return {"pullRequest": (repo, pr)}

    def _m_merge_pr(self, inp):
        gid = inp.get("pullRequestId", "")
        kind, key = decode_global_id(gid) if isinstance(gid, str) else (None, None)
        if kind != "PullRequest":
            self.errors.append({"message": "mergePullRequest: unknown pullRequestId"})
            return {}
        full, _, num = key.rpartition("#")
        owner, _, name = full.partition("/")
        repo = FORGE.repos.get((owner, name))
        pr = repo.pulls.get(int(num)) if repo and num.isdigit() else None
        if pr is None:
            self.errors.append({"message": "mergePullRequest: unknown pull request"})
            return {}
        method = (inp.get("mergeMethod") or "MERGE").upper()
        if method == "SQUASH":
            method = "squash"
        elif method == "REBASE":
            method = "rebase"
        else:
            method = "merge"
        if pr["state"] != "open":
            self.errors.append({"message": "mergePullRequest: pull request is not open"})
            return {"pullRequest": (repo, pr)}
        if do_merge(repo, pr, method) is None:
            self.errors.append({"message": "mergePullRequest: merge conflict"})
            return {"pullRequest": (repo, pr)}
        return {"pullRequest": (repo, pr)}

    def _m_add_comment(self, inp):
        gid = inp.get("subjectId", "")
        kind, key = decode_global_id(gid) if isinstance(gid, str) else (None, None)
        if kind != "Issue":
            self.errors.append({"message": "addComment: unknown subjectId"})
            return {}
        full, _, num = key.rpartition("#")
        owner, _, name = full.partition("/")
        repo = FORGE.repos.get((owner, name))
        issue = repo.issues.get(int(num)) if repo and num.isdigit() else None
        if issue is None:
            self.errors.append({"message": "addComment: unknown issue"})
            return {}
        comment = {"id": FORGE.next_id_value(),
                   "node_id": global_id("IssueComment", "%s#%d:%d" % (repo.full_name, issue["number"], len(issue["comments"]) + 1)),
                   "body": inp.get("body") or ""}
        issue["comments"].append(comment)
        return {"commentEdge": {"node": comment}}


class _Unknown:
    pass


_UNKNOWN = _Unknown()


def _graphql_one(body):
    """Execute one GraphQL operation body -> response dict."""
    query = body.get("query")
    variables = body.get("variables") or {}
    operation_name = body.get("operationName")
    if not isinstance(query, str):
        return {"data": None, "errors": [{"message": "query must be a string"}]}
    try:
        doc = _GQLParser(query).parse()
    except ValueError as exc:
        return {"data": None, "errors": [{"message": "GraphQL syntax error: %s" % exc}]}
    with FORGE.lock:
        ex = GraphQLExecutor()
        data = ex.execute(doc, variables, operation_name)
    resp = {"data": data}
    if ex.errors:
        resp["errors"] = ex.errors
    return resp


# --------------------------------------------------------------------------- MCP

MCP_TOOLS = [
    {"name": "create_repo",
     "description": "Create a repository owned by the authenticated user.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "name": {"type": "string"},
                                    "description": {"type": "string"},
                                    "private": {"type": "boolean"}},
                     "required": ["name"]}},
    {"name": "get_repo",
     "description": "Get a repository by owner and name.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_issue",
     "description": "Create an issue in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "title": {"type": "string"},
                                    "body": {"type": "string"}},
                     "required": ["owner", "repo", "title"]}},
    {"name": "list_issues",
     "description": "List issues in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "state": {"type": "string"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_pull_request",
     "description": "Open a pull request from a head branch into a base branch.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "title": {"type": "string"},
                                    "body": {"type": "string"},
                                    "head": {"type": "string"},
                                    "base": {"type": "string"}},
                     "required": ["owner", "repo", "title", "head", "base"]}},
    {"name": "merge_pull_request",
     "description": "Merge a pull request by number.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "pull_number": {"type": "integer"}},
                     "required": ["owner", "repo", "pull_number"]}},
    {"name": "get_issue",
     "description": "Get one issue by number.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "number": {"type": "integer"}},
                     "required": ["owner", "repo", "number"]}},
    {"name": "list_pull_requests",
     "description": "List pull requests in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "state": {"type": "string"}},
                     "required": ["owner", "repo"]}},
]


def _mcp_tool_result(payload, is_error=False):
    text = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
    return {"content": [{"type": "text", "text": text}],
            "structuredContent": payload, "isError": is_error}


def _mcp_call_tool(name, args):
    """Execute one MCP tool. Returns a tool-result dict."""
    with FORGE.lock:
        try:
            if name == "create_repo":
                repo_name = args.get("name")
                if not isinstance(repo_name, str) or not repo_name:
                    return _mcp_tool_result({"error": "name is required"}, True)
                repo = FORGE.create_repo(VIEWER_LOGIN, repo_name,
                                         bool(args.get("private", False)),
                                         args.get("description") or "")
                return _mcp_tool_result(repo_json(repo))
            if name == "get_repo":
                owner = args.get("owner") or VIEWER_LOGIN
                repo = FORGE.get_repo(owner, args.get("repo") or "")
                return _mcp_tool_result(repo_json(repo))
            if name == "create_issue":
                repo = FORGE.get_repo(args.get("owner") or VIEWER_LOGIN, args.get("repo") or "")
                title = args.get("title")
                if not isinstance(title, str) or not title:
                    return _mcp_tool_result({"error": "title is required"}, True)
                number = repo.next_number
                repo.next_number += 1
                issue = {"id": FORGE.next_id_value(),
                         "node_id": global_id("Issue", "%s#%d" % (repo.full_name, number)),
                         "number": number, "title": title, "body": args.get("body") or "",
                         "state": "open", "labels": [], "comments": [], "seq": FORGE.next_seq()}
                repo.issues[number] = issue
                return _mcp_tool_result(issue_json(repo, issue))
            if name == "list_issues":
                repo = FORGE.get_repo(args.get("owner") or VIEWER_LOGIN, args.get("repo") or "")
                state = args.get("state") or "open"
                items = [i for i in repo.issues.values() if state == "all" or i["state"] == state]
                items.sort(key=lambda i: i["number"])
                return _mcp_tool_result({"issues": [issue_json(repo, i) for i in items]})
            if name == "get_issue":
                repo = FORGE.get_repo(args.get("owner") or VIEWER_LOGIN, args.get("repo") or "")
                issue = repo.issues.get(args.get("number"))
                if issue is None:
                    return _mcp_tool_result({"error": "issue not found"}, True)
                return _mcp_tool_result(issue_json(repo, issue))
            if name == "create_pull_request":
                repo = FORGE.get_repo(args.get("owner") or VIEWER_LOGIN, args.get("repo") or "")
                head = args.get("head")
                base = args.get("base") or repo.default_branch
                head_sha = repo.ref_tip(head) if head else None
                base_sha = repo.ref_tip(base) if base else None
                if head_sha is None or base_sha is None:
                    return _mcp_tool_result({"error": "head or base branch does not exist"}, True)
                for p in repo.pulls.values():
                    if p["head"] == head and p["base"] == base and p["state"] == "open":
                        return _mcp_tool_result({"error": "a pull request already exists"}, True)
                number = repo.next_number
                repo.next_number += 1
                pr = {"id": FORGE.next_id_value(),
                      "node_id": global_id("PullRequest", "%s#%d" % (repo.full_name, number)),
                      "number": number, "title": args.get("title") or "", "body": args.get("body") or "",
                      "state": "open", "merged": False, "mergeable": True,
                      "merge_commit_sha": None, "head": head, "base": base,
                      "head_sha": head_sha, "base_sha": base_sha}
                ok, _ = pr_mergeable(repo, pr)
                pr["mergeable"] = ok
                repo.pulls[number] = pr
                return _mcp_tool_result(pr_json(repo, pr))
            if name == "list_pull_requests":
                repo = FORGE.get_repo(args.get("owner") or VIEWER_LOGIN, args.get("repo") or "")
                state = args.get("state") or "open"
                items = [p for p in repo.pulls.values() if state == "all" or p["state"] == state]
                items.sort(key=lambda p: p["number"])
                return _mcp_tool_result({"pull_requests": [pr_json(repo, p) for p in items]})
            if name == "merge_pull_request":
                repo = FORGE.get_repo(args.get("owner") or VIEWER_LOGIN, args.get("repo") or "")
                pr = repo.pulls.get(args.get("pull_number"))
                if pr is None:
                    return _mcp_tool_result({"error": "pull request not found"}, True)
                if pr["state"] != "open":
                    return _mcp_tool_result({"error": "pull request is not open"}, True)
                commit = do_merge(repo, pr, "merge")
                if commit is None:
                    return _mcp_tool_result({"error": "merge conflict"}, True)
                return _mcp_tool_result({"merged": True, "sha": commit,
                                         "number": pr["number"], "state": "closed"})
            return _mcp_tool_result({"error": "unknown tool: %s" % name}, True)
        except (NotFound, Unprocessable) as exc:
            return _mcp_tool_result({"error": str(exc)}, True)


class GraphQLMCPMixin:
    def handle_graphql(self):
        raw = self.raw_body()
        try:
            body = json.loads(raw.decode("utf-8"))
        except Exception:
            self.send_json(400, {"message": "Problems parsing JSON"})
            return
        with FORGE.lock:
            if isinstance(body, list):
                self.send_json(200, [_graphql_one(op) if isinstance(op, dict) else
                                     {"data": None, "errors": [{"message": "operation must be an object"}]}
                                     for op in body])
            elif isinstance(body, dict):
                self.send_json(200, _graphql_one(body))
            else:
                self.send_json(400, {"message": "GraphQL body must be an object or an array"})

    def handle_mcp(self):
        if self.command == "DELETE":
            self.read_body()
            self.send_no_content(204)
            return
        if self.command != "POST":
            self.send_json(405, {"message": "Method Not Allowed"})
            return
        raw = self.raw_body()
        try:
            body = json.loads(raw.decode("utf-8"))
        except Exception:
            # parse error: HTTP 400, JSON-RPC -32700 (echo the id when recoverable)
            rpc_id = None
            m = re.search(rb'"id"\s*:\s*(\d+|"(?:[^"\\]|\\.)*")', raw)
            if m:
                try:
                    rpc_id = json.loads(m.group(1).decode("utf-8"))
                except Exception:
                    rpc_id = None
            self.send_json(400, {"jsonrpc": "2.0", "id": rpc_id,
                                 "error": {"code": -32700, "message": "Parse error"}})
            return
        if not isinstance(body, dict) or "method" not in body:
            self.send_json(400, {"jsonrpc": "2.0", "id": body.get("id") if isinstance(body, dict) else None,
                                 "error": {"code": -32600, "message": "Invalid Request"}})
            return
        method = body.get("method")
        rpc_id = body.get("id")
        params = body.get("params") or {}
        if not isinstance(params, dict):
            params = {}
        result, error = self._mcp_dispatch(method, params)
        if rpc_id is None:
            # notification: 202, no body
            self.send_response(202)
            self.send_header("Content-Length", "0")
            self.send_header("X-GitHub-Request-Id", self._req_id())
            self.end_headers()
            return
        if error is not None:
            self.send_json(200, {"jsonrpc": "2.0", "id": rpc_id, "error": error})
        else:
            self.send_json(200, {"jsonrpc": "2.0", "id": rpc_id, "result": result})

    def _mcp_dispatch(self, method, params):
        if method == "server/discover":
            return ({"protocolVersion": MCP_REVISION,
                     "supportedVersions": MCP_REVISIONS,
                     "capabilities": {"tools": {}},
                     "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION},
                     "instructions": "A GitHub-compatible git forge: repositories, issues, pull requests."}, None)
        if method == "initialize":
            requested = params.get("protocolVersion")
            chosen = requested if requested in MCP_REVISIONS else MCP_REVISIONS[0]
            return ({"protocolVersion": chosen,
                     "capabilities": {"tools": {}},
                     "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION}}, None)
        if method in ("notifications/initialized", "notifications/cancelled"):
            return ({}, None)
        if method == "tools/list":
            return ({"tools": MCP_TOOLS}, None)
        if method == "tools/call":
            name = params.get("name")
            args = params.get("arguments") or {}
            if not isinstance(args, dict):
                args = {}
            tool = next((t for t in MCP_TOOLS if t["name"] == name), None)
            if tool is None:
                return None, {"code": -32602, "message": "Unknown tool: %s" % name}
            required = tool["inputSchema"].get("required", [])
            missing = [r for r in required if r not in args or args[r] is None]
            if missing:
                return ({"content": [{"type": "text",
                                      "text": json.dumps({"error": "missing required arguments: %s" % ", ".join(missing)})}],
                         "structuredContent": {"error": "missing required arguments: %s" % ", ".join(missing)},
                         "isError": True}, None)
            return (_mcp_call_tool(name, args), None)
        if method == "ping":
            return ({}, None)
        return None, {"code": -32601, "message": "Method not found: %s" % method}


class ForgeHandler(GitMixin, GraphQLMCPMixin, Handler):
    pass


# --------------------------------------------------------------------------- lifecycle

def _http_request(url, method, body=None, timeout=30):
    req = urllib.request.Request(url, method=method,
                                 data=body,
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.status, resp.read()


class ForgeServer(ThreadingHTTPServer):
    daemon_threads = True
    # The default listen backlog (5) drops/delays SYNs when 50 clones connect
    # at once; the suite's clone workload opens them all concurrently.
    request_queue_size = 256
    allow_reuse_address = True


def main():
    import argparse
    parser = argparse.ArgumentParser(description="github-core-clone-01 forge")
    parser.add_argument("--port", type=int, default=0, help="standalone port (0 = ephemeral)")
    args = parser.parse_args()
    env_url = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
    server = ForgeServer(("0.0.0.0", args.port), ForgeHandler)
    if env_url:
        port = server.server_address[1]
        sys.stdout.write("[entry] listening on port %d\n" % port)
        sys.stdout.flush()
        # register with retries
        delay = 0.25
        while True:
            try:
                status, _ = _http_request(env_url + "/register", "POST",
                                          json.dumps({"port": port}).encode(), timeout=30)
                if status in (200, 409):
                    break
                if status in (400, 405):
                    sys.stderr.write("[entry] register answered HTTP %d\n" % status)
                    sys.exit(1)
            except Exception:
                pass
            time.sleep(delay)
            delay = min(2.0, delay * 2)
        sys.stdout.write("[entry] registered; waiting for the env to say done\n")
        sys.stdout.flush()
        delay = 0.25
        while True:
            try:
                status, data = _http_request(env_url + "/done", "GET", timeout=30)
                if status == 200 and json.loads(data.decode("utf-8")).get("done") is True:
                    break
            except Exception:
                pass
            time.sleep(delay)
            delay = min(2.0, delay * 2)
        server.shutdown()
        server.server_close()
        sys.stdout.write("[entry] done\n")
        sys.exit(0)
    else:
        sys.stdout.write("[entry] standalone on port %d (MAKEFUN_ENV_URL unset)\n" % server.server_address[1])
        sys.stdout.flush()
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass


if __name__ == "__main__":
    main()

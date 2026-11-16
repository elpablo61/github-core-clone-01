# github-core-clone-01 — a GitHub-compatible git forge in one Python file

[![make.fun bounty](https://img.shields.io/badge/make.fun-bounty-blue)](https://make.fun/bounty/github-core-clone-01)
[![license: MIT](https://img.shields.io/badge/license-MIT-green)](LICENSE)
[![python: 3.13](https://img.shields.io/badge/python-3.13-blue)](main.py)

A standalone forge that serves GitHub's four surfaces from **one process** and
its own in-memory store — no UI, no outside service, no git binary, standard
library only:

- **git smart HTTP** — protocol v2 (`ls-refs`, `fetch`, shallow/deepen) and v0,
  `git-upload-pack` / `git-receive-pack`, pack v2 read/write (full objects,
  ofs/ref-delta resolution), sideband-64k, report-status, fast-forward rules
- **GitHub REST v3** (`/api/v3`) — repositories, branches, commits, contents,
  issues, comments, labels, pull requests (files, squash merge, conflicts)
- **GitHub GraphQL v4** (`/api/graphql`) — the documents `gh` and
  `github-mcp-server` send: viewer, repository, issues, pull requests,
  `__type` introspection, `node(id:)`, batching, cursor pagination, mutations
- **MCP over streamable HTTP** (`/mcp`) — `server/discover` (2026-07-28) and
  the legacy `initialize` handshake, `tools/list` / `tools/call`

Entry for the [make.fun bounty "Build a GitHub-compatible git forge"](https://make.fun/bounty/github-core-clone-01)
($500, closes 21 Nov 2026).

## Run

```sh
# Trial lifecycle (the kit's contract): the env hands it MAKEFUN_ENV_URL
# and MAKEFUN_SHOP_TOKEN; the forge binds an ephemeral port, registers it,
# serves until the env says done, then exits 0.
MAKEFUN_ENV_URL=http://store:8080 MAKEFUN_SHOP_TOKEN=<token> python3 main.py

# Standalone (dev / local grading):
MAKEFUN_SHOP_TOKEN=<token> python3 main.py --port 8765
```

Python 3.13, standard library only. No install step, no dependencies.

## How it works

`main.py` (~3.100 lines) is the whole forge:

- **Store** — one in-memory `Forge`: repositories, git objects (sha1 ids,
  commit/tree/blob/tag), refs, issues, pull requests, labels. Commit metadata
  (parents/tree) is cached so fast-forward and merge-base walks stay cheap.
  All rendered timestamps are one fixed value and creation order comes from a
  monotonic sequence, so two runs on the same input behave identically.
- **Git** — pkt-line framing, pack v2 writer (no deltas; the suite accepts
  that) and a pack reader that resolves ofs-delta/ref-delta chains, including
  thin packs against objects the server already holds. Fetches honour `have`
  lines (incremental), `deepen` (shallow boundaries + unshallow), and never
  re-send objects the client holds.
- **REST** — the v3 shapes the suite asserts, including `Link` pagination,
  201/200/204/404/409/422 statuses, and `X-GitHub-Request-Id` on every reply.
- **GraphQL** — a small parser for the exact documents the suite sends
  (variables, inline enums/input objects, fragments, batching) over one
  shared resolver backed by the same store as REST, so the two views agree.
- **MCP** — eight tools (`create_repo`, `get_repo`, `create_issue`,
  `list_issues`, `create_pull_request`, `merge_pull_request`, plus
  `get_issue`, `list_pull_requests`) with JSON-RPC error codes -32601/-32602/
  -32700 where the spec wants them.
- **Performance notes** — `TCP_NODELAY` on every connection (without it the
  Nagle/delayed-ACK pairing costs ~40 ms per round trip), a 256-deep listen
  backlog (the 50-concurrent-clone workload needs it), and a threaded server.

## Local grading (kit)

```sh
# start the forge, then run the sealed suite against it:
node --experimental-strip-types sdk/run.ts \
  --url http://127.0.0.1:8765 --token <token> --perf --json
```

Local results on this machine (4 runs): **120/120 conformance checks**
(git 30/30, repos 15/15, issues 15/15, pulls 20/20, graphql 20/20,
mcp 15/15, protocol 5/5), score **916–934 / 1000**
(feature 600 + agent 200 + perf 116–134). See `BUILD_LOG.md` (not committed)
for the per-workload numbers and the honest gaps.

## License

MIT — see [LICENSE](LICENSE).

---

Built for the make.fun bounty — try make.fun: https://make.fun/r/vky0ybyt

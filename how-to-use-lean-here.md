# How to use Lean on this machine

Setup notes for any agent session (Claude, codex, kimi) that wants to do
Lean 4 work here. Everything below is installed at user scope and works
from non-interactive shells.

## Toolchain

elan-managed, at `~/.elan/bin` (`lean`, `lake`, `elan`) — already on PATH
in agent shells. New project: `lake new <name>` (add `math` template for a
Mathlib dependency, then `nice ionice lake exe cache get` before the first
build — never build Mathlib from source). A valid project needs
`lakefile.toml` (or `.lean`) plus `lean-toolchain`.

Existing Lean projects: `~/prog/shy-heap-lean`, `~/prog/auman/aumann`.

## lean4 plugin (local proving loop)

`lean4@lean4-skills` v4.6.7 (cameronfreer/lean4-skills) is installed for
Claude Code (user scope) and codex. It activates automatically on `.lean`
files; commands: `/lean4:draft`, `formalize`, `autoformalize`, `prove`,
`autoprove`, `disprove`, `checkpoint`, `review`, `refactor`, `golf`,
`learn`, `diagnose`. Sanity check: `/lean4:diagnose`. Its git guardrails
activate inside Lean projects (destructive whole-worktree git ops are
hard-blocked; statements/signatures are treated as immutable contracts).

## Aristotle (remote heavy prover)

`aristotle` CLI wrapper at `~/.local/bin/aristotle` — auth is
self-contained (key auto-loaded from `~/.config/aristotle.key`; never
read or print that file). Claude sessions also have the `/aristotle`
skill; full workflow in `~/.claude/skills/aristotle/SKILL.md`. Essentials:

- Canonical input: a Lean project with `sorry` holes **you wrote
  yourself** — statement formulation stays under your control. Optional
  natural-language proof sketch in the docstring under a
  `PROVIDED SOLUTION` tag (comments inside proof blocks are ignored).
- For a conjecture, ask **prove-or-disprove** first — it generates
  counterexamples, which is cheaper than hours on an unprovable goal.
- Async by default: `aristotle submit "<prompt>" --project-dir <dir>` →
  record the project ID → `aristotle show <id>` to poll →
  `aristotle download <id> --destination <path>`. Runs take minutes to
  hours; avoid `--wait` for anything nontrivial. Record prompt + project
  ID + integration point in session notes / NEXT.md.
- Strong at local helper lemmas, weak at global coordination arguments —
  decompose, and leave the main theorem its own `sorry`.
- **Do not trust its exit codes** (observed exiting 0 on hard errors).
  Success = confirmed project ID or downloaded artefact, nothing less.
- A returned proof counts only after local re-checking at declaration
  level: `lake build`, statement is the one you meant, no `sorry`, no
  added axioms (`#print axioms <theorem>`).
- Data policy: Matthias's own projects and public material may be sent
  without asking; Fuse material never (rule follows content, not path);
  other proprietary code needs confirmation every time.

## Division of labour

Draft statements and skeletons locally (`/lean4:draft`,
`/lean4:formalize`), delegate hard sorries to Aristotle, review/golf the
returned proofs locally (`/lean4:review`, `/lean4:golf`).
`/lean4:disprove` is the local counterpart to Aristotle's counterexample
search.

## lean-lsp-mcp (live goal inspection)

[lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) is registered as
a user-scope MCP server for Claude Code and codex (`lean-lsp`, runs
`uvx lean-lsp-mcp`). Tools include `lean_goal(file, line)`,
`lean_local_search`, `lean_loogle` (type patterns),
`lean_multi_attempt` (test several tactics at once), and
`lean_diagnostic_messages` — sub-second feedback instead of full
`lake build` round-trips. Run `lake build` (and `lake exe cache get` on
a fresh clone) once per project first to avoid LSP timeouts.

## Kimi

Kimi has the `lean4` skill installed skill-only at
`~/.agents/skills/lean4/` (instructions and references; no helper
scripts or hooks). Aristotle works from kimi via the same `aristotle`
CLI wrapper.

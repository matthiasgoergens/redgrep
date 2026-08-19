# NEXT — redgrep rework (handoff 2026-08-17)

Goal: extended regexes (∪ · * ∩ ¬) as typed combinators, matching-as-parsing
with **typed failure evidence** (`not` swaps the bifunctor sides — no prior
art found; survey at ~/prog/paquari-notes/redgrep-evidence-of-absence/survey.md (private)), correct and fast.
DESIGN.md is the decision log; every number below has raw logs under
logs/2026-08-17/ with commit + command.

## Done this session (all on master, all tests green)

- Stackage lts-24.55 / GHC 9.10.3 (3bee920); builds, tests, benches all run.
- Prior-art survey + blog draft (22b22e6, 72a0af4;
  ~/prog/paquari-notes/redgrep-evidence-of-absence/evidence-of-absence.html (private) — draft in Matthias's voice,
  NOT reviewed by him for publication).
- Phase 1 (e317b6d): Redgrep.Core value-free canonical AST, Brzozowski
  derivs, oracle (Redgrep.Oracle), ~30 properties incl. differential vs
  both 2016 engines (they agree — old code was correct, just slow).
- Closure ops (e317b6d): quotient, rightQuotient, rev, invHom. Machine
  nodes = DFAs as leaves, modBase/divisibleBy (4e0de1f, the Div7 answer).
- Phase 3: interned lazy DFA `matchDfa` (48363bc); derivative classes +
  persistent `compile`/`matchCompiled` (77bde15); dense ASCII tables
  (7bf32f9). flapping 100k: 70 ms → ~0.6 ms. div7 6.8 ns/char.
- Phase 4 rule 1 (39bdb49): Redgrep.Plan rewrites canonical `.* lit .*`
  to memchr substring search — ping-search 100k: 106 µs vs regex-tdfa
  502 µs (logs/2026-08-17/bench/phase4-planner-rule1.txt).
- **Formally verified** (e88f50b): 8 language-level laws (deriv laws for
  ∩ ¬ · *, invHom rule, rev/invHom, right-quotient-via-rev, nonempty-chunk
  star) proved by Aristotle (project 881d1d9a, aristotle/PROJECTS),
  re-checked locally: lake build OK, zero sorry, axioms only
  propext/Classical.choice/Quot.sound; deriv1_invHom needs NO axioms
  (logs/2026-08-17/aristotle-axioms-audit.log). Proved file:
  aristotle/Statements-proved.lean.
- Two memory bugs fixed (77bde15): refine-without-dedup (exponential);
  compile queue self-append (infinite loop; probe: tools/probe-compile.hs). Standing guard: run tests via
  `systemd-run --user --scope -p MemoryMax=6G` (+ env DBUS/XDG vars,
  see DESIGN.md) with `--test-arguments '+RTS -M4g -RTS'`.

## Next actions (priority order)

1. **Required-factor prefilter + ByteString end-to-end.** Generalise
   planner rule 1: extract a necessary literal from any pattern, reject
   fast, then DFA; move matcher input to ByteString (all engines walk
   String today). Matthias explicitly wants the performance chase
   ("chase the ceiling list").
2. **Hash-consing the AST** (kmett `intern` or manual table): fixes the
   one-shot evil-pattern cost (state construction, not caching —
   evil-aqn-an unchanged by interning, see DESIGN.md phase-3 notes).
3. **Phase 2 evidence layer**: bit-coded trace + typed decode; failure
   evidence via mkeps-dual; implement Keil–Thiemann Δ/∇ as independent
   cross-check. MUST first write down the refutation disambiguation
   policy for seq/rep (open design question, DESIGN.md hazards) — and
   `rep_ (Rep x) = Rep x` is UNSOUND for evidence (documented hazard).
   Lean twin: seed from aristotle/Statements-proved.lean + local Lean
   toolchain (how-to-use-lean-here.md); study pandaman64/lean-regex.

## Open items

- DeepSeek review DONE (3 findings, all measured, fixed, regression-
  tested; transcript in logs/2026-08-17/). Codex still out of credits
  until Aug 20 — optional third family pass then.
- Blog draft needs Matthias's read before any publication (his rule);
  note pushing the repo makes the draft file public.
- falsify migration for tests (in lts-24.55; deferred while suite churns).
- 2016 modules deleted from tree (git history keeps them); differential
  props retired with them.
- many-short-strings: still 2.5x behind regex-tdfa (109 µs vs 271 µs).
- Aristotle project 4385f9c0 (Lean twin correctness sorries) pending;
  verify locally on return (lake build, no sorry, #print axioms).

## Spun-off threads (not this project's critical path)

- FIP-style static in-place checker for Lean (and the GHC prior-art
  survey: LinearTypes, destination-passing, cardinality analysis):
  independent session, own motivating example — see DESIGN.md
  "In-place mutation: runtime vs static". Decision and reasons recorded
  there 2026-08-19. CANDIDATE MOTIVATING EXAMPLE found 2026-08-19:
  Langley's zstd-in-Lean FSE decoder (imperialviolet.org 2026-07-26,
  10x vs C, names RC-invisibility as the killer) — a real, published,
  quantified instance of exactly the problem the checker would solve.

## Unverified beliefs (do not treat as fact)

- "flapping" name origin: from 2016 Red.hs:663; no google/redgrep origin
  found (README grep empty), Matthias doesn't remember coining context.
- Bille–Gørtz–Jessen (arXiv:2510.09311): whether complement yields a
  structured witness — hedged; PDF at ~/prog/paquari-notes/redgrep-evidence-of-absence/, unread in depth.
- lean-regex capabilities: from web search only, never built/run here.
- Benchmark absolute numbers drift ~1.5x with machine load (observed
  between runs); relative standings were stable.

## Gotchas for the next session

- `aristotle download --destination` = archive FILE (tar.gz), not a dir
  (skill updated by peer session, git-tracked b35b0fe/5d47733).
- stack test/bench needs XDG_RUNTIME_DIR + DBUS_SESSION_BUS_ADDRESS set
  for systemd-run --user (see DESIGN.md / this file's guard command).
- Bench CSV+txt go to logs/<date>/bench/ with commit hash in the name.

# redgrep rework: correctness, speed, and the evidence bifunctor

Status: phase 1 in progress (2026-08-17). Prior-art background: `notes-prior-art/survey.md`
and the write-up `notes-prior-art/evidence-of-absence.html`.

## Goal

Make what the library always tried to do actually work, and work fast:
extended regexes (union, concatenation, star, intersection, complement) as
typed combinators, matching as parsing, with success evidence on match and
structured failure evidence on non-match, `not` swapping the two.

Architecture (from the survey): the term is folded once before any input
arrives; the match loop iterates on first-order data; values exist only at
the two ends.

1. **Phase 1 (this commit): value-free core + oracle + property tests +
   benchmarks.** `Redgrep.Core`: untyped, `Ord`-erable regex AST maintained in
   ACI-canonical form by smart constructors (Owens–Reppy–Turon), Brzozowski
   derivatives, plain and memoised matchers. Correctness pinned by an
   obviously-correct oracle and differential testing against the 2016 engines.
2. **Phase 2: evidence.** Bit-coded run trace (Sulzmann–Lu second algorithm,
   Tan–Urban's `erase` discipline: comparisons always on the erased skeleton,
   never the payload) + one typed decode at the end. Failure evidence via the
   mkeps-dual (ε-refutation) — the novel part. Requires choosing an explicit
   *refutation disambiguation policy* for seq/rep (e.g. blame the longest
   viable prefix); record it here when chosen.
3. **Phase 3: speed.** State interning (hash-consing or rere-style knot-tied
   memoisation), character-class partitioning of the alphabet (derivative
   classes), lazy DFA. Benchmarks decide; sparse (Antimirov), dense
   (marks/AFA) and syntactic (Brzozowski) are interchangeable state formats.
4. **Phase 4 (later): the query planner.** Choose backend per regex, like GNU
   grep's literal prefilter (find a required substring, memchr/Boyer–Moore to
   candidate positions, verify) or RE2's required-prefix analysis. Positive
   fragment → could even use Glushkov-family engines; complement/intersection
   present → derivative family. Explicitly out of scope until phases 1–3 hold.

## Repository layout decision

`master` should show what works plus the write-up; the 2016 exploration is
preserved by git history, not by the working tree. The old modules
(`Red`, `Final`, `DDup`, `Types`, `ArbitraryFinal`, `Tool`, `Util`) stay in
place for now **only** as differential-test references and benchmark
baselines, and will simply be deleted once the new engine reaches feature
parity (evidence included) — git history keeps the fossil record. The
write-up stays in `notes-prior-art/`; publishing it anywhere is a separate,
explicit step.

## Correctness: oracle + properties

Oracle (`Redgrep.Oracle`): direct recursive membership semantics —
`member :: RE -> String -> Bool` by trying all splits for `seq`, all nonempty
first chunks for `rep`, Boolean operations pointwise, `not` by negation.
Exponential and obviously correct; used only on small regexes and short
strings. Chosen over a stratified length-indexed set semantics because it is
harder to get wrong and extends trivially to inverse homomorphism.

Test discipline: for each random regex (sizes ~≤ 12 over alphabet {a,b}),
check against **all** strings over {a,b} up to length 5 (63 strings) rather
than random strings — deterministic boundary coverage, cheap at these sizes.

Properties (test/Spec.hs):
- `match` agrees with the oracle (the main theorem).
- `matchMemo` agrees with `match`.
- `nullable r == member r ""`.
- Derivative is left quotient: `member (deriv c r) s == member r (c:s)`.
- Canonical-form laws hold *structurally* (not just semantically):
  `alt [x,y] == alt [y,x]`, `alt [x,x] == x`, `not_ (not_ x) == x`.
- `quotient u r` matches `s` iff `r` matches `u ++ s` (prefix quotient).
- `rightQuotient u r` matches `s` iff `r` matches `s ++ u`.
- `rev r` matches `s` iff `r` matches `reverse s`.
- `invHom h r` matches `s` iff `r` matches `concatMap h s` (fixed sample
  homomorphisms, including erasing and expanding ones).
- Differential: the 2016 final-tagless engine (`DDup.dd`) and the 2016
  initial engine (`Red.match`) agree with `Redgrep.Core.match` on the
  translatable fragment (positive char classes + dot), small sizes only.
  Disagreements are findings about the old engines, not necessarily bugs in
  the new one — the oracle arbitrates.

## Benchmarks (bench/Bench.hs, criterion)

Engines: `Core.match` (naive re-derivation), `Core.matchMemo` (per-run
transition cache), `regex-applicative` (Glushkov threads, the closest typed
Haskell library), `regex-tdfa` (tagged DFA, the standard POSIX engine), and
the 2016 engines on small inputs (`Red.match`, `DDup.dd`).

Workloads:
- `a*` on `a^n` — the trivial-loop baseline (state space of size 1).
- unanchored literal search `.*ping.*` — what grep does all day.
- `(a?)^n a^n` on `a^n` — the classic backtracking killer; derivative and
  DFA engines should stay polynomial.
- `flapping`: `(.* ping .*) ∩ ¬(.* flapping .*)` — the extended-algebra
  showcase; only Core and the 2016 engines can express it.

Method: criterion with `--time-limit` kept low for iteration; runs saved
under `logs/<date>/bench/` with the commit hash. Comparisons against other
languages (grep, RE2, rust/regex, Google redgrep itself) belong in a later
subprocess harness — in-process Haskell comparisons first.

Base-rate note (2026-08-17): timings recorded on this machine, GHC 9.10.3,
`-O2` on the benchmark component; treat cross-run comparisons at ±20%.

## Closure operations: what is sound where

| operation | status | reason |
|---|---|---|
| left quotient by string | free | it *is* the derivative |
| right quotient by string | free | `rev . quotient (reverse u) . rev` |
| reversal | free, whole algebra | rev commutes with ∪, ∩, ¬, ·(swapped), * — and `rev (invHom h r) = invHom (reverse . h) (rev r)` |
| inverse homomorphism | new constructor | commutes with derivatives (`d_c (h⁻¹L) = h⁻¹(d_{h c} L)`) and all Boolean ops; nullable is inherited; evidence composes (evidence for `s` is evidence for `h s`) |
| forward homomorphism | **deferred** | does NOT commute with ¬ or ∩ (`h(A∩B) ⊆ h(A)∩h(B)` strictly, similar failure for ¬), so syntactic substitution is unsound in this algebra; sound routes are complement-elimination via DFA first, or restriction to the positive fragment |
| quotient by a language | deferred | `K\L = ⋃_{u∈K} u\L` — needs automaton product, not a syntactic rule |

`invHom` is represented as `InvHom (Map Char String) RE` — a `Map` rather than
a function so the AST keeps decidable equality and ordering (the whole point
of phase 1). Characters absent from the map map to themselves.

These operations are for fun and are secondary: the priority is making the
original feature set (extended algebra + evidence) correct and fast.

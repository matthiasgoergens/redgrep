# redgrep rework: correctness, speed, and the evidence bifunctor

Status: phase 1 in progress (2026-08-17). Prior-art background: `~/prog/paquari-notes/redgrep-evidence-of-absence/survey.md (private)`
and the write-up `~/prog/paquari-notes/redgrep-evidence-of-absence/evidence-of-absence.html (private)`.

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

`master` shows what works plus the write-up; the 2016 exploration lives in
git history (removed 2026-08-17 on Matthias's instruction, after the
differential tests had confirmed the old engines agreed with the new core
on their shared fragment — that agreement is recorded in the test history
and logs). The write-up stays in `notes-prior-art/`; publishing it as a
blog post is a separate, explicit step.

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
under `logs/<date>/bench/` with the commit hash — on disk only, untracked
(history rewritten 2026-08-17 to drop logs/ and the notes; commit hashes
quoted in docs from before that rewrite refer to the pre-rewrite
history). Comparisons against other
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

### Finite state machines as primitives (added 2026-08-17, from Div7)

Motivation: matthiasgoergens/Div7 expresses "decimal number divisible by 7"
by building the 7-state residue automaton and then *state-eliminating* it
into a regex — which fills a file and is unreadable. Under derivatives the
machine is native: `Machine Fsm Int` (a DFA as plain data plus its current
state) is a leaf whose derivative is a table lookup, `d_c (Machine f q) =
Machine f (δ(q,c))`, and whose nullability is acceptance. Everything else
composes for free through the algebra: Boolean combinations of machines are
lazy product constructions performed by the derivative engine, quotients are
derivative chains, invHom wraps cleanly. `divisibleBy 7` is one line, its
derivative closure is the automaton itself (~9 states, property-tested), and
`cut2 (divisibleBy 7) (contains "42")` just works.

Decisions and their reasons:
- Transitions are total by convention: missing (state, char) falls back to a
  per-state else-entry, missing else-entry falls back to the implicit dead
  state `-1`, and the smart constructor maps the dead state to `Nil` so the
  ordinary Nil-absorption laws apply.
- `rev` on a machine node subset-constructs the reversed automaton (start =
  accepting set, accept = subsets containing the original state, transitions
  = preimages; untabulated characters behave uniformly so one reversed
  else-transition covers them). Worst case 2^|Q|; machine nodes are expected
  small. This keeps `rev` total on the whole algebra.
- Phase-2 evidence for machine nodes (to be settled with phase 2): they are
  recognizer primitives, like a generalised `Sym` — success evidence is the
  consumed substring, failure evidence the rejecting state and position. No
  interior parse structure, by design.
- The planner connection: machine nodes are also the *output* format — the
  phase-4 planner compiles (fragments of) regexes into exactly this
  constructor.

These operations are for fun and are secondary: the priority is making the
original feature set (extended algebra + evidence) correct and fast.

## The Lean twin is verified (2026-08-17)

lean/ contains the executable twin (Core: RE/nullable/deriv/matchRE;
Semantics: Mathlib Language denotation), and ALL its correctness
theorems are now proved and locally verified (Aristotle project
4385f9c0; lake build clean, zero sorry, every theorem on
propext/Classical.choice/Quot.sound only): nullable_correct,
lang_deriv (lang (deriv c r) = deriv1 c (lang r)), deriv_correct, and
matchRE_correct — the executable matcher agrees with the denotation on
every input. The eight language-level laws served as the lemma library,
as designed. v2 targets: InvHom and Machine constructors in the twin,
then the phase-2 evidence types as an indexed family.

## The chase (phase 4 started early, 2026-08-17)

Matthias reframed the Lean-ceiling list (SIMD prefilters, byte-level IO)
as the target list. Rule 1 of the query planner is in
(logs/2026-08-17/bench/phase4-planner-rule1.*): `Redgrep.Plan`
structurally recognises canonical `.* lit .*` and dispatches to
bytestring's memchr-backed substring search instead of any automaton.
ping-search at 100k: planned 106 µs vs regex-tdfa 502 µs — 4.7x FASTER
than the engine that had led this workload all day, and 17x faster than
our own compiled DFA. Soundness by construction (fires only on the exact
canonical shape) plus properties tying it to the engine and to
isInfixOf.

Rule 2 (same day, logs/2026-08-17/bench/phase4-prefilter.*):
`requiredLiteral` — a sound necessary-factor analysis (per-operator:
any Cut conjunct's factor binds; only factors common to all Alt branches
survive; adjacent exact-literal Seq children concatenate; Rep/Not/
InvHom/Machine contribute nothing) — and `matchCompiledBS`, a byte-level
walker over dense 0..255 tables. Plans without a containment shape but
with a required literal become Prefiltered: memchr reject, then DFA.
Measured on flapping (∩ + ¬, required literal "ping" found through the
intersection): no-hit input 74 µs vs 377 µs unfiltered (5.1x) at 100k;
hit-input overhead ~6%. Soundness property: every claimed literal is
contained in every match (100 cases, oracle-checked strings); flapping's
literal asserted exactly.

Next rules, in payoff order: multi-literal prefilters (Teddy-style) via
FFI later; String-side engines byte-native; the same memchr trick
transfers to the Lean twin via @[extern].

## Lean as a systems language: the gap list (2026-08-18/19)

What exists: real C FFI (@[extern] + lake extern_lib, hand-written shims
against lean.h), ByteArray/unboxed scalars, Perceus RC with compile-time
reuse pairing — so dense tables walk at native speed and perf works on
the compiled binary. What's missing, in our priority order: (1) FFI
ergonomics + a trust discipline — bind memchr/memmem behind a Lean
signature whose contract is a stated proposition, property-test the
boundary, prove everything above it (planner rule 1 verified-modulo-
shim); (2) mmap and tuned byte IO; (3) SIMD only via C; (4) binary size,
cross-compilation, struct packing.

### External corroboration: zstd-in-Lean (Langley, imperialviolet.org,
2026-07-26; mined 2026-08-19)

A verified FSE/zstd decoder in Lean measured 10x slower than C zstd.
His pain points, mapped to our list (all "per the post" — read via
summariser, verify against the original before quoting): (1) THE
CENTRAL ONE, corroborating our FIP thread from a practitioner: RC
sharing is invisible — "a seemingly minor tweak can completely crater
performance by holding onto a reference to a large array somewhere
inconspicuous"; no linear/uniqueness types to make the in-place fast
path a static fact. This is independent testimony that uniqueness
VISIBILITY (checker or at minimum a may-copy diagnostic) is the single
highest-value language change. (2) Imperative-mode (Id.run) code
complicates proof automation — the invariant-carrying that makes
bounds-check elimination possible is painful exactly where the hot
loops live; Lean folk reportedly working on it. (3) Verified-assembly
route blocked: bv_decide (certifying bitblast) exhausts memory on small
examples — relevant ceiling for any future verified-SIMD ambition.
(4) Type-checker memory blowups on complicated proofs. New items for
the gap list: uniqueness visibility (top), imperative-proof automation,
bv_decide scalability. Also note his FSE workload is branchy
table-walk-plus-bit-reads — structurally our DFA loop, so the 10x is a
relevant prior for un-tuned verified Lean vs C on redgrep-shaped code.

### In-place mutation: runtime vs static (2026-08-19)

Lean's reuse is static ANALYSIS but a runtime GUARANTEE: reset/reuse
tokens are inserted at compile time, yet reset still compiles to an
isShared refcount check with a copying slow path — FBIP style reliably
hits the fast path but nothing proves it. The static answer exists one
language over: Koka's FIP ("fully in-place functional programming",
Lorenzen-Leijen-Swierstra, ICFP 2023 — citation from memory, verify),
a type discipline making zero-allocation in-place execution a
compile-time fact; the general mechanism is uniqueness/linear types.
GHC prior art to survey (all hedged, from memory): LinearTypes (Bernardy
et al., POPL 2018) — checked but does not currently drive in-place
update; destination-passing-style work in Linear Haskell (Bagrel);
demand/cardinality analysis and one-shot lambdas as the analysis-side
precedent; stream fusion as the allocation-removal precedent. Motivating
examples the FIP literature brags about (verify): red-black tree
insertion/rebalancing, Morris traversal via pointer reversal, in-place
sorting of list structures.

DECISION (Matthias, 2026-08-19): an FIP-style static checker for Lean is
interesting but NOT this project's critical path — redgrep's hot path
(compiled-DFA walk) mutates nothing; FIP concerns concentrate in
run-once builder code. Pursue in an INDEPENDENT session with its own
motivating example (start from the FIP papers' own showcases). For
redgrep, the lighter path stands: allocation bounds as theorems over an
instrumented cost semantics, model-to-runtime gap covered by
measurement.

## Aristotle usage protocol (2026-08-19, per Matthias)

Three tools, not one. (a) SATELLITES: fresh projects seeded with already-
proved lemma files, one small goal each, full budget per theorem — the
budget-exhaustion answer. (b) PROPOSALS amendment on every submission:
alternative definitions welcome as additions with equivalence proofs
(paid off immediately: matchW, derivW-as-primitive). (c) DESIGN
CONSULTATIONS: ask-mode questions mining whole-system insight — which of
our definitions cause proof friction, how to architect the next phase —
from the projects with the deepest context. Its design answers are
reported evidence like any reviewer's: check before adopting.

## Review outcomes (2026-08-17, two adversarial passes + Matthias)

Adopted immediately (in the phase-1 commit series):
- **Kleene-algebra/De Morgan law suite** as properties (star unfold,
  distributivity, De Morgan pairs, absorption, structural seq associativity)
  — the smart constructors are the crux and three ad hoc laws undersampled
  them.
- **State-space measurement**: derivative-closure size per generated regex,
  capped and distribution-collected — the one test that would have caught
  the 2016 failure mode.
- **Three-letter alphabet** for tests: with {a,b} alone, class-merge
  canonicalisation ([ab]∪[bc] vs [abc]) is structurally untestable.
- **kth-from-last regression family** `(a|b)* a (a|b)^k`, k ≤ 8, checked
  against its direct specification at lengths past the exhaustive sweep:
  distinguishing-string length grows with state count (2^(k+1) states), so
  bounded-length sweeps have a provable blind spot exactly there.
- **invHom canonicalisation**: identity entries dropped, identity maps
  collapse.

Accepted with timing:
- **Character classes as intervals/predicates instead of Set Char** — a
  representation decision, not an optimisation; scheduled together with the
  phase-3 alphabet-partitioning work that touches the same code. Set Char is
  acceptable only while the test alphabet is tiny.
- **Property-testing library**: QuickCheck is the weakest of the current
  options (Matthias: "QuickCheck is pretty bad", and he ports Hypothesis to
  Rust/OCaml). falsify-0.2.0 (Hypothesis-style internal shrinking) is in
  lts-24.55; migrate the suite once it stabilises rather than churning now.
  SmallCheck-style exhaustive term enumeration at small depths is worth
  adding at the same time (random terms undersample degenerate shapes).
- **Proof-assistant route** (Matthias is open to extraction): Tan–Urban's
  Isabelle formalisation covers POSIX lexing on the positive fragment only —
  the evidence bifunctor with ∩/¬ has no existing formalisation, so proving
  it would be new work, most naturally attempted once the phase-2 types have
  settled (Lean 4 or Agda; the survey's Dec-refutation formalisations are
  the starting points). Until then: oracle + differential + laws.
- **Mixed benchmark corpus** (Matthias): keep the synthetic/adversarial
  workloads AND add realistic text + patterns (log file, IP/timestamp/email
  shapes); also add allocation stats (+RTS -T is already visible to
  criterion), a large-alternation workload, workloads for invHom/rev/right
  quotient, and a nested-intersection stressor (see PSPACE note below).

Documented hazards (do not rediscover):
- **`rep_ (Rep x) = Rep x` is unsound for phase-2 evidence.** Language-equal
  but parse-structure-different; nested-star regrouping is run-time-
  dependent (the POSIX hard case), so no static rectification exists. The
  evidence layer must either keep its own unflattened structure keyed to the
  canonical core via the erase discipline (Tan–Urban — the intended reading
  of "folded once"), or adopt and document a policy making nested-star
  groupings interchangeable. Same warning for any future De-Morgan-style
  rewrite between cut and not/alt/not: evidence shapes differ.
- **Memo-hit cost is O(|state|) until interning lands** (structural Ord on
  cache keys); benchmark write-ups must label the core-memo column as
  "complexity class fixed, constants pending phase 3". Measured 2026-08-17:
  core-memo is 1.1–2.4× slower than plain re-derivation at current state
  sizes — the cache pays for nothing yet. With machine nodes it becomes
  pathological: on div7, core runs at ~12 ns/char while core-memo is ~1000×
  slower, because every cache probe compares the embedded transition table
  structurally (logs/2026-08-17/bench/div7-machine.*). Interning is not an
  optimisation, it is a prerequisite for the memo to exist.
- **Intersection is PSPACE-complete in general**: adversarial nested ∩/¬ can
  force genuinely exponential state sets; no canonicalisation fixes this.
  Accepted limitation; strongest argument for the phase-4 planner.
- **Keil–Thiemann Δ/∇** (positive/negative derivative pair flipping at ¬):
  implement in phase 2 as an independent boolean-level "does a refutation
  exist" check to cross-validate the mkeps-dual before trusting its shape.

Phase-3 step 1 (interned lazy DFA, logs/2026-08-17/bench/phase3-interned-dfa.*):
`matchDfa` pays the structural comparison once per distinct state (to assign
an id), then transitions are id-to-id lookups. At 100k input:
- ping-search 595 µs (was 27.9 ms plain, 47×; regex-tdfa 293 µs — within 2×).
- flapping (∩ + ¬) 604 µs (was 70 ms, 116×) — ~6 ns/char on the workload
  nothing else in the comparison set can express.
- a* 266 µs — now 2× FASTER than regex-tdfa (581 µs).
- div7 977 µs ≈ plain core (both are table walks); the matchMemo pathology
  (1.1 s) is gone. Lazy triple product 3×5×7 runs at 1.6 ms.
- evil-(a?)^n·a^n unchanged: every state in that run is visited once, so
  caching cannot help; the cost is state *construction* (big Alt-of-suffix
  terms), which is the Antimirov/marks argument — next.

Phase-3 step 2 (derivative classes + persistent compiled DFA,
logs/2026-08-17/bench/phase3-compiled.*): `classes` computes the ORT
alphabet partition per state; `compile cap` eagerly builds a reusable DFA
over it (Nothing above the state cap). Measured: many-short-strings (2000
x 20 chars) 529 µs compiled vs 16.1 ms rebuilding the lazy DFA per call —
the 30x that motivates persistence; regex-tdfa still 4.5x ahead there
(literal prefilter). On one long input matchDfa remains ~3x faster than
matchCompiled (the compiled walker scans a class list per char; a dense
char-indexed table for ASCII is the known fix, phase-3 backlog). Matcher
choice is workload-dependent — a first, tiny instance of the phase-4
planner question.

Phase-3 step 3 (dense ASCII transition tables,
logs/2026-08-17/bench/phase3-dense.*): compiled states precompute a
UArray over chars 0..127 (class-list scan kept above ASCII). Closes the
compiled-vs-lazy gap entirely: astar 270 µs (was 1.0 ms, now equal to
matchDfa and 2.2x ahead of regex-tdfa), ping-search 713 µs, flapping
874 µs, div7 676 µs — the fastest engine we have on div7 (6.8 ns/char),
and many-short-strings 271 µs, within 2.5x of regex-tdfa from 30x behind
at per-call construction. matchCompiled is now the default
recommendation for reused patterns; matchDfa remains for one-shot.

Two memory bugs found and fixed in this step (both under the standing
guard: tests now run inside `systemd-run --user --scope -p MemoryMax=6G`
plus `+RTS -M4g`):
- `refine` without dedup: class lists multiplied per leaf (2^#syms for
  nested terms) — genuine exponential memory, killed a test run at
  multi-GB. Fixed by dedup; distinct classes are bounded by the atoms of
  the Boolean algebra the leaves generate.
- `compile` threaded the whole queue through its interning fold and then
  appended it to itself: queue doubled per step, ids never grew, the cap
  never fired — infinite loop on any regex with a transition (a bare Sym
  looped). Found by tools/probe-compile.hs; the probe stays in
  the tree.

Aristotle status: all 8 language-level laws reported proved (standard
axioms only, two benign elaboration adjustments). The earlier "download
endpoint broken" diagnosis was WRONG — user error, twice over:
`--destination` names the archive FILE (a tar.gz), not a directory to
populate, and the "empty directory" was a misread `find` on what was in
fact the downloaded archive. Correct usage:
`aristotle download <id> --destination <name>.tar.gz`. Archive kept at
aristotle/redgrep-laws-881d1d9a.tar.gz. Statement-level diff done: all
defs and all 8 statements identical to what was submitted; additions are
only `open` scoping (Computability for ∗; Classical for deriv1_mul's if).
Three laws (deriv1_inter, deriv1_compl, deriv1_invHom) hold by rfl.
VERIFIED locally 2026-08-17: lake build succeeds (Lean 4.28.0, Mathlib
per the returned manifest), zero sorry, and the #print axioms audit
(logs/2026-08-17/aristotle-axioms-audit.log) shows every theorem resting
only on propext / Classical.choice / Quot.sound — with deriv1_invHom
depending on NO axioms at all (definitionally true). The proved file is
kept at aristotle/Statements-proved.lean. The engine's per-constructor
rules for ∩, ¬, ·, *, invHom, rev, and both quotients now implement
machine-checked laws rather than tested ones.

Phase-1 baseline measurements (logs/2026-08-17/bench/phase1-e317b6d.*,
GHC 9.10.3, this machine):
- Input-length scaling is linear everywhere tested (flapping at 100k chars:
  ~74 ms; the 2016 engines could not leave 3-digit inputs).
- vs regex-tdfa: ~1.6× slower on a*, ~100× slower on literal search
  (tdfa prefilters; planner territory), catastrophically slower on
  (a?)^n a^n as pattern size grows (big Alt-of-suffixes states rebuilt per
  char — the Antimirov/marks argument, phase 3).
- vs regex-applicative: faster on a* at all sizes; slower on literal search.

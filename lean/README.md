# Lean twin of the redgrep core

This is the verified reference twin of the Haskell engine (see DESIGN.md for
the phase plan): `Core.lean` mirrors `src/Redgrep/Core.hs` as executable
structural recursion (`RE`, `nullable`, `deriv`, `matchRE`), `Semantics.lean`
gives the denotation into Mathlib's `Language Char`, `Statements.lean` is the
verbatim copy of the eight language-level laws already proved by Aristotle
(`aristotle/Statements-proved.lean`), and `Correctness.lean` states the three
theorems connecting engine to denotation — `nullable_correct`,
`deriv_correct`, `matchRE_correct`. The twin deliberately simplifies where
canonicity is a Haskell-side performance concern: `alt`/`cut` are binary
rather than canonical sets, `sym` is a predicate, and the `InvHom`/`Machine`
constructors are deferred to v2.

The `sorry`s in `Correctness.lean` are intentional: the statements are the
load-bearing part, and filling them is later work for local `/lean4` sessions
plus Aristotle (each docstring records which proved law in `Statements.lean`
covers which case of the induction). For making the verified engine *fast*
rather than merely correct, the study object is
[pandaman64/lean-regex](https://github.com/pandaman64/lean-regex), a verified
regex engine whose optimisation history is worth mining. Build with
`lake exe cache get` then `lake build`; the toolchain and manifest are pinned
to the same Lean v4.28.0 / Mathlib versions as the Aristotle project so the
local Mathlib cache is reused.

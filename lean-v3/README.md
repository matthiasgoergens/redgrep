# Lean twin of the redgrep core, v3 — ACI + bounds

v3 brings the twin up to what the Haskell engine actually does: comparable
character classes (`Cls`, a `Finset Char` or its complement, so `RE` has
derived decidable equality and a total order `RE.cmp`) and ACI
canonicalisation (smart constructors `altL`/`cutL`/`seq2`/`rep_`/`not_`/
`sym`/`invHom_` that flatten, sort, deduplicate and apply unit/absorbing
laws, with the engine routed through them). Representation choice: binary
`alt`/`cut` constructors plus a `canon : RE → RE` normalisation function and
a decidable `Canonical` predicate, rather than `Finset RE`/sorted-`List RE`
fields — the nested-inductive routes block `deriving DecidableEq` and every
recursion, and the point of canonicity here is quantitative, not
representational (rationale in the `Core.lean` docstring). The payoff is
`Bounds.lean`: the reachable-derivative closure, the bounding function `B`
with the classical per-constructor recurrences, and the `closure_finite` /
`closure_ncard_le` statements that only make sense once derivatives are kept
in ACI normal form.

v2 (`lean/`) stays the verified reference until v3's theorems are re-proved:
everything in `Correctness.lean` and `Bounds.lean` here is deliberately
`sorry` — the statements are the deliverable of this draft, and they are to
be reviewed before any prover (local `/lean4` sessions, then Aristotle) sees
them. `Statements.lean` is the verbatim, fully-proved v2 copy of the
language-level laws and carries no sorries. Build as for v2 (see
`lean/README.md`): the toolchain and manifest are pinned to the same
Lean v4.28.0 / Mathlib, `.lake/packages` was reflinked from `lean/`, then
`lake exe cache get && lake build`.

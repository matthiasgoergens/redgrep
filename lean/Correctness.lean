import Semantics
import Statements

/-!
# Redgrep correctness statements

The three theorems tying the executable engine (`Core.lean`) to its
denotational specification (`Semantics.lean`).  Statements only — the
proofs are intended for local `/lean4` work plus Aristotle.  The
language-level laws already proved in `Statements.lean` cover the hard
cases of the inductions; each docstring below records which law covers
which constructor case.
-/

namespace Redgrep

/-- The engine's `nullable` decides membership of the empty string.

Proof plan: induction on `r`.  Every case is close to definitional
unfolding of `lang`: `sym` (a singleton `[c]` is never `[]`), `alt`/`cut`
(`[] ∈ L₁ ⊔ L₂` / `L₁ ⊓ L₂` splits pointwise), `seq` (`[] ∈ L₁ * L₂` iff
`[] ∈ L₁` and `[] ∈ L₂`, via `Language.nil_mem_mul` or the like), `rep`
(`[] ∈ L∗` always, `Language.nil_mem_kstar`), `not` (complement flips
membership), `eps`/`nil` trivial. -/
theorem nullable_correct (r : RE) : nullable r = true ↔ ([] : List Char) ∈ lang r := by
  sorry

/-- The engine's `deriv` computes the Brzozowski derivative of the
denotation: `lang (deriv c r) = deriv1 c (lang r)` pointwise.

Proof plan: induction on `r`.  The per-constructor laws proved in
`Statements.lean` cover the interesting cases: `cut` is `deriv1_inter`
(and `alt` its dual for `⊔`, which holds by `rfl` the same way), `not`
is `deriv1_compl`, `seq` is `deriv1_mul` (whose `if [] ∈ L₁` guard is
discharged by `nullable_correct`), and `rep` is `deriv1_kstar`.  The
`sym`/`eps`/`nil` cases are direct unfolding. -/
theorem deriv_correct (c : Char) (r : RE) (w : List Char) :
    w ∈ lang (deriv c r) ↔ (c :: w) ∈ lang r := by
  sorry

/-- Full-match correctness: the engine agrees with the denotation on
every input string.

Proof plan: induction on `s` generalising `r`; the step is
`deriv_correct`, the base is `nullable_correct`. -/
theorem matchRE_correct (r : RE) (s : List Char) : matchRE r s = true ↔ s ∈ lang r := by
  sorry

end Redgrep

import Semantics
import Statements

open Language Computability

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
  induction r with
  | sym cls =>
      show false = true ↔ ∃ c, cls c = true ∧ ([] : List Char) = [c]
      simp
  | alt r₁ r₂ ih₁ ih₂ =>
      show (nullable r₁ || nullable r₂) = true ↔ [] ∈ lang r₁ ∨ [] ∈ lang r₂
      simp [ih₁, ih₂]
  | cut r₁ r₂ ih₁ ih₂ =>
      show (nullable r₁ && nullable r₂) = true ↔ [] ∈ lang r₁ ∧ [] ∈ lang r₂
      simp [ih₁, ih₂]
  | seq r₁ r₂ ih₁ ih₂ =>
      simp [nullable, lang, ih₁, ih₂, Language.mem_mul]
  | rep r ih =>
      simp [nullable, lang, Language.nil_mem_kstar]
  | not r ih =>
      show (!nullable r) = true ↔ ¬ ([] ∈ lang r)
      rw [Bool.not_eq_true', ← ih]
      simp
  | eps => simp [nullable, lang]
  | nil => simp [nullable, lang]

/-- Auxiliary form of `deriv_correct`: the denotation of the syntactic
derivative is the Brzozowski derivative of the denotation, as languages. -/
theorem lang_deriv (c : Char) (r : RE) : lang (deriv c r) = deriv1 c (lang r) := by
  induction r with
  | sym cls =>
      by_cases h : cls c = true
      · ext w
        show w ∈ lang (if cls c then RE.eps else RE.nil) ↔ (c :: w) ∈ lang (RE.sym cls)
        rw [if_pos h]
        show w ∈ (1 : Language Char) ↔ ∃ d, cls d = true ∧ c :: w = [d]
        simp [Language.mem_one, h]
      · ext w
        show w ∈ lang (if cls c then RE.eps else RE.nil) ↔ (c :: w) ∈ lang (RE.sym cls)
        rw [if_neg h]
        show w ∈ (0 : Language Char) ↔ ∃ d, cls d = true ∧ c :: w = [d]
        simp [h]
  | alt r₁ r₂ ih₁ ih₂ =>
      show lang (deriv c r₁) ⊔ lang (deriv c r₂) = deriv1 c (lang r₁ ⊔ lang r₂)
      rw [ih₁, ih₂]; rfl
  | cut r₁ r₂ ih₁ ih₂ =>
      show lang (deriv c r₁) ⊓ lang (deriv c r₂) = deriv1 c (lang r₁ ⊓ lang r₂)
      rw [ih₁, ih₂, deriv1_inter]
  | seq r₁ r₂ ih₁ ih₂ =>
      show lang (if nullable r₁ then _ else _) = deriv1 c (lang r₁ * lang r₂)
      rw [deriv1_mul]
      by_cases h : nullable r₁ = true
      · have hnil : ([] : List Char) ∈ lang r₁ := (nullable_correct r₁).mp h
        rw [if_pos h, if_pos hnil]
        show lang (deriv c r₁) * lang r₂ ⊔ lang (deriv c r₂) = _
        rw [ih₁, ih₂]
      · have hnil : ([] : List Char) ∉ lang r₁ := fun hm => h ((nullable_correct r₁).mpr hm)
        rw [if_neg h, if_neg hnil]
        show lang (deriv c r₁) * lang r₂ = _
        rw [ih₁, sup_bot_eq]
  | rep r ih =>
      show lang (deriv c r) * (lang r)∗ = deriv1 c ((lang r)∗)
      rw [ih, deriv1_kstar]
  | not r ih =>
      show (lang (deriv c r))ᶜ = deriv1 c ((lang r)ᶜ)
      rw [ih, deriv1_compl]
  | eps =>
      ext w
      show w ∈ (0 : Language Char) ↔ (c :: w) ∈ (1 : Language Char)
      simp [Language.mem_one]
  | nil =>
      ext w
      show w ∈ (0 : Language Char) ↔ (c :: w) ∈ (0 : Language Char)
      simp

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
  rw [lang_deriv]; rfl

/-- Full-match correctness: the engine agrees with the denotation on
every input string.

Proof plan: induction on `s` generalising `r`; the step is
`deriv_correct`, the base is `nullable_correct`. -/
theorem matchRE_correct (r : RE) (s : List Char) : matchRE r s = true ↔ s ∈ lang r := by
  induction s generalizing r with
  | nil => exact nullable_correct r
  | cons c t ih =>
      show matchRE (deriv c r) t = true ↔ (c :: t) ∈ lang r
      rw [ih (deriv c r)]
      exact deriv_correct c r t

end Redgrep

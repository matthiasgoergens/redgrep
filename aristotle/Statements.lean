/-
Language-level laws behind redgrep's derivative engine (see README.md).

`Language α` is Mathlib's `Set (List α)` with `*` = concatenation,
`∗` = Kleene star, `⊓` = intersection, `ᶜ` = complement, `⊥` = empty.

The definitions below are the semantic counterparts of the engine's
operations; each theorem is the law a per-constructor rule implements.
API names (flatMap/bind/flatten/join) may be adapted to the Mathlib in
use, but the MEANING of each statement must be preserved exactly.
-/
import Mathlib.Computability.Language

open Language

variable {α : Type*}

/-- Brzozowski derivative by one character. -/
def deriv1 (c : α) (L : Language α) : Language α := {w | c :: w ∈ L}

/-- Derivative by a word (left quotient). -/
def derivW (u : List α) (L : Language α) : Language α := {w | u ++ w ∈ L}

/-- Language reversal. -/
def revLang (L : Language α) : Language α := {w | w.reverse ∈ L}

/-- Inverse image under a string homomorphism h (extended pointwise). -/
def invHom (h : α → List α) (L : Language α) : Language α :=
  {w | (w.flatMap h) ∈ L}

/- Boolean operations commute with the derivative. -/
theorem deriv1_inter (c : α) (L₁ L₂ : Language α) :
    deriv1 c (L₁ ⊓ L₂) = deriv1 c L₁ ⊓ deriv1 c L₂ := by sorry

theorem deriv1_compl (c : α) (L : Language α) :
    deriv1 c (Lᶜ) = (deriv1 c L)ᶜ := by sorry

/- Concatenation: split blame between the two factors. -/
theorem deriv1_mul (c : α) (L₁ L₂ : Language α) :
    deriv1 c (L₁ * L₂) =
      deriv1 c L₁ * L₂ ⊔ (if ([] : List α) ∈ L₁ then deriv1 c L₂ else ⊥) := by
  sorry

/- Star: the nonempty-first-chunk argument makes this hold even when
   [] ∈ L. -/
theorem deriv1_kstar (c : α) (L : Language α) :
    deriv1 c (L∗) = deriv1 c L * L∗ := by sorry

/- Star membership needs only decompositions into nonempty chunks
   (the oracle's rep case). -/
theorem kstar_nonempty_chunks (L : Language α) (w : List α) :
    w ∈ L∗ ↔
      ∃ l : List (List α), (∀ x ∈ l, x ∈ L ∧ x ≠ []) ∧ l.flatten = w := by
  sorry

/- The inverse-homomorphism derivative rule: derive by the image string. -/
theorem deriv1_invHom (h : α → List α) (c : α) (L : Language α) :
    deriv1 c (invHom h L) = invHom h (derivW (h c) L) := by sorry

/- Reversal commutes with inverse homomorphism via the reversed hom. -/
theorem revLang_invHom (h : α → List α) (L : Language α) :
    revLang (invHom h L) = invHom (fun c => (h c).reverse) (revLang L) := by
  sorry

/- Right quotient by a suffix via reversal. -/
theorem rightQuot_via_rev (u : List α) (L : Language α) :
    {w | w ++ u ∈ L} = revLang (derivW u.reverse (revLang L)) := by sorry

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

open Language Computability

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
    deriv1 c (L₁ ⊓ L₂) = deriv1 c L₁ ⊓ deriv1 c L₂ := rfl

theorem deriv1_compl (c : α) (L : Language α) :
    deriv1 c (Lᶜ) = (deriv1 c L)ᶜ := rfl

/- Concatenation: split blame between the two factors. -/
open Classical in
theorem deriv1_mul (c : α) (L₁ L₂ : Language α) :
    deriv1 c (L₁ * L₂) =
      deriv1 c L₁ * L₂ ⊔ (if ([] : List α) ∈ L₁ then deriv1 c L₂ else ⊥) := by
  ext w
  simp only [deriv1, Language.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    match a, hab with
    | [], hab =>
      refine Or.inr ?_
      simp only [List.nil_append] at hab
      rw [if_pos ha]
      simpa [hab] using hb
    | (d :: a'), hab =>
      left
      simp only [List.cons_append, List.cons.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨a', ha, b, hb, rfl⟩
  · rintro (⟨a, ha, b, hb, rfl⟩ | h)
    · exact ⟨c :: a, ha, b, hb, rfl⟩
    · by_cases hnil : ([] : List α) ∈ L₁
      · rw [if_pos hnil] at h
        exact ⟨[], hnil, c :: w, h, rfl⟩
      · rw [if_neg hnil] at h
        exact absurd h (Set.notMem_empty _)

/- Star: the nonempty-first-chunk argument makes this hold even when
   [] ∈ L. -/
theorem deriv1_kstar (c : α) (L : Language α) :
    deriv1 c (L∗) = deriv1 c L * L∗ := by
  ext w
  simp only [deriv1, Language.mem_mul]
  constructor
  · intro h
    obtain ⟨S, hS, hmem⟩ := Language.mem_kstar_iff_exists_nonempty.mp h
    match S, hS with
    | [], hS => simp at hS
    | (s :: T), hS =>
      obtain ⟨hs, hsne⟩ := hmem s (by simp)
      match s, hs, hsne with
      | [], _, hsne => exact absurd rfl hsne
      | (d :: s'), hs, _ =>
        simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hS
        obtain ⟨rfl, rfl⟩ := hS
        refine ⟨s', hs, T.flatten, ?_, rfl⟩
        exact Language.join_mem_kstar fun y hy => (hmem y (by simp [hy])).1
  · rintro ⟨a, ha, b, hb, rfl⟩
    show c :: (a ++ b) ∈ L∗
    have hmem : (c :: a) ++ b ∈ L * L∗ := Language.append_mem_mul ha hb
    exact Set.mem_of_mem_of_subset hmem (mul_kstar_le_kstar (a := L))

/- Star membership needs only decompositions into nonempty chunks
   (the oracle's rep case). -/
theorem kstar_nonempty_chunks (L : Language α) (w : List α) :
    w ∈ L∗ ↔
      ∃ l : List (List α), (∀ x ∈ l, x ∈ L ∧ x ≠ []) ∧ l.flatten = w := by
  rw [Language.mem_kstar_iff_exists_nonempty]
  constructor
  · rintro ⟨S, rfl, h⟩; exact ⟨S, h, rfl⟩
  · rintro ⟨S, h, rfl⟩; exact ⟨S, rfl, h⟩

/- The inverse-homomorphism derivative rule: derive by the image string. -/
theorem deriv1_invHom (h : α → List α) (c : α) (L : Language α) :
    deriv1 c (invHom h L) = invHom h (derivW (h c) L) := rfl

/-- Reversing a `flatMap` by the pointwise-reversed hom reverses the argument list. -/
private theorem reverse_flatMap_reverse (h : α → List α) (w : List α) :
    (w.flatMap fun c => (h c).reverse).reverse = w.reverse.flatMap h := by
  induction w with
  | nil => simp
  | cons d t ih => simp [List.flatMap_cons, List.reverse_append, ih]

/- Reversal commutes with inverse homomorphism via the reversed hom. -/
theorem revLang_invHom (h : α → List α) (L : Language α) :
    revLang (invHom h L) = invHom (fun c => (h c).reverse) (revLang L) := by
  ext w
  show w.reverse.flatMap h ∈ L ↔ (w.flatMap fun c => (h c).reverse).reverse ∈ L
  rw [reverse_flatMap_reverse]

/- Right quotient by a suffix via reversal. -/
theorem rightQuot_via_rev (u : List α) (L : Language α) :
    {w | w ++ u ∈ L} = revLang (derivW u.reverse (revLang L)) := by
  ext w
  show w ++ u ∈ L ↔ (u.reverse ++ w.reverse).reverse ∈ L
  rw [List.reverse_append, List.reverse_reverse, List.reverse_reverse]

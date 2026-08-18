import Semantics
import Statements

/-!
# Correctness statements for the v3 engine (all `sorry` for now)

Two groups of contracts, both against the denotation `lang` in
`Semantics.lean`:

1. **The engine contract**, verbatim from v2: `nullable_correct`,
   `lang_derivW`, `lang_deriv`, `deriv_correct`, `matchRE_correct`.
2. **The canonicalisation contract**, new in v3: every smart constructor
   denotes exactly the language of the plain constructor it replaces, and
   `canon` is language-preserving and idempotent.  These are what let every
   v2-style proof be replayed over the smart-constructor-routed engine, and
   they are the semantic side of the ACI story that `Bounds.lean` counts.

The statements are the load-bearing part; filling the `sorry`s is later work
for local `/lean4` sessions plus Aristotle (the v2 proofs in
`lean/Correctness.lean` are the blueprint — each case there transfers once
the group-2 lemmas rewrite smart constructors to plain ones).
-/

open Language Computability

namespace Redgrep

/-! ### Group 1: the engine contract (statements as in v2) -/

theorem nullable_correct (r : RE) :
    nullable r = true ↔ ([] : List Char) ∈ lang r := by
  sorry

/-- The word derivative of the engine denotes the left quotient. -/
theorem lang_derivW (u : List Char) (r : RE) :
    lang (derivW u r) = _root_.derivW u (lang r) := by
  sorry

theorem lang_deriv (c : Char) (r : RE) :
    lang (deriv c r) = deriv1 c (lang r) := by
  sorry

theorem deriv_correct (c : Char) (r : RE) (w : List Char) :
    w ∈ lang (deriv c r) ↔ (c :: w) ∈ lang r := by
  sorry

theorem matchRE_correct (r : RE) (s : List Char) :
    matchRE r s = true ↔ s ∈ lang r := by
  sorry

/-! ### Group 2: the canonicalisation contract

Each smart constructor preserves the denotation of the plain construction it
canonicalises.  n-ary constructors are stated in membership form (the `⋃`/`⋂`
over a list, unfolded) to keep the statements elaboration-robust. -/

/-- Smart `sym` agrees with the constructor (empty class ↦ `0`, class
normalisation is language-preserving). -/
theorem lang_smart_sym (cls : Cls) : lang (sym cls) = lang (.sym cls) := by
  sorry

/-- `altL` denotes the union of its members' languages. -/
theorem mem_lang_altL (rs : List RE) (w : List Char) :
    w ∈ lang (altL rs) ↔ ∃ r ∈ rs, w ∈ lang r := by
  sorry

theorem lang_alt2 (r₁ r₂ : RE) : lang (alt2 r₁ r₂) = lang r₁ ⊔ lang r₂ := by
  sorry

/-- `cutL` denotes the intersection of its members' languages (the empty
intersection is `Σ*`). -/
theorem mem_lang_cutL (rs : List RE) (w : List Char) :
    w ∈ lang (cutL rs) ↔ ∀ r ∈ rs, w ∈ lang r := by
  sorry

theorem lang_cut2 (r₁ r₂ : RE) : lang (cut2 r₁ r₂) = lang r₁ ⊓ lang r₂ := by
  sorry

theorem lang_seq2 (r₁ r₂ : RE) : lang (seq2 r₁ r₂) = lang r₁ * lang r₂ := by
  sorry

theorem lang_rep_ (r : RE) : lang (rep_ r) = (lang r)∗ := by
  sorry

theorem lang_not_ (r : RE) : lang (not_ r) = (lang r)ᶜ := by
  sorry

theorem lang_invHom_ (h : List (Char × List Char)) (r : RE) :
    lang (invHom_ h r) = _root_.invHom (applyHom h) (lang r) := by
  sorry

/-- `canon` is language-preserving: canonicalisation is free, semantically. -/
theorem canon_correct (r : RE) : lang (canon r) = lang r := by
  sorry

/-- `canon` lands in canonical form: the smart constructors are closed under
each other, i.e. normalisation is idempotent. -/
theorem canon_canonical (r : RE) : Canonical (canon r) := by
  sorry

end Redgrep

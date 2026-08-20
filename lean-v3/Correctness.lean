import Semantics
import Statements
import Engine
import ACI

/-!
# Correctness statements for the v3 engine

Two groups of contracts, both against the denotation `lang` in
`Semantics.lean`:

1. **The engine contract**, verbatim from v2: `nullable_correct`,
   `lang_derivW`, `lang_deriv`, `deriv_correct`, `matchRE_correct`.
2. **The canonicalisation contract**, new in v3: every smart constructor
   denotes exactly the language of the plain constructor it replaces, and
   `canon` is language-preserving and idempotent.  These are what let every
   v2-style proof be replayed over the smart-constructor-routed engine, and
   they are the semantic side of the ACI story that `Bounds.lean` counts.

All statements are proved unconditionally.

## Provenance of the hom invariant

An earlier version of `invHom_`/`homNorm` dropped identity entries from the
association list *before* restoring the "unique keys" invariant that the
Haskell original inherits from `Map Char String`.  Since `applyHom` resolves a
key by **first hit wins**, that was unsound on lists with duplicate keys: for

```
h₀ = [('a', ['a']), ('a', [])] ,  applyHom h₀ = fun c => [c] ,
oldHomNorm h₀ = [('a', [])]    ,  applyHom (oldHomNorm h₀) 'a' = [] ,
```

the regex `h₀⁻¹([a])` (language `{"a"}`) stepped to a state accepting `"a"`
again, refuting `lang_derivW`, `lang_deriv`, `deriv_correct`,
`matchRE_correct`, `lang_invHom_` and `canon_correct` as stated.  That
counterexample is what motivated the current normal form, which deduplicates
by key (keeping the first binding) before filtering, and hence preserves the
denoted homomorphism pointwise (`homNorm_applyHom`).  With the invariant
restored, all six statements hold with no side condition, and the refutations
and their `HomsStable`-guarded repairs have been removed.
-/

open Language Computability

namespace Redgrep

/-! ### Group 1: the engine contract (statements as in v2) -/

theorem nullable_correct (r : RE) :
    nullable r = true ↔ ([] : List Char) ∈ lang r :=
  nullable_iff r

/-- The word derivative of the engine denotes the left quotient. -/
theorem lang_derivW (u : List Char) (r : RE) :
    lang (derivW u r) = _root_.derivW u (lang r) :=
  lang_derivW_eq u r

theorem lang_deriv (c : Char) (r : RE) :
    lang (deriv c r) = deriv1 c (lang r) :=
  lang_deriv_eq c r

theorem deriv_correct (c : Char) (r : RE) (w : List Char) :
    w ∈ lang (deriv c r) ↔ (c :: w) ∈ lang r := by
  rw [lang_deriv_eq c r]
  exact Iff.rfl

theorem matchRE_correct (r : RE) (s : List Char) :
    matchRE r s = true ↔ s ∈ lang r :=
  matchRE_iff r s

/-! ### Regression test: the duplicate-key witness

`h₀` is the association list from the counterexample that refuted the
statements above under the old normal form: `applyHom h₀` is the identity
(first hit wins, `('a', ['a'])`), while filtering identity entries *before*
deduplicating by key exposed the shadowed `('a', [])` and erased `'a'`.  With
the dedup-by-key step in place, `homNorm h₀` is empty and `invHom_ h₀`
collapses to its body, as it must. -/

/-- The duplicate-key association list of the historical counterexample; it
denotes the identity homomorphism. -/
def h₀ : List (Char × List Char) := [('a', ['a']), ('a', [])]

/-- The historical counterexample witness: `h₀⁻¹([a])`, of language `{"a"}`. -/
def r₀ : RE := .invHom h₀ (.sym (.pos {'a'}))

theorem applyHom_h₀ (c : Char) : applyHom h₀ c = [c] := by
  unfold applyHom h₀
  by_cases h : c = 'a'
  · subst h; rfl
  · rw [show (List.find? (fun p => p.1 == c) [('a', ['a']), ('a', [])]) = none from by
      simp [List.find?, show ('a' == c) = false from by simpa using Ne.symm h]]

theorem homNorm_h₀ : homNorm h₀ = [] := by
  rw [homNorm, h₀, homDedupKeys]
  simp [homDedupKeys]

/-- Normalisation now keeps `h₀` an identity homomorphism, so the smart
constructor discards the node entirely. -/
theorem invHom_smart_h₀ {r : RE} (hr : r ≠ .nil) : invHom_ h₀ r = r := by
  rw [invHom_eq_ite, if_neg hr, if_pos homNorm_h₀]

/-- `lang r₀ = {"a"}`. -/
theorem mem_lang_r₀ (w : List Char) : w ∈ lang r₀ ↔ w = ['a'] := by
  show w.flatMap (applyHom h₀) ∈ lang (RE.sym (.pos {'a'})) ↔ _
  rw [show applyHom h₀ = (fun c => [c]) from funext applyHom_h₀, flatMap_singleton_self]
  simp only [Smart.mem_lang_sym]
  constructor
  · rintro ⟨c, hc, rfl⟩
    simp only [inCls, decide_eq_true_eq, Finset.mem_singleton] at hc
    rw [hc]
  · rintro rfl
    exact ⟨'a', by simp [inCls], rfl⟩

theorem matchRE_r₀_a : matchRE r₀ ['a'] = true :=
  (matchRE_correct r₀ ['a']).mpr ((mem_lang_r₀ ['a']).mpr rfl)

/-- The engine no longer accepts `"aa"`: the unsoundness is gone. -/
theorem matchRE_r₀_aa : matchRE r₀ ['a', 'a'] = false := by
  rw [Bool.eq_false_iff, ne_eq, matchRE_correct, mem_lang_r₀]
  simp

/-! ### Group 2: the canonicalisation contract

Each smart constructor preserves the denotation of the plain construction it
canonicalises.  n-ary constructors are stated in membership form (the `⋃`/`⋂`
over a list, unfolded) to keep the statements elaboration-robust. -/

/-- Smart `sym` agrees with the constructor (empty class ↦ `0`, class
normalisation is language-preserving). -/
theorem lang_smart_sym (cls : Cls) : lang (sym cls) = lang (.sym cls) :=
  Smart.lang_smart_sym cls

/-- `altL` denotes the union of its members' languages. -/
theorem mem_lang_altL (rs : List RE) (w : List Char) :
    w ∈ lang (altL rs) ↔ ∃ r ∈ rs, w ∈ lang r :=
  Smart.mem_lang_altL rs w

theorem lang_alt2 (r₁ r₂ : RE) : lang (alt2 r₁ r₂) = lang r₁ ⊔ lang r₂ :=
  Smart.lang_alt2 r₁ r₂

/-- `cutL` denotes the intersection of its members' languages (the empty
intersection is `Σ*`). -/
theorem mem_lang_cutL (rs : List RE) (w : List Char) :
    w ∈ lang (cutL rs) ↔ ∀ r ∈ rs, w ∈ lang r :=
  Smart.mem_lang_cutL rs w

theorem lang_cut2 (r₁ r₂ : RE) : lang (cut2 r₁ r₂) = lang r₁ ⊓ lang r₂ :=
  Smart.lang_cut2 r₁ r₂

theorem lang_seq2 (r₁ r₂ : RE) : lang (seq2 r₁ r₂) = lang r₁ * lang r₂ :=
  Smart.lang_seq2 r₁ r₂

theorem lang_rep_ (r : RE) : lang (rep_ r) = (lang r)∗ :=
  Smart.lang_rep_ r

theorem lang_not_ (r : RE) : lang (not_ r) = (lang r)ᶜ :=
  Smart.lang_not_ r

/-! #### `lang_invHom_` -/

/-- The smart inverse homomorphism denotes the inverse image of the
homomorphism its association list denotes: normalisation is meaning-preserving
(`homNorm_applyHom`). -/
theorem lang_invHom_ (h : List (Char × List Char)) (r : RE) :
    lang (invHom_ h r) = _root_.invHom (applyHom h) (lang r) :=
  lang_invHom_smart h r

/-! #### `canon_correct` -/

/-- `canon` is language-preserving: canonicalisation is free, semantically. -/
theorem canon_correct (r : RE) : lang (canon r) = lang r := by
  induction r with
  | sym cl => exact Smart.lang_smart_sym cl
  | alt a b iha ihb =>
    show lang (alt2 (canon a) (canon b)) = _
    rw [Smart.lang_alt2, iha, ihb]
    rfl
  | cut a b iha ihb =>
    show lang (cut2 (canon a) (canon b)) = _
    rw [Smart.lang_cut2, iha, ihb]
    rfl
  | seq a b iha ihb =>
    show lang (seq2 (canon a) (canon b)) = _
    rw [Smart.lang_seq2, iha, ihb]
    rfl
  | rep a ih =>
    show lang (rep_ (canon a)) = _
    rw [Smart.lang_rep_, ih]
    rfl
  | not a ih =>
    show lang (not_ (canon a)) = _
    rw [Smart.lang_not_, ih]
    rfl
  | invHom hh a ih =>
    show lang (invHom_ hh (canon a)) = _
    rw [lang_invHom_smart, ih]
    rfl
  | eps => rfl
  | nil => rfl

/-- `canon` lands in canonical form: the smart constructors are closed under
each other, i.e. normalisation is idempotent. -/
theorem canon_canonical (r : RE) : Canonical (canon r) := canon_idem r

end Redgrep

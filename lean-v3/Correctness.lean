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

## Status of the statements as originally written

Everything that is true as stated is proved below.  Six of the statements are
**refuted** as stated, all for one and the same reason, which is a property of
the *fixed* definitions in `Core.lean` and not of the proofs:

* `invHom_ h r` replaces the association list `h` by `homNorm h` (identity
  entries dropped, then sorted and deduplicated), while `applyHom` resolves a
  key by **first hit wins**.  For an `h` with *duplicate keys* those two
  disagree, e.g. for

  ```
  h₀ = [('a', ['a']), ('a', [])] ,  applyHom h₀ = fun c => [c] ,
  homNorm h₀ = [('a', [])]       ,  applyHom (homNorm h₀) 'a' = [] .
  ```

  `Core.lean` calls duplicate keys "the caller's mistake and merely
  tolerated", so this is a genuine gap between the smart constructor and the
  unguarded contract, not a repairable proof.

The affected statements — `lang_derivW`, `lang_deriv`, `deriv_correct`,
`matchRE_correct`, `lang_invHom_`, `canon_correct` — are kept verbatim but
commented out, each accompanied by

* a **formal refutation** (`not_lang_derivW`, …), i.e. a proof of the negation
  of the statement as written, all using the single witness `r₀` below, and
* a **corrected version** carrying the side condition `HomsStable`
  (`Engine.lean`): every `invHom` node of the term denotes the same
  homomorphism before and after `homNorm`.  The condition is automatic for
  terms without `invHom` nodes, for every association list with pairwise
  distinct keys (`HomWF.homStable`), and for everything the engine itself
  builds (`homNorm` is idempotent), so the corrected statements cover every
  intended use.
-/

open Language Computability

namespace Redgrep

/-! ### Group 1: the engine contract (statements as in v2) -/

theorem nullable_correct (r : RE) :
    nullable r = true ↔ ([] : List Char) ∈ lang r :=
  nullable_iff r

/-! #### The counterexample witness

`h₀` denotes the identity homomorphism (`applyHom` takes the *first* hit,
`('a', ['a'])`), but `homNorm h₀` deletes that entry as an identity entry and
so exposes `('a', [])`: after normalisation `'a'` is erased.  `r₀` is the
regex `h₀⁻¹([a])`, whose language is `{"a"}`. -/

/-- An association list with duplicate keys: `applyHom` is the identity, its
`homNorm` is not. -/
def h₀ : List (Char × List Char) := [('a', ['a']), ('a', [])]

/-- The refutation witness: `h₀⁻¹([a])`, a regex whose language is `{"a"}`. -/
def r₀ : RE := .invHom h₀ (.sym (.pos {'a'}))

/-- The engine state reached from `r₀` after reading `"a"`. -/
def d₀ : RE := .invHom [('a', ([] : List Char))] .eps

theorem applyHom_h₀ (c : Char) : applyHom h₀ c = [c] := by
  unfold applyHom h₀
  by_cases h : c = 'a'
  · subst h; rfl
  · rw [show (List.find? (fun p => p.1 == c) [('a', ['a']), ('a', [])]) = none from by
      simp [List.find?, show ('a' == c) = false from by simpa using Ne.symm h]]

theorem homNorm_h₀ : homNorm h₀ = [('a', ([] : List Char))] := by
  simp [homNorm, h₀]

theorem invHom_smart_h₀ {r : RE} (hr : r ≠ .nil) :
    invHom_ h₀ r = .invHom [('a', ([] : List Char))] r := by
  rw [invHom_eq_ite]
  simp [hr, homNorm_h₀]

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

/-- After `homNorm`, the letter `'a'` is erased, so `"a"` *is* in the language
of the derived state `d₀`. -/
theorem mem_lang_d₀ : ['a'] ∈ lang d₀ := by
  show (['a'] : List Char).flatMap (applyHom [('a', ([] : List Char))]) ∈ lang RE.eps
  simp [applyHom, Smart.mem_lang_eps]

/-- One step of the engine from `r₀` lands in `d₀`. -/
theorem deriv_r₀ : deriv 'a' r₀ = d₀ := by
  show invHom_ h₀ (derivW (applyHom h₀ 'a') (RE.sym (.pos {'a'}))) = d₀
  rw [applyHom_h₀, show derivW ['a'] (RE.sym (.pos {'a'})) = RE.eps from by
    rw [derivW]; simp [inCls]]
  exact invHom_smart_h₀ (by simp)

theorem derivW_r₀ : derivW ['a'] r₀ = d₀ := by
  rw [show r₀ = RE.invHom h₀ (.sym (.pos {'a'})) from rfl, derivW]
  rw [show (['a'] : List Char).flatMap (applyHom h₀) = ['a'] from by
      simp [applyHom_h₀],
    show derivW ['a'] (RE.sym (.pos {'a'})) = RE.eps from by rw [derivW]; simp [inCls]]
  exact invHom_smart_h₀ (by simp)

/-! #### `lang_derivW` -/

/-
theorem lang_derivW (u : List Char) (r : RE) :
    lang (derivW u r) = _root_.derivW u (lang r) := by
  sorry
-/
-- REFUTED as stated (duplicate keys in the association list of an `invHom`
-- node; see the module docstring).  Corrected form: `lang_derivW_of_stable`.

theorem not_lang_derivW :
    ¬ ∀ (u : List Char) (r : RE), lang (derivW u r) = _root_.derivW u (lang r) := by
  intro h
  have := h ['a'] r₀
  rw [derivW_r₀] at this
  have hmem : (['a'] : List Char) ∈ _root_.derivW ['a'] (lang r₀) := this ▸ mem_lang_d₀
  rw [mem_derivW, mem_lang_r₀] at hmem
  simp at hmem

/-- The corrected `lang_derivW`: the word derivative of the engine denotes the
left quotient, for every term whose `invHom` nodes survive `homNorm`. -/
theorem lang_derivW_of_homsStable (u : List Char) (r : RE) (h : HomsStable r) :
    lang (derivW u r) = _root_.derivW u (lang r) :=
  lang_derivW_of_stable u r h

/-! #### `lang_deriv` -/

/-
theorem lang_deriv (c : Char) (r : RE) :
    lang (deriv c r) = deriv1 c (lang r) := by
  sorry
-/
-- REFUTED as stated; corrected form: `lang_deriv_of_homsStable`.

theorem not_lang_deriv :
    ¬ ∀ (c : Char) (r : RE), lang (deriv c r) = deriv1 c (lang r) := by
  intro h
  have := h 'a' r₀
  rw [deriv_r₀] at this
  have hmem : (['a'] : List Char) ∈ deriv1 'a' (lang r₀) := this ▸ mem_lang_d₀
  have : (['a', 'a'] : List Char) ∈ lang r₀ := hmem
  rw [mem_lang_r₀] at this
  simp at this

theorem lang_deriv_of_homsStable (c : Char) (r : RE) (h : HomsStable r) :
    lang (deriv c r) = deriv1 c (lang r) :=
  lang_deriv_of_stable c r h

/-! #### `deriv_correct` -/

/-
theorem deriv_correct (c : Char) (r : RE) (w : List Char) :
    w ∈ lang (deriv c r) ↔ (c :: w) ∈ lang r := by
  sorry
-/
-- REFUTED as stated; corrected form: `deriv_correct_of_homsStable`.

theorem not_deriv_correct :
    ¬ ∀ (c : Char) (r : RE) (w : List Char),
      w ∈ lang (deriv c r) ↔ (c :: w) ∈ lang r := by
  intro h
  have hmem := (h 'a' r₀ ['a']).mp (by rw [deriv_r₀]; exact mem_lang_d₀)
  rw [mem_lang_r₀] at hmem
  simp at hmem

theorem deriv_correct_of_homsStable (c : Char) (r : RE) (w : List Char)
    (h : HomsStable r) : w ∈ lang (deriv c r) ↔ (c :: w) ∈ lang r := by
  rw [lang_deriv_of_stable c r h]
  exact Iff.rfl

/-! #### `matchRE_correct` -/

/-
theorem matchRE_correct (r : RE) (s : List Char) :
    matchRE r s = true ↔ s ∈ lang r := by
  sorry
-/
-- REFUTED as stated; corrected form: `matchRE_correct_of_homsStable`.

theorem matchRE_r₀ : matchRE r₀ ['a', 'a'] = true := by
  show nullable (deriv 'a' (deriv 'a' r₀)) = true
  rw [deriv_r₀]
  show nullable (invHom_ [('a', ([] : List Char))]
    (derivW (applyHom [('a', ([] : List Char))] 'a') RE.eps)) = true
  rw [show applyHom [('a', ([] : List Char))] 'a' = [] from rfl,
    show Redgrep.derivW ([] : List Char) RE.eps = RE.eps from by rw [Redgrep.derivW]]
  rw [invHom_eq_ite,
    show homNorm [('a', ([] : List Char))] = [('a', ([] : List Char))] from by simp [homNorm]]
  simp [nullable]

theorem not_matchRE_correct :
    ¬ ∀ (r : RE) (s : List Char), matchRE r s = true ↔ s ∈ lang r := by
  intro h
  have hmem := (h r₀ ['a', 'a']).mp matchRE_r₀
  rw [mem_lang_r₀] at hmem
  simp at hmem

theorem matchRE_correct_of_homsStable (r : RE) (s : List Char) (h : HomsStable r) :
    matchRE r s = true ↔ s ∈ lang r :=
  matchRE_of_stable r s h

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

/-
theorem lang_invHom_ (h : List (Char × List Char)) (r : RE) :
    lang (invHom_ h r) = _root_.invHom (applyHom h) (lang r) := by
  sorry
-/
-- REFUTED as stated; corrected form: `lang_smart_invHom_of_stable` (and
-- `lang_invHom_of_homWF`, the same statement for association lists with
-- pairwise distinct keys).

theorem not_lang_invHom_ :
    ¬ ∀ (h : List (Char × List Char)) (r : RE),
      lang (invHom_ h r) = _root_.invHom (applyHom h) (lang r) := by
  intro hyp
  have h1 : (['a'] : List Char) ∈ _root_.invHom (applyHom h₀) (lang (RE.sym (.pos {'a'}))) := by
    show (['a'] : List Char).flatMap (applyHom h₀) ∈ lang (RE.sym (.pos {'a'}))
    rw [show (['a'] : List Char).flatMap (applyHom h₀) = ['a'] from by simp [applyHom_h₀]]
    exact ⟨'a', by simp [inCls], rfl⟩
  rw [← hyp h₀ (RE.sym (.pos {'a'})), invHom_smart_h₀ (by simp)] at h1
  have : (['a'] : List Char).flatMap (applyHom [('a', ([] : List Char))]) ∈
      lang (RE.sym (.pos {'a'})) := h1
  rw [show (['a'] : List Char).flatMap (applyHom [('a', ([] : List Char))]) = [] from rfl] at this
  obtain ⟨c, -, hc⟩ := this
  simp at hc

/-- The corrected `lang_invHom_`, under the stability side condition. -/
theorem lang_smart_invHom_of_stable {h : List (Char × List Char)} (hst : HomStable h) (r : RE) :
    lang (invHom_ h r) = _root_.invHom (applyHom h) (lang r) :=
  lang_invHom_of_stable hst r

/-- The corrected `lang_invHom_` for the intended usage: association lists
with pairwise distinct keys. -/
theorem lang_invHom_of_homWF {h : List (Char × List Char)} (hwf : HomWF h) (r : RE) :
    lang (invHom_ h r) = _root_.invHom (applyHom h) (lang r) :=
  lang_invHom_of_stable hwf.homStable r

/-! #### `canon_correct` -/

/-
/-- `canon` is language-preserving: canonicalisation is free, semantically. -/
theorem canon_correct (r : RE) : lang (canon r) = lang r := by
  sorry
-/
-- REFUTED as stated; corrected form: `canon_correct_of_homsStable`.

theorem canon_r₀ : canon r₀ = .invHom [('a', ([] : List Char))] (.sym (.pos {'a'})) := by
  show invHom_ h₀ (canon (RE.sym (.pos {'a'}))) = _
  rw [show canon (RE.sym (.pos {'a'})) = RE.sym (.pos {'a'}) from by
    show sym (Cls.pos {'a'}) = _
    rw [Smart.sym_def]
    simp [Cls.isEmpty, Cls.norm, Cls.isFull, charCount]]
  exact invHom_smart_h₀ (by simp)

theorem not_canon_correct : ¬ ∀ (r : RE), lang (canon r) = lang r := by
  intro h
  have h1 : (['a'] : List Char) ∈ lang r₀ := (mem_lang_r₀ ['a']).mpr rfl
  rw [← h r₀, canon_r₀] at h1
  have : (['a'] : List Char).flatMap (applyHom [('a', ([] : List Char))]) ∈
      lang (RE.sym (.pos {'a'})) := h1
  rw [show (['a'] : List Char).flatMap (applyHom [('a', ([] : List Char))]) = [] from rfl] at this
  obtain ⟨c, -, hc⟩ := this
  simp at hc

/-- The corrected `canon_correct`: canonicalisation is semantically free for
every term whose `invHom` nodes survive `homNorm`. -/
theorem canon_correct_of_homsStable (r : RE) (h : HomsStable r) : lang (canon r) = lang r := by
  induction r with
  | sym cl => exact Smart.lang_smart_sym cl
  | alt a b iha ihb =>
    show lang (alt2 (canon a) (canon b)) = _
    rw [Smart.lang_alt2, iha h.1, ihb h.2]
    rfl
  | cut a b iha ihb =>
    show lang (cut2 (canon a) (canon b)) = _
    rw [Smart.lang_cut2, iha h.1, ihb h.2]
    rfl
  | seq a b iha ihb =>
    show lang (seq2 (canon a) (canon b)) = _
    rw [Smart.lang_seq2, iha h.1, ihb h.2]
    rfl
  | rep a ih =>
    show lang (rep_ (canon a)) = _
    rw [Smart.lang_rep_, ih h]
    rfl
  | not a ih =>
    show lang (not_ (canon a)) = _
    rw [Smart.lang_not_, ih h]
    rfl
  | invHom hh a ih =>
    show lang (invHom_ hh (canon a)) = _
    rw [lang_invHom_of_stable h.1, ih h.2]
    rfl
  | eps => rfl
  | nil => rfl

/-- `canon` lands in canonical form: the smart constructors are closed under
each other, i.e. normalisation is idempotent. -/
theorem canon_canonical (r : RE) : Canonical (canon r) := canon_idem r

end Redgrep

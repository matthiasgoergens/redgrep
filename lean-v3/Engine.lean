import SmartLang

/-!
# The engine contract, and the hom well-formedness side condition

`Core.lean`'s smart constructor `invHom_` replaces its association list `h` by
the normal form `homNorm h` (identity entries dropped, then sorted and
deduplicated).  `applyHom` resolves a key by *first hit wins*, so this
normalisation is **not** meaning-preserving for every `h`: dropping an identity
entry can expose a later entry with the same key.  The concrete failure is

```
h = [('a', ['a']), ('a', ['b'])] ,  applyHom h 'a' = ['a'] ,
homNorm h = [('a', ['b'])]       ,  applyHom (homNorm h) 'a' = ['b'] .
```

Everything in this file is therefore stated relative to the side condition

* `HomStable h` — `applyHom (homNorm h) = applyHom h`, i.e. normalising the
  association list does not change the homomorphism it denotes, and
* `HomsStable r` — every `invHom` node of `r` carries a `HomStable` list.

Both are automatic for the association lists the engine itself produces
(`homNorm` is idempotent), and `HomStable` holds in particular whenever the
keys of `h` are pairwise distinct (`HomWF.homStable`), which is the intended
usage recorded in `Core.lean`.  `Correctness.lean` records the counterexamples
that refute the unguarded statements.
-/

open Language Computability

namespace Redgrep

/-! ### Nullability -/

theorem nullable_iff (r : RE) : nullable r = true ↔ ([] : List Char) ∈ lang r := by
  induction r with
  | sym cl => simp [nullable]
  | alt a b iha ihb => simp [nullable, iha, ihb]
  | cut a b iha ihb => simp [nullable, iha, ihb]
  | seq a b iha ihb =>
    simp only [nullable, Bool.and_eq_true, iha, ihb, Smart.mem_lang_seq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨[], h1, [], h2, rfl⟩
    · rintro ⟨x, hx, y, hy, hxy⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hxy
      exact ⟨hx, hy⟩
  | rep a _ =>
    simp only [nullable, Smart.lang_rep, true_iff]
    exact Language.nil_mem_kstar _
  | not a iha => simp [nullable, ← iha]
  | invHom h a iha => simpa [nullable] using iha
  | eps => simp [nullable]
  | nil => simp [nullable]

/-! ### Hom stability -/

/-- The side condition making `invHom_` meaning-preserving: normalising the
association list does not change the homomorphism it denotes. -/
def HomStable (h : List (Char × List Char)) : Prop := applyHom (homNorm h) = applyHom h

/-- The engine only ever builds normalised association lists, and those are
always stable. -/
theorem homNorm_homStable (h : List (Char × List Char)) : HomStable (homNorm h) := by
  unfold HomStable
  rw [homNorm_idem]

/-- Well-formedness of an association list: pairwise distinct keys.  This is
the intended usage recorded in `Core.lean`, and it implies `HomStable`. -/
def HomWF (h : List (Char × List Char)) : Prop := (h.map Prod.fst).Nodup

theorem applyHom_eq_of_mem {l : List (Char × List Char)} (hnd : HomWF l) {c : Char}
    {img : List Char} (hp : (c, img) ∈ l) : applyHom l c = img := by
  induction l with
  | nil => simp at hp
  | cons p t ih =>
    unfold applyHom
    by_cases hpc : p.1 = c
    · rw [List.find?_cons_of_pos (by simp [hpc])]
      rcases List.mem_cons.mp hp with rfl | hp'
      · rfl
      · exfalso
        have : p.1 ∈ t.map Prod.fst := by rw [hpc]; exact List.mem_map.mpr ⟨_, hp', rfl⟩
        exact (List.nodup_cons.mp hnd).1 this
    · rw [List.find?_cons_of_neg (by simpa using hpc)]
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact absurd rfl hpc
      · exact ih (List.nodup_cons.mp hnd).2 hp'

theorem applyHom_eq_self {l : List (Char × List Char)} {c : Char}
    (h : ∀ p ∈ l, p.1 ≠ c) : applyHom l c = [c] := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    unfold applyHom
    rw [List.find?_cons_of_neg (by simpa using h p (by simp))]
    exact ih fun q hq => h q (by simp [hq])

theorem HomWF.homNorm {h : List (Char × List Char)} (hwf : HomWF h) :
    HomWF (Redgrep.homNorm h) := by
  refine List.Nodup.map_on ?_ (homNorm_nodup h)
  intro x hx y hy hxy
  exact List.inj_on_of_nodup_map hwf (mem_homNorm.mp hx).1 (mem_homNorm.mp hy).1 hxy

/-- Distinct keys make the association list stable under `homNorm`. -/
theorem HomWF.homStable {h : List (Char × List Char)} (hwf : HomWF h) : HomStable h := by
  funext c
  by_cases hex : ∃ img, (c, img) ∈ h ∧ img ≠ [c]
  · obtain ⟨img, hmem, hne⟩ := hex
    rw [applyHom_eq_of_mem hwf.homNorm (mem_homNorm.mpr ⟨hmem, hne⟩),
      applyHom_eq_of_mem hwf hmem]
  · push_neg at hex
    have h1 : applyHom (Redgrep.homNorm h) c = [c] := by
      refine applyHom_eq_self fun p hp hpc => ?_
      obtain ⟨hmem, hne⟩ := mem_homNorm.mp hp
      subst hpc
      exact hne (hex p.2 (by simpa using hmem))
    rw [h1]
    by_cases hmem : ∃ img, (c, img) ∈ h
    · obtain ⟨img, hi⟩ := hmem
      rw [applyHom_eq_of_mem hwf hi, hex img hi]
    · push_neg at hmem
      refine (applyHom_eq_self fun p hp hpc => ?_).symm
      exact hmem p.2 (by rw [← hpc]; simpa using hp)

theorem flatMap_singleton_self (w : List Char) : w.flatMap (fun c => [c]) = w := by
  induction w with
  | nil => rfl
  | cons c t ih => simp [List.flatMap_cons, ih]

/-- Language contract of the smart inverse homomorphism, under the stability
side condition. -/
theorem lang_invHom_of_stable {h : List (Char × List Char)} (hst : HomStable h) (r : RE) :
    lang (invHom_ h r) = _root_.invHom (applyHom h) (lang r) := by
  rw [invHom_eq_ite]
  split
  · rename_i hr
    subst hr
    ext w
    show w ∈ lang RE.nil ↔ (w.flatMap (applyHom h)) ∈ lang RE.nil
    exact iff_of_false Smart.mem_lang_nil.mp Smart.mem_lang_nil.mp
  · split
    · rename_i hemp
      ext w
      show w ∈ lang r ↔ (w.flatMap (applyHom h)) ∈ lang r
      rw [← hst, hemp]
      rw [show applyHom [] = fun c => [c] from rfl, flatMap_singleton_self]
    · show _root_.invHom (applyHom (homNorm h)) (lang r) = _root_.invHom (applyHom h) (lang r)
      rw [hst]

/-! ### Hereditary hom stability -/

/-- Every `invHom` node of the term carries a stable association list. -/
def HomsStable : RE → Prop
  | .sym _ => True
  | .alt a b => HomsStable a ∧ HomsStable b
  | .cut a b => HomsStable a ∧ HomsStable b
  | .seq a b => HomsStable a ∧ HomsStable b
  | .rep a => HomsStable a
  | .not a => HomsStable a
  | .invHom h a => HomStable h ∧ HomsStable a
  | .eps => True
  | .nil => True

@[simp] theorem homsStable_sym (cl : Cls) : HomsStable (.sym cl) := trivial
@[simp] theorem homsStable_eps : HomsStable .eps := trivial
@[simp] theorem homsStable_nil : HomsStable .nil := trivial
@[simp] theorem homsStable_top : HomsStable top := trivial

theorem homsStable_smart_sym (cl : Cls) : HomsStable (sym cl) := by
  rw [Smart.sym_def]; split <;> trivial

theorem homsStable_altToList {r : RE} (h : HomsStable r) : ∀ x ∈ altToList r, HomsStable x := by
  induction r with
  | alt a b iha ihb =>
    intro x hx
    rw [Smart.altToList_alt, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha h.1 x hx
    · exact ihb h.2 x hx
  | nil => intro x hx; simp at hx
  | sym cl => intro x hx; rw [Smart.altToList_sym, List.mem_singleton] at hx; subst hx; exact h
  | cut a b _ _ =>
    intro x hx; rw [Smart.altToList_cut, List.mem_singleton] at hx; subst hx; exact h
  | seq a b _ _ =>
    intro x hx; rw [Smart.altToList_seq, List.mem_singleton] at hx; subst hx; exact h
  | rep a _ => intro x hx; rw [Smart.altToList_rep, List.mem_singleton] at hx; subst hx; exact h
  | not a _ => intro x hx; rw [Smart.altToList_not, List.mem_singleton] at hx; subst hx; exact h
  | invHom hh a _ =>
    intro x hx; rw [Smart.altToList_invHom, List.mem_singleton] at hx; subst hx; exact h
  | eps => intro x hx; rw [Smart.altToList_eps, List.mem_singleton] at hx; subst hx; exact h

theorem homsStable_altOfList {l : List RE} (h : ∀ x ∈ l, HomsStable x) :
    HomsStable (altOfList l) := by
  induction l with
  | nil => trivial
  | cons r rs ih =>
    rw [Smart.altOfList_cons]
    split
    · exact h r (by simp)
    · exact ⟨h r (by simp), ih fun x hx => h x (by simp [hx])⟩

theorem homsStable_cutToList {r : RE} (h : HomsStable r) : ∀ x ∈ cutToList r, HomsStable x := by
  induction r with
  | cut a b iha ihb =>
    intro x hx
    rw [Smart.cutToList_cut, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha h.1 x hx
    · exact ihb h.2 x hx
  | not a _ =>
    intro x hx
    rw [Smart.cutToList_not] at hx
    split at hx
    · simp at hx
    · rw [List.mem_singleton] at hx; subst hx; exact h
  | nil => intro x hx; rw [Smart.cutToList_nil, List.mem_singleton] at hx; subst hx; exact h
  | sym cl => intro x hx; rw [Smart.cutToList_sym, List.mem_singleton] at hx; subst hx; exact h
  | alt a b _ _ =>
    intro x hx; rw [Smart.cutToList_alt, List.mem_singleton] at hx; subst hx; exact h
  | seq a b _ _ =>
    intro x hx; rw [Smart.cutToList_seq, List.mem_singleton] at hx; subst hx; exact h
  | rep a _ => intro x hx; rw [Smart.cutToList_rep, List.mem_singleton] at hx; subst hx; exact h
  | invHom hh a _ =>
    intro x hx; rw [Smart.cutToList_invHom, List.mem_singleton] at hx; subst hx; exact h
  | eps => intro x hx; rw [Smart.cutToList_eps, List.mem_singleton] at hx; subst hx; exact h

theorem homsStable_cutOfList {l : List RE} (h : ∀ x ∈ l, HomsStable x) :
    HomsStable (cutOfList l) := by
  induction l with
  | nil => trivial
  | cons r rs ih =>
    rw [Smart.cutOfList_cons]
    split
    · exact h r (by simp)
    · exact ⟨h r (by simp), ih fun x hx => h x (by simp [hx])⟩

theorem homsStable_seqToList {r : RE} (h : HomsStable r) : ∀ x ∈ seqToList r, HomsStable x := by
  induction r with
  | seq a b iha ihb =>
    intro x hx
    rw [Smart.seqToList_seq, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha h.1 x hx
    · exact ihb h.2 x hx
  | eps => intro x hx; simp at hx
  | nil => intro x hx; rw [Smart.seqToList_nil, List.mem_singleton] at hx; subst hx; exact h
  | sym cl => intro x hx; rw [Smart.seqToList_sym, List.mem_singleton] at hx; subst hx; exact h
  | alt a b _ _ =>
    intro x hx; rw [Smart.seqToList_alt, List.mem_singleton] at hx; subst hx; exact h
  | cut a b _ _ =>
    intro x hx; rw [Smart.seqToList_cut, List.mem_singleton] at hx; subst hx; exact h
  | rep a _ => intro x hx; rw [Smart.seqToList_rep, List.mem_singleton] at hx; subst hx; exact h
  | not a _ => intro x hx; rw [Smart.seqToList_not, List.mem_singleton] at hx; subst hx; exact h
  | invHom hh a _ =>
    intro x hx; rw [Smart.seqToList_invHom, List.mem_singleton] at hx; subst hx; exact h

theorem homsStable_seqOfList {l : List RE} (h : ∀ x ∈ l, HomsStable x) :
    HomsStable (seqOfList l) := by
  induction l with
  | nil => trivial
  | cons r rs ih =>
    rw [Smart.seqOfList_cons]
    split
    · exact h r (by simp)
    · exact ⟨h r (by simp), ih fun x hx => h x (by simp [hx])⟩

theorem homsStable_altL {rs : List RE} (h : ∀ r ∈ rs, HomsStable r) : HomsStable (altL rs) := by
  rw [Smart.altL_eq]
  split
  · trivial
  · refine homsStable_altOfList fun x hx => ?_
    rw [mem_sortDedup, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨cl, rfl⟩ := Smart.altMerged_sym _ x hx
      exact homsStable_smart_sym cl
    · rw [List.mem_filter, List.mem_flatMap] at hx
      obtain ⟨⟨r, hr, hxr⟩, -⟩ := hx
      exact homsStable_altToList (h r hr) x hxr

theorem homsStable_cutL {rs : List RE} (h : ∀ r ∈ rs, HomsStable r) : HomsStable (cutL rs) := by
  rw [Smart.cutL_eq]
  split
  · trivial
  · rcases Smart.cutBody_eq_or ((rs.flatMap cutToList).filter isSym)
      ((rs.flatMap cutToList).filter (not ∘ isSym)) with hb | ⟨l, hl, hb⟩
    · rw [hb]; trivial
    · rw [hb]
      refine homsStable_cutOfList fun x hx => ?_
      rw [mem_sortDedup] at hx
      rcases hl x hx with hx' | ⟨cl, rfl⟩
      · rw [List.mem_filter, List.mem_flatMap] at hx'
        obtain ⟨⟨r, hr, hxr⟩, -⟩ := hx'
        exact homsStable_cutToList (h r hr) x hxr
      · exact homsStable_smart_sym cl

theorem homsStable_alt2 {a b : RE} (ha : HomsStable a) (hb : HomsStable b) :
    HomsStable (alt2 a b) := by
  refine homsStable_altL fun r hr => ?_
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ha
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact hb
    · simp at hr

theorem homsStable_cut2 {a b : RE} (ha : HomsStable a) (hb : HomsStable b) :
    HomsStable (cut2 a b) := by
  refine homsStable_cutL fun r hr => ?_
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ha
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact hb
    · simp at hr

theorem homsStable_seq2 {a b : RE} (ha : HomsStable a) (hb : HomsStable b) :
    HomsStable (seq2 a b) := by
  rw [Smart.seq2_eq]
  split
  · trivial
  · split
    · exact hb
    · split
      · exact ha
      · refine homsStable_seqOfList fun x hx => ?_
        rcases List.mem_append.mp hx with hx | hx
        · exact homsStable_seqToList ha x hx
        · exact homsStable_seqToList hb x hx

theorem homsStable_rep_ {a : RE} (ha : HomsStable a) : HomsStable (rep_ a) := by
  cases a with
  | nil => trivial
  | eps => trivial
  | rep s => exact ha
  | not s =>
    show HomsStable (if RE.not s = top then top else RE.rep (.not s))
    split
    · trivial
    · exact ha
  | _ => exact ha

theorem homsStable_not_ {a : RE} (ha : HomsStable a) : HomsStable (not_ a) := by
  cases a with
  | not s => exact ha
  | _ => exact ha

theorem homsStable_invHom_ (h : List (Char × List Char)) {a : RE} (ha : HomsStable a) :
    HomsStable (invHom_ h a) := by
  rw [invHom_eq_ite]
  split
  · trivial
  · split
    · exact ha
    · exact ⟨homNorm_homStable h, ha⟩

/-! ### Stability is preserved by the engine -/

theorem homsStable_derivW : ∀ (u : List Char) (r : RE), HomsStable r → HomsStable (derivW u r) := by
  intro u r
  induction u, r using derivW.induct with
  | case1 cls => intro _; rw [derivW]; exact homsStable_smart_sym cls
  | case2 cls c _ => intro _; rw [derivW]; split <;> trivial
  | case3 cls c _ => intro _; rw [derivW]; split <;> trivial
  | case4 u cls _ _ => intro _; rw [derivW] <;> trivial
  | case5 u a b iha ihb => intro h; rw [derivW]; exact homsStable_alt2 (iha h.1) (ihb h.2)
  | case6 u a b iha ihb => intro h; rw [derivW]; exact homsStable_cut2 (iha h.1) (ihb h.2)
  | case7 u a b iha _ ihdrop =>
    intro h
    rw [derivW]
    refine homsStable_alt2 (homsStable_seq2 (iha h.1) h.2) (homsStable_altL fun x hx => ?_)
    rw [List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    split
    · exact ihdrop i h.2
    · trivial
  | case8 u a _ ihdrop =>
    intro h
    rw [derivW]
    refine homsStable_altL fun x hx => ?_
    rcases List.mem_append.mp hx with hx | hx
    · split at hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact homsStable_rep_ h
      · simp at hx
    · rw [List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      split
      · exact homsStable_seq2 (ihdrop i h) (homsStable_rep_ h)
      · trivial
  | case9 u a ih => intro h; rw [derivW]; exact homsStable_not_ (ih h)
  | case10 u hh a ih =>
    intro h
    rw [derivW]
    refine homsStable_invHom_ hh ?_
    simpa using ih h.2
  | case11 => intro _; rw [derivW]; trivial
  | case12 u _ => intro _; rw [derivW] <;> trivial
  | case13 u => intro _; rw [derivW]; trivial

theorem homsStable_deriv (c : Char) (r : RE) (h : HomsStable r) : HomsStable (deriv c r) := by
  induction r with
  | sym cl => rw [deriv_sym]; split <;> trivial
  | alt a b iha ihb => exact homsStable_alt2 (iha h.1) (ihb h.2)
  | cut a b iha ihb => exact homsStable_cut2 (iha h.1) (ihb h.2)
  | seq a b iha ihb =>
    rw [deriv_seq]
    split
    · exact homsStable_alt2 (homsStable_seq2 (iha h.1) h.2) (ihb h.2)
    · exact homsStable_seq2 (iha h.1) h.2
  | rep a ih => exact homsStable_seq2 (ih h) (homsStable_rep_ h)
  | not a ih => exact homsStable_not_ (ih h)
  | invHom hh a _ => exact homsStable_invHom_ hh (homsStable_derivW _ a h.2)
  | eps => trivial
  | nil => trivial

/-! ### A decomposition lemma for the Kleene star -/

@[simp] theorem mem_derivW {u w : List Char} {L : Language Char} :
    w ∈ _root_.derivW u L ↔ u ++ w ∈ L := Iff.rfl

theorem nil_mem_derivW {u : List Char} {L : Language Char} :
    [] ∈ _root_.derivW u L ↔ u ∈ L := by
  show u ++ [] ∈ L ↔ u ∈ L
  rw [List.append_nil]

theorem kstar_head {L : Language Char} {x : List Char} (hx : x ∈ L∗) (hne : x ≠ []) :
    ∃ c t, c ≠ [] ∧ c ∈ L ∧ t ∈ L∗ ∧ x = c ++ t := by
  obtain ⟨S, rfl, hS⟩ := Language.mem_kstar_iff_exists_nonempty.mp hx
  cases S with
  | nil => simp at hne
  | cons c T =>
    obtain ⟨hc, hcne⟩ := hS c (by simp)
    exact ⟨c, T.flatten, hcne, hc,
      Language.join_mem_kstar (fun y hy => (hS y (by simp [hy])).1), by simp⟩

theorem append_mem_kstar {L : Language Char} {c t : List Char} (hc : c ∈ L) (ht : t ∈ L∗) :
    c ++ t ∈ L∗ :=
  Set.mem_of_mem_of_subset (Language.append_mem_mul hc ht) (mul_kstar_le_kstar (a := L))

theorem append_mem_kstar_left {L : Language Char} {c t : List Char} (hc : c ∈ L∗)
    (ht : t ∈ L∗) : c ++ t ∈ L∗ :=
  Set.mem_of_mem_of_subset (Language.append_mem_mul hc ht) (kstar_mul_kstar L).le

/-- If a nonempty prefix `u` is consumed inside `L∗`, then some *proper* prefix of `u` is a
whole number of iterations and the straddling chunk starts with the rest of `u`. -/
theorem kstar_append_decomp {L : Language Char} (n : ℕ) :
    ∀ (u : List Char), u.length ≤ n → u ≠ [] → ∀ w, u ++ w ∈ L∗ →
      ∃ i, i < u.length ∧ u.take i ∈ L∗ ∧
        ∃ z y, (u.drop i ++ z) ∈ L ∧ y ∈ L∗ ∧ w = z ++ y := by
  induction n with
  | zero =>
    intro u hlen hne
    exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)) hne
  | succ n ih =>
    intro u hlen hne w hw
    obtain ⟨c, t, hcne, hc, ht, heq⟩ := kstar_head hw (by simp [hne])
    rcases List.append_eq_append_iff.mp heq with ⟨a, hca, hwa⟩ | ⟨a, hua, hta⟩
    · refine ⟨0, List.length_pos_of_ne_nil hne, ?_, a, t, ?_, ht, hwa⟩
      · simpa using Language.nil_mem_kstar L
      · simpa using hca ▸ hc
    · by_cases ha : a = []
      · subst ha
        simp only [List.append_nil] at hua
        subst hua
        rw [List.nil_append] at hta
        subst hta
        exact ⟨0, List.length_pos_of_ne_nil hne, by simpa using Language.nil_mem_kstar L,
          [], t, by simpa using hc, ht, rfl⟩
      · subst hua
        have hlen' : a.length ≤ n := by
          simp only [List.length_append] at hlen
          have : 0 < c.length := List.length_pos_of_ne_nil hcne
          omega
        obtain ⟨i, hi, hti, z, y, hz, hy, hwzy⟩ := ih a hlen' ha w (hta ▸ ht)
        refine ⟨c.length + i, ?_, ?_, z, y, ?_, hy, hwzy⟩
        · simp only [List.length_append]; omega
        · rw [List.take_append]
          simp only [Nat.add_sub_cancel_left]
          rw [List.take_of_length_le (by omega)]
          exact append_mem_kstar hc hti
        · rw [List.drop_append]
          simp only [Nat.add_sub_cancel_left]
          rw [List.drop_eq_nil_of_le (by omega)]
          simpa using hz

/-! ### The word derivative -/

theorem lang_derivW_of_stable : ∀ (u : List Char) (r : RE), HomsStable r →
    lang (derivW u r) = _root_.derivW u (lang r) := by
  intro u r
  induction u, r using derivW.induct with
  | case1 cls =>
    intro _
    rw [derivW, Smart.lang_smart_sym]
    ext w
    exact Iff.rfl
  | case2 cls c hc =>
    intro _
    rw [derivW, if_pos hc]
    ext w
    show w ∈ lang RE.eps ↔ [c] ++ w ∈ lang (RE.sym cls)
    simp only [Smart.mem_lang_eps, Smart.mem_lang_sym]
    constructor
    · rintro rfl
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c', -, he⟩
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      exact he.2
  | case3 cls c hc =>
    intro _
    rw [derivW, if_neg hc]
    ext w
    show w ∈ lang RE.nil ↔ [c] ++ w ∈ lang (RE.sym cls)
    simp only [Smart.mem_lang_nil, Smart.mem_lang_sym, false_iff, not_exists]
    rintro c' ⟨hc', he⟩
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
    exact hc (by rw [he.1]; exact hc')
  | case4 u cls h1 h2 =>
    intro _
    rw [derivW]
    · ext w
      show w ∈ lang RE.nil ↔ u ++ w ∈ lang (RE.sym cls)
      simp only [Smart.mem_lang_nil, Smart.mem_lang_sym, false_iff, not_exists]
      rintro c' ⟨-, he⟩
      cases u with
      | nil => exact h1 rfl
      | cons d t =>
        simp only [List.cons_append, List.cons.injEq] at he
        have ht : t = [] := (List.append_eq_nil_iff.mp he.2).1
        exact h2 d (by rw [ht])
    · exact h1
    · exact h2
  | case5 u a b iha ihb =>
    intro h
    rw [derivW, Smart.lang_alt2, iha h.1, ihb h.2]
    rfl
  | case6 u a b iha ihb =>
    intro h
    rw [derivW, Smart.lang_cut2, iha h.1, ihb h.2]
    rfl
  | case7 u a b iha ihtake ihdrop =>
    intro h
    rw [derivW]
    ext w
    rw [mem_derivW, Smart.mem_lang_alt2, Smart.mem_lang_seq2, Smart.mem_lang_altL]
    show (_ ∨ _) ↔ u ++ w ∈ lang a * lang b
    constructor
    · rintro (⟨p, hp, q, hq, rfl⟩ | ⟨s, hs, hws⟩)
      · rw [iha h.1, mem_derivW] at hp
        rw [← List.append_assoc]
        exact Language.append_mem_mul hp hq
      · rw [List.mem_map] at hs
        obtain ⟨i, -, rfl⟩ := hs
        split at hws
        · rename_i hnull
          rw [nullable_iff, ihtake i h.1, nil_mem_derivW] at hnull
          rw [ihdrop i h.2, mem_derivW] at hws
          have heq : u ++ w = u.take i ++ (u.drop i ++ w) := by
            rw [← List.append_assoc, List.take_append_drop]
          rw [heq]
          exact Language.append_mem_mul hnull hws
        · exact absurd hws (by simp)
    · intro hw'
      obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw'
      rcases List.append_eq_append_iff.mp hxy with ⟨z, huz, hyz⟩ | ⟨z, hxz, hwz⟩
      · right
        have htake : u.take x.length = x := by
          rw [huz, List.take_append]; simp
        have hdrop : u.drop x.length = z := by
          rw [huz, List.drop_append]; simp
        have hnull : nullable (derivW (u.take x.length) a) = true := by
          rw [nullable_iff, ihtake x.length h.1, nil_mem_derivW, htake]
          exact hx
        refine ⟨_, List.mem_map.mpr ⟨x.length, ?_, rfl⟩, ?_⟩
        · rw [List.mem_range, huz]
          simp only [List.length_append]
          omega
        · rw [if_pos hnull, ihdrop x.length h.2, mem_derivW, hdrop, ← hyz]
          exact hy
      · left
        refine ⟨z, ?_, y, hy, hwz.symm⟩
        rw [iha h.1, mem_derivW, ← hxz]
        exact hx
  | case8 u a ihtake ihdrop =>
    intro h
    rw [derivW]
    ext w
    rw [mem_derivW, Smart.mem_lang_altL]
    show (∃ s ∈ _, w ∈ lang s) ↔ u ++ w ∈ (lang a)∗
    constructor
    · rintro ⟨s, hs, hws⟩
      rcases List.mem_append.mp hs with hs | hs
      · split at hs
        · rename_i hu
          rw [List.mem_singleton] at hs
          subst hs
          have hu' : u = [] := List.isEmpty_iff.mp hu
          subst hu'
          rw [Smart.mem_lang_rep_] at hws
          simpa using hws
        · simp at hs
      · rw [List.mem_map] at hs
        obtain ⟨i, -, rfl⟩ := hs
        split at hws
        · rename_i hnull
          rw [nullable_iff, ihtake i h, nil_mem_derivW] at hnull
          obtain ⟨p, hp, q, hq, rfl⟩ := Smart.mem_lang_seq2.mp hws
          rw [ihdrop i h, mem_derivW] at hp
          rw [Smart.mem_lang_rep_] at hq
          have heq : u ++ (p ++ q) = u.take i.1 ++ ((u.drop i.1 ++ p) ++ q) := by
            rw [List.append_assoc (u.drop i.1), ← List.append_assoc (u.take i.1),
              List.take_append_drop]
          rw [heq]
          exact append_mem_kstar_left hnull (append_mem_kstar hp hq)
        · exact absurd hws (by simp)
    · intro hw'
      by_cases hu : u = []
      · subst hu
        refine ⟨rep_ a, List.mem_append_left _ (by simp), ?_⟩
        rw [Smart.mem_lang_rep_]
        simpa using hw'
      · obtain ⟨i, hi, hti, z, y, hz, hy, rfl⟩ :=
          kstar_append_decomp u.length u le_rfl hu w hw'
        refine ⟨_, List.mem_append_right _ (List.mem_map.mpr
          ⟨⟨i, List.mem_range.mpr hi⟩, List.mem_attach _ _, rfl⟩), ?_⟩
        have hnull : nullable (derivW (u.take i) (RE.rep a)) = true := by
          rw [nullable_iff, ihtake ⟨i, List.mem_range.mpr hi⟩ h, nil_mem_derivW]
          exact hti
        rw [if_pos hnull]
        refine Smart.mem_lang_seq2.mpr ⟨z, ?_, y, Smart.mem_lang_rep_.mpr hy, rfl⟩
        rw [ihdrop ⟨i, List.mem_range.mpr hi⟩ h, mem_derivW]
        exact hz
  | case9 u a ih =>
    intro h
    rw [derivW, Smart.lang_not_, ih h]
    rfl
  | case10 u hh a ih =>
    intro h
    rw [derivW, lang_invHom_of_stable h.1]
    have hih : lang (derivW (u.flatMap (applyHom hh)) a)
        = _root_.derivW (u.flatMap (applyHom hh)) (lang a) := by
      simpa using ih h.2
    rw [hih]
    ext w
    show (u.flatMap (applyHom hh)) ++ (w.flatMap (applyHom hh)) ∈ lang a ↔
      ((u ++ w).flatMap (applyHom hh)) ∈ lang a
    rw [List.flatMap_append]
  | case11 =>
    intro _
    rw [derivW]
    ext w
    exact Iff.rfl
  | case12 u h1 =>
    intro _
    rw [derivW]
    · ext w
      show w ∈ lang RE.nil ↔ u ++ w ∈ lang RE.eps
      simp only [Smart.mem_lang_nil, Smart.mem_lang_eps, false_iff]
      intro he
      exact h1 (List.append_eq_nil_iff.mp he).1
    · exact h1
  | case13 u =>
    intro _
    rw [derivW]
    ext w
    show w ∈ lang RE.nil ↔ u ++ w ∈ lang RE.nil
    simp

theorem lang_deriv_of_stable (c : Char) (r : RE) (h : HomsStable r) :
    lang (deriv c r) = deriv1 c (lang r) := by
  induction r with
  | sym cl =>
    rw [deriv_sym]
    ext w
    by_cases hc : inCls c cl
    · simp only [hc, if_pos]
      show w ∈ lang RE.eps ↔ c :: w ∈ lang (RE.sym cl)
      simp only [Smart.mem_lang_eps, Smart.mem_lang_sym]
      constructor
      · rintro rfl; exact ⟨c, hc, rfl⟩
      · rintro ⟨d, _, hd⟩; simpa using (List.cons.injEq c w d []).mp hd |>.2
    · simp only [hc, if_neg, Bool.false_eq_true, not_false_iff]
      show w ∈ lang RE.nil ↔ c :: w ∈ lang (RE.sym cl)
      simp only [Smart.mem_lang_nil, Smart.mem_lang_sym, false_iff]
      rintro ⟨d, hd, he⟩
      obtain ⟨rfl, -⟩ := (List.cons.injEq c w d []).mp he
      exact hc hd
  | alt a b iha ihb =>
    rw [deriv_alt, Smart.lang_alt2, iha h.1, ihb h.2]
    rfl
  | cut a b iha ihb =>
    rw [deriv_cut, Smart.lang_cut2, iha h.1, ihb h.2]
    rfl
  | seq a b iha ihb =>
    show lang (if nullable a then alt2 (seq2 (deriv c a) b) (deriv c b)
      else seq2 (deriv c a) b) = deriv1 c (lang a * lang b)
    rw [deriv1_mul]
    by_cases hn : nullable a
    · rw [if_pos hn, Smart.lang_alt2, Smart.lang_seq2, iha h.1, ihb h.2,
        if_pos ((nullable_iff a).mp hn)]
    · rw [if_neg hn, Smart.lang_seq2, iha h.1,
        if_neg (fun hx => hn ((nullable_iff a).mpr hx))]
      simp
  | rep a iha =>
    show lang (seq2 (deriv c a) (rep_ a)) = deriv1 c ((lang a)∗)
    rw [Smart.lang_seq2, Smart.lang_rep_, iha h, deriv1_kstar]
  | not a iha =>
    show lang (not_ (deriv c a)) = deriv1 c ((lang a)ᶜ)
    rw [Smart.lang_not_, iha h, deriv1_compl]
  | invHom hh a _ =>
    show lang (invHom_ hh (derivW (applyHom hh c) a)) =
      deriv1 c (_root_.invHom (applyHom hh) (lang a))
    rw [lang_invHom_of_stable h.1, lang_derivW_of_stable _ _ h.2, deriv1_invHom]
  | eps =>
    show lang RE.nil = deriv1 c (1 : Language Char)
    ext w
    show w ∈ lang RE.nil ↔ c :: w ∈ (1 : Language Char)
    simp only [Smart.mem_lang_nil, false_iff, Language.mem_one]
    exact List.cons_ne_nil _ _
  | nil =>
    show lang RE.nil = deriv1 c (0 : Language Char)
    ext w
    show w ∈ lang RE.nil ↔ c :: w ∈ (0 : Language Char)
    simp only [Smart.mem_lang_nil, false_iff]
    exact Set.notMem_empty _

theorem matchRE_of_stable (r : RE) (s : List Char) (h : HomsStable r) :
    matchRE r s = true ↔ s ∈ lang r := by
  induction s generalizing r with
  | nil => exact nullable_iff r
  | cons c t ih =>
    show nullable (t.foldl (fun r c => deriv c r) (deriv c r)) = true ↔ _
    rw [show (nullable (t.foldl (fun r c => deriv c r) (deriv c r)) = true)
      = (matchRE (deriv c r) t = true) from rfl, ih (deriv c r) (homsStable_deriv c r h),
      lang_deriv_of_stable c r h]
    rfl

end Redgrep

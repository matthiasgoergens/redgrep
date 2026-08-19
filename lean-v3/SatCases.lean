import SatPool

/-!
# Saturated pools, constructor by constructor (the non-concatenation cases)

For every constructor except `seq` and `rep` this file builds a saturated
pool around the pools of the immediate subterms:

* `sym`, `eps`, `nil` — the base pool plus (at most) the raw leaf itself;
* `alt`, `cut` — the union of the two subpools, closed under smart unions
  (resp. intersections), which is what `sat_altPool`/`sat_cutPool` provide;
* `not` — the subpool together with its complements, `not_` peeling at most
  one layer;
* `invHom` — the subpool with a homomorphism wrapper, the reachable
  homomorphisms being sub-permutations of the original one (`invHom_` sorts,
  filters and deduplicates its association list, so it can only shrink).

`seq` and `rep` are handled in `ChainPool.lean`.
-/

namespace Redgrep

open Smart

/-! ### A pool with extra non-concatenation atoms -/

/-- Adjoining a finite set `E` of non-concatenation states to a saturated
set keeps it saturated, provided the derivatives of `E` stay inside. -/
theorem sat_extend {U : Finset Char} {Pa E : Set RE} (hPa : Sat U Pa)
    (hEfin : E.Finite)
    (hEalt : ∀ x ∈ E, ∀ y ∈ altToList x, y ∈ Pa ∪ E)
    (hEcut : ∀ x ∈ E, ∀ y ∈ cutToList x, y ∈ Pa ∪ E)
    (hEsym : ∀ cl, (RE.sym cl) ∈ E → ClsOK U cl)
    (hEnot : ∀ y : RE, (RE.not y) ∈ E → y ∈ Pa ∪ E)
    (hEns : ∀ x ∈ E, NotSeq x)
    (hEd : ∀ x ∈ E, ∀ c, deriv c x ∈ Pa ∪ E)
    (hEw : ∀ x ∈ E, ∀ w, derivW w x ∈ Pa ∪ E) :
    Sat U (Pa ∪ E) := by
  have hsub : Pa ⊆ Pa ∪ E := Set.subset_union_left
  have hd : ∀ x ∈ Pa ∪ E, ∀ c, deriv c x ∈ Pa ∪ E := by
    rintro x (hx | hx) c
    · exact hsub (hPa.deriv_mem x hx c)
    · exact hEd x hx c
  have hw : ∀ x ∈ Pa ∪ E, ∀ w, derivW w x ∈ Pa ∪ E := by
    rintro x (hx | hx) w
    · exact hsub (hPa.derivW_mem x hx w)
    · exact hEw x hx w
  have hsuf : ∀ x ∈ Pa ∪ E, ∀ i, seqOfList ((seqToList x).drop i) ∈ Pa ∪ E := by
    rintro x (hx | hx) i
    · exact hsub (hPa.suffix_mem x hx i)
    · exact suffix_mem_of_notSeq (hsub hPa.eps_mem) (Or.inr hx) (hEns x hx) i
  have hsuf0 : ∀ z ∈ Pa ∪ E, seqOfList (seqToList z) ∈ Pa ∪ E := by
    intro z hz
    have := hsuf z hz 0
    rwa [List.drop_zero] at this
  refine ⟨⟨hPa.finite.union hEfin, hsub hPa.eps_mem, hsub hPa.nil_mem, hsub hPa.top_mem,
    fun cl h => hsub (hPa.sym_mem cl h), ?_, ?_, ?_⟩, ?_, hd, hw, hsuf, ?_, ?_⟩
  · rintro cl (hx | hx)
    · exact hPa.sym_cls cl hx
    · exact hEsym cl hx
  · rintro x (hx | hx) y hy
    · exact hsub (hPa.alt_atom x hx y hy)
    · exact hEalt x hx y hy
  · rintro x (hx | hx) y hy
    · exact hsub (hPa.cut_atom x hx y hy)
    · exact hEcut x hx y hy
  · rintro y (hx | hx)
    · exact hsub (hPa.not_body y hx)
    · exact hEnot y hx
  · rintro x (hx | hx)
    · exact fun h rest hrest c => hsub (hPa.headD_mem x hx h rest hrest c)
    · exact headD_mem_of_notSeq (Or.inr hx) (hEns x hx) hd hsuf0
  · rintro x (hx | hx)
    · exact fun h rest hrest w => hsub (hPa.headW_mem x hx h rest hrest w)
    · exact headW_mem_of_notSeq (Or.inr hx) (hEns x hx) hw hsuf0

/-! ### Leaves -/

theorem exists_sat_nilRE (U : Finset Char) : ∃ P, Sat U P ∧ (RE.nil) ∈ P :=
  ⟨symBase U, sat_symBase U, nil_mem_symBase U⟩

theorem exists_sat_eps (U : Finset Char) : ∃ P, Sat U P ∧ (RE.eps) ∈ P :=
  ⟨symBase U, sat_symBase U, eps_mem_symBase U⟩

theorem exists_sat_sym {U : Finset Char} {cl : Cls} (h : ClsOK U cl) :
    ∃ P, Sat U P ∧ (RE.sym cl) ∈ P := by
  refine ⟨symBase U ∪ {RE.sym cl}, sat_extend (sat_symBase U) (Set.finite_singleton _)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_, Or.inr rfl⟩
  · rintro x rfl y hy
    rw [altToList_sym, List.mem_singleton] at hy
    exact Or.inr hy
  · rintro x rfl y hy
    rw [cutToList_sym, List.mem_singleton] at hy
    exact Or.inr hy
  · rintro cl' hcl'
    rw [Set.mem_singleton_iff, RE.sym.injEq] at hcl'
    exact hcl' ▸ h
  · rintro y hy
    exact absurd hy (by simp)
  · rintro x rfl
    trivial
  · rintro x rfl c
    rw [deriv_sym]
    split
    · exact Or.inl (eps_mem_symBase U)
    · exact Or.inl (nil_mem_symBase U)
  · rintro x rfl w
    match w with
    | [] => rw [derivW_sym_nil]; exact Or.inl (sym_mem_symBase h)
    | [c] =>
      rw [derivW_sym_one]
      split
      · exact Or.inl (eps_mem_symBase U)
      · exact Or.inl (nil_mem_symBase U)
    | c :: d :: w => rw [derivW_sym_two]; exact Or.inl (nil_mem_symBase U)

/-! ### Complement -/

theorem not_cases (z : RE) : not_ z = .not z ∨ ∃ w, z = .not w ∧ not_ z = w := by
  cases z with
  | not w => exact Or.inr ⟨w, rfl, rfl⟩
  | _ => exact Or.inl rfl

theorem exists_sat_not {U : Finset Char} {Pa : Set RE} {a : RE}
    (hPa : Sat U Pa) (ha : a ∈ Pa) : ∃ P, Sat U P ∧ (RE.not a) ∈ P := by
  have hmem : ∀ x ∈ Pa, (RE.not x) ∈ (fun z => RE.not z) '' Pa := fun x hx => ⟨x, hx, rfl⟩
  refine ⟨Pa ∪ (fun z => RE.not z) '' Pa,
    sat_extend hPa (hPa.finite.image _) ?_ ?_ ?_ ?_ ?_ ?_ ?_, Or.inr (hmem a ha)⟩
  · rintro x ⟨z, hz, rfl⟩ y hy
    rw [altToList_not, List.mem_singleton] at hy
    exact Or.inr (hy ▸ hmem z hz)
  · rintro x ⟨z, hz, rfl⟩ y hy
    rw [cutToList_not] at hy
    split at hy
    · simp at hy
    · rw [List.mem_singleton] at hy
      exact Or.inr (hy ▸ hmem z hz)
  · rintro cl ⟨z, hz, hzz⟩
    exact absurd hzz (by simp)
  · rintro y ⟨z, hz, hzz⟩
    rw [RE.not.injEq] at hzz
    exact Or.inl (hzz ▸ hz)
  · rintro x ⟨z, hz, rfl⟩
    trivial
  · rintro x ⟨z, hz, rfl⟩ c
    rw [deriv_not]
    rcases not_cases (deriv c z) with h | ⟨w, hw, h⟩
    · rw [h]
      exact Or.inr (hmem _ (hPa.deriv_mem z hz c))
    · rw [h]
      exact Or.inl (hPa.not_body w (hw ▸ hPa.deriv_mem z hz c))
  · rintro x ⟨z, hz, rfl⟩ w
    rw [derivW_not]
    rcases not_cases (derivW w z) with h | ⟨v, hv, h⟩
    · rw [h]
      exact Or.inr (hmem _ (hPa.derivW_mem z hz w))
    · rw [h]
      exact Or.inl (hPa.not_body v (hv ▸ hPa.derivW_mem z hz w))

/-! ### Inverse homomorphism -/

theorem subperm_finite (h : List (Char × List Char)) :
    {g : List (Char × List Char) | g.Subperm h}.Finite := by
  classical
  refine Set.Finite.subset (h.sublists.flatMap List.permutations).finite_toSet ?_
  rintro g ⟨l, hl, hsub⟩
  refine List.mem_flatMap.mpr ⟨l, List.mem_sublists.mpr hsub, ?_⟩
  exact List.mem_permutations.mpr hl.symm

/-- `invHom_` either collapses, or keeps the body under a *sub-permutation*
of the given homomorphism (it filters, sorts and deduplicates it). -/
theorem invHom_cases (g : List (Char × List Char)) (x : RE) :
    invHom_ g x = .nil ∨ invHom_ g x = x ∨
      ∃ g', g'.Subperm g ∧ invHom_ g x = .invHom g' x := by
  unfold invHom_
  split
  · exact Or.inl rfl
  · simp only []
    split
    · exact Or.inr (Or.inl rfl)
    · refine Or.inr (Or.inr ⟨_, ?_, rfl⟩)
      exact ((List.dedup_sublist _).subperm.trans
        (List.mergeSort_perm _ _).subperm).trans List.filter_sublist.subperm

theorem exists_sat_invHom {U : Finset Char} {Pa : Set RE} {hm : List (Char × List Char)} {a : RE}
    (hPa : Sat U Pa) (ha : a ∈ Pa) : ∃ P, Sat U P ∧ (RE.invHom hm a) ∈ P := by
  classical
  set E : Set RE := {y | ∃ g, g.Subperm hm ∧ ∃ x ∈ Pa, y = .invHom g x} with hEdef
  have hEmem : ∀ (g : List (Char × List Char)), g.Subperm hm → ∀ x ∈ Pa, (RE.invHom g x) ∈ E :=
    fun g hg x hx => ⟨g, hg, x, hx, rfl⟩
  have hEfin : E.Finite := by
    refine Set.Finite.subset
      (Set.Finite.image (fun p : List (Char × List Char) × RE => RE.invHom p.1 p.2)
        ((subperm_finite hm).prod hPa.finite)) ?_
    rintro y ⟨g, hg, x, hx, rfl⟩
    exact ⟨(g, x), ⟨hg, hx⟩, rfl⟩
  refine ⟨Pa ∪ E, sat_extend hPa hEfin ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    Or.inr (hEmem hm (List.Subperm.refl hm) a ha)⟩
  · rintro x ⟨g, hg, z, hz, rfl⟩ y hy
    rw [altToList_invHom, List.mem_singleton] at hy
    exact Or.inr (hy ▸ hEmem g hg z hz)
  · rintro x ⟨g, hg, z, hz, rfl⟩ y hy
    rw [cutToList_invHom, List.mem_singleton] at hy
    exact Or.inr (hy ▸ hEmem g hg z hz)
  · rintro cl ⟨g, hg, z, hz, hzz⟩
    exact absurd hzz (by simp)
  · rintro y ⟨g, hg, z, hz, hzz⟩
    exact absurd hzz (by simp)
  · rintro x ⟨g, hg, z, hz, rfl⟩
    trivial
  · rintro x ⟨g, hg, z, hz, rfl⟩ c
    rw [deriv_invHom]
    have hbody : derivW (applyHom g c) z ∈ Pa := hPa.derivW_mem z hz _
    rcases invHom_cases g (derivW (applyHom g c) z) with h | h | ⟨g', hg', h⟩
    · rw [h]; exact Or.inl hPa.nil_mem
    · rw [h]; exact Or.inl hbody
    · rw [h]; exact Or.inr (hEmem g' (hg'.trans hg) _ hbody)
  · rintro x ⟨g, hg, z, hz, rfl⟩ w
    rw [derivW_invHom]
    have hbody : derivW (w.flatMap (applyHom g)) z ∈ Pa := hPa.derivW_mem z hz _
    rcases invHom_cases g (derivW (w.flatMap (applyHom g)) z) with h | h | ⟨g', hg', h⟩
    · rw [h]; exact Or.inl hPa.nil_mem
    · rw [h]; exact Or.inl hbody
    · rw [h]; exact Or.inr (hEmem g' (hg'.trans hg) _ hbody)

/-! ### Union and intersection -/

theorem exists_sat_alt {U : Finset Char} {Pa Pb : Set RE} {a b : RE}
    (hPa : Sat U Pa) (hPb : Sat U Pb) (ha : a ∈ Pa) (hb : b ∈ Pb) :
    ∃ P, Sat U P ∧ (RE.alt a b) ∈ P := by
  classical
  set A : Set RE := Pa ∪ Pb ∪ {RE.alt a b} with hAdef
  have hmemA : ∀ x : RE, x ∈ A ↔ (x ∈ Pa ∨ x ∈ Pb ∨ x = .alt a b) := by
    intro x
    simp only [hAdef, Set.mem_union, Set.mem_singleton_iff]
    tauto
  have hPaA : Pa ⊆ A := fun x hx => (hmemA x).mpr (Or.inl hx)
  have hPbA : Pb ⊆ A := fun x hx => (hmemA x).mpr (Or.inr (Or.inl hx))
  have hrA : (RE.alt a b) ∈ A := (hmemA _).mpr (Or.inr (Or.inr rfl))
  have hAtom : AtomSet U A := by
    refine ⟨(hPa.finite.union hPb.finite).union (Set.finite_singleton _),
      hPaA hPa.eps_mem, hPaA hPa.nil_mem, hPaA hPa.top_mem,
      fun cl h => hPaA (hPa.sym_mem cl h), ?_, ?_, ?_⟩
    · intro cl hcl
      rcases (hmemA _).mp hcl with h | h | h
      · exact hPa.sym_cls cl h
      · exact hPb.sym_cls cl h
      · exact absurd h (by simp)
    · intro x hx y hy
      rcases (hmemA x).mp hx with h | h | rfl
      · exact hPaA (hPa.alt_atom x h y hy)
      · exact hPbA (hPb.alt_atom x h y hy)
      · rw [altToList_alt, List.mem_append] at hy
        rcases hy with hy | hy
        · exact hPaA (hPa.alt_atom a ha y hy)
        · exact hPbA (hPb.alt_atom b hb y hy)
    · intro x hx y hy
      rcases (hmemA x).mp hx with h | h | rfl
      · exact hPaA (hPa.cut_atom x h y hy)
      · exact hPbA (hPb.cut_atom x h y hy)
      · rw [cutToList_alt, List.mem_singleton] at hy
        exact hy ▸ hrA
  have hAP : A ⊆ AltPool A := Set.subset_union_left
  have hspan : ∀ x y : RE, x ∈ A → y ∈ A → alt2 x y ∈ AltPool A := by
    intro x y hx hy
    refine Or.inr ⟨[x, y], ?_, rfl⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hy
      · simp at hz
  have hsuf : ∀ x ∈ A, ∀ i, seqOfList ((seqToList x).drop i) ∈ AltPool A := by
    intro x hx i
    rcases (hmemA x).mp hx with h | h | rfl
    · exact hAP (hPaA (hPa.suffix_mem x h i))
    · exact hAP (hPbA (hPb.suffix_mem x h i))
    · exact suffix_mem_of_notSeq (hAP (hPaA hPa.eps_mem)) (hAP hrA) trivial i
  have hd : ∀ x ∈ A, ∀ c, deriv c x ∈ AltPool A := by
    intro x hx c
    rcases (hmemA x).mp hx with h | h | rfl
    · exact hAP (hPaA (hPa.deriv_mem x h c))
    · exact hAP (hPbA (hPb.deriv_mem x h c))
    · rw [deriv_alt]
      exact hspan _ _ (hPaA (hPa.deriv_mem a ha c)) (hPbA (hPb.deriv_mem b hb c))
  have hw : ∀ x ∈ A, ∀ w, derivW w x ∈ AltPool A := by
    intro x hx w
    rcases (hmemA x).mp hx with h | h | rfl
    · exact hAP (hPaA (hPa.derivW_mem x h w))
    · exact hAP (hPbA (hPb.derivW_mem x h w))
    · rw [derivW_alt]
      exact hspan _ _ (hPaA (hPa.derivW_mem a ha w)) (hPbA (hPb.derivW_mem b hb w))
  refine ⟨AltPool A, sat_altPool hAtom ?_ hd hw hsuf ?_ ?_, hAP hrA⟩
  · intro y hy
    rcases (hmemA _).mp hy with h | h | h
    · exact hAP (hPaA (hPa.not_body y h))
    · exact hAP (hPbA (hPb.not_body y h))
    · exact absurd h (by simp)
  · intro x hx
    rcases (hmemA x).mp hx with h | h | rfl
    · exact fun hh rest hrest c => hAP (hPaA (hPa.headD_mem x h hh rest hrest c))
    · exact fun hh rest hrest c => hAP (hPbA (hPb.headD_mem x h hh rest hrest c))
    · exact headD_mem_of_notSeq (hAP hrA) trivial (altPool_deriv hAtom hd)
        (altPool_suffix_zero hAtom hsuf)
  · intro x hx
    rcases (hmemA x).mp hx with h | h | rfl
    · exact fun hh rest hrest w => hAP (hPaA (hPa.headW_mem x h hh rest hrest w))
    · exact fun hh rest hrest w => hAP (hPbA (hPb.headW_mem x h hh rest hrest w))
    · exact headW_mem_of_notSeq (hAP hrA) trivial (altPool_derivW hAtom hw)
        (altPool_suffix_zero hAtom hsuf)

theorem exists_sat_cut {U : Finset Char} {Pa Pb : Set RE} {a b : RE}
    (hPa : Sat U Pa) (hPb : Sat U Pb) (ha : a ∈ Pa) (hb : b ∈ Pb) :
    ∃ P, Sat U P ∧ (RE.cut a b) ∈ P := by
  classical
  set A : Set RE := Pa ∪ Pb ∪ {RE.cut a b} with hAdef
  have hmemA : ∀ x : RE, x ∈ A ↔ (x ∈ Pa ∨ x ∈ Pb ∨ x = .cut a b) := by
    intro x
    simp only [hAdef, Set.mem_union, Set.mem_singleton_iff]
    tauto
  have hPaA : Pa ⊆ A := fun x hx => (hmemA x).mpr (Or.inl hx)
  have hPbA : Pb ⊆ A := fun x hx => (hmemA x).mpr (Or.inr (Or.inl hx))
  have hrA : (RE.cut a b) ∈ A := (hmemA _).mpr (Or.inr (Or.inr rfl))
  have hAtom : AtomSet U A := by
    refine ⟨(hPa.finite.union hPb.finite).union (Set.finite_singleton _),
      hPaA hPa.eps_mem, hPaA hPa.nil_mem, hPaA hPa.top_mem,
      fun cl h => hPaA (hPa.sym_mem cl h), ?_, ?_, ?_⟩
    · intro cl hcl
      rcases (hmemA _).mp hcl with h | h | h
      · exact hPa.sym_cls cl h
      · exact hPb.sym_cls cl h
      · exact absurd h (by simp)
    · intro x hx y hy
      rcases (hmemA x).mp hx with h | h | rfl
      · exact hPaA (hPa.alt_atom x h y hy)
      · exact hPbA (hPb.alt_atom x h y hy)
      · rw [altToList_cut, List.mem_singleton] at hy
        exact hy ▸ hrA
    · intro x hx y hy
      rcases (hmemA x).mp hx with h | h | rfl
      · exact hPaA (hPa.cut_atom x h y hy)
      · exact hPbA (hPb.cut_atom x h y hy)
      · rw [cutToList_cut, List.mem_append] at hy
        rcases hy with hy | hy
        · exact hPaA (hPa.cut_atom a ha y hy)
        · exact hPbA (hPb.cut_atom b hb y hy)
  have hAP : A ⊆ CutPool A := Set.subset_union_left
  have hspan : ∀ x y : RE, x ∈ A → y ∈ A → cut2 x y ∈ CutPool A := by
    intro x y hx hy
    refine Or.inr ⟨[x, y], ?_, rfl⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hy
      · simp at hz
  have hsuf : ∀ x ∈ A, ∀ i, seqOfList ((seqToList x).drop i) ∈ CutPool A := by
    intro x hx i
    rcases (hmemA x).mp hx with h | h | rfl
    · exact hAP (hPaA (hPa.suffix_mem x h i))
    · exact hAP (hPbA (hPb.suffix_mem x h i))
    · exact suffix_mem_of_notSeq (hAP (hPaA hPa.eps_mem)) (hAP hrA) trivial i
  have hd : ∀ x ∈ A, ∀ c, deriv c x ∈ CutPool A := by
    intro x hx c
    rcases (hmemA x).mp hx with h | h | rfl
    · exact hAP (hPaA (hPa.deriv_mem x h c))
    · exact hAP (hPbA (hPb.deriv_mem x h c))
    · rw [deriv_cut]
      exact hspan _ _ (hPaA (hPa.deriv_mem a ha c)) (hPbA (hPb.deriv_mem b hb c))
  have hw : ∀ x ∈ A, ∀ w, derivW w x ∈ CutPool A := by
    intro x hx w
    rcases (hmemA x).mp hx with h | h | rfl
    · exact hAP (hPaA (hPa.derivW_mem x h w))
    · exact hAP (hPbA (hPb.derivW_mem x h w))
    · rw [derivW_cut]
      exact hspan _ _ (hPaA (hPa.derivW_mem a ha w)) (hPbA (hPb.derivW_mem b hb w))
  refine ⟨CutPool A, sat_cutPool hAtom ?_ hd hw hsuf ?_ ?_, hAP hrA⟩
  · intro y hy
    rcases (hmemA _).mp hy with h | h | h
    · exact hAP (hPaA (hPa.not_body y h))
    · exact hAP (hPbA (hPb.not_body y h))
    · exact absurd h (by simp)
  · intro x hx
    rcases (hmemA x).mp hx with h | h | rfl
    · exact fun hh rest hrest c => hAP (hPaA (hPa.headD_mem x h hh rest hrest c))
    · exact fun hh rest hrest c => hAP (hPbA (hPb.headD_mem x h hh rest hrest c))
    · exact headD_mem_of_notSeq (hAP hrA) trivial (cutPool_deriv hAtom hd)
        (cutPool_suffix_zero hAtom hsuf)
  · intro x hx
    rcases (hmemA x).mp hx with h | h | rfl
    · exact fun hh rest hrest w => hAP (hPaA (hPa.headW_mem x h hh rest hrest w))
    · exact fun hh rest hrest w => hAP (hPbA (hPb.headW_mem x h hh rest hrest w))
    · exact headW_mem_of_notSeq (hAP hrA) trivial (cutPool_derivW hAtom hw)
        (cutPool_suffix_zero hAtom hsuf)

end Redgrep

import ClsAlg
import ACICut
import AltAlg

/-!
# The ACI algebra of the smart intersection

Dual to `AltAlg.lean`.  The asymmetries with the union case are that
`cutToList` drops `top` (the unit) rather than `nil`, that `nil` is absorbing,
and that the merged `sym` member can *collapse* the whole intersection: an
empty intersection of classes makes the term `nil`.

Because of that collapse the merged member is factored out as `cutMerged`
(the analogue of `altMerged`, but *without* the `nil` filtering) and
`cutBody_eq'` records the collapse as a single `if`.

As in the union case, the merged class of a canonical intersection is a fold
of `Cls.inter` over the member classes, so the laws rest on that fold being
independent of order and multiplicity (`ClsAlg.lean`).  Unlike `Cls.union`,
`Cls.inter` preserves *normality* of classes (`Cls.normal_inter`), which is
what replaces the `norm` congruence used on the union side.
-/

namespace Redgrep

open Smart

/-- The flattened member list of a list of intersection operands. -/
def cutFlat (rs : List RE) : List RE := rs.flatMap cutToList

@[simp] theorem cutFlat_nil : cutFlat [] = [] := rfl

@[simp] theorem cutFlat_cons (r : RE) (rs : List RE) :
    cutFlat (r :: rs) = cutToList r ++ cutFlat rs := rfl

theorem cutFlat_append (rs ss : List RE) :
    cutFlat (rs ++ ss) = cutFlat rs ++ cutFlat ss := List.flatMap_append

theorem mem_cutFlat {x : RE} {rs : List RE} :
    x ∈ cutFlat rs ↔ ∃ r ∈ rs, x ∈ cutToList r := List.mem_flatMap

/-- The merged `sym` member of an intersection, before the `nil` collapse. -/
def cutMerged (syms : List RE) : List RE :=
  match symClasses syms with
  | [] => []
  | c :: cs => [sym (cs.foldl Cls.inter c)]

theorem cutMerged_eq_nil {L : List RE} (hsc : symClasses L = []) : cutMerged L = [] := by
  simp only [cutMerged, hsc]

theorem cutMerged_eq_singleton {L : List RE} {c : Cls} {cs : List Cls}
    (hsc : symClasses L = c :: cs) : cutMerged L = [sym (cs.foldl Cls.inter c)] := by
  simp only [cutMerged, hsc]

theorem cutBody_eq' (syms rest : List RE) :
    cutBody syms rest =
      if RE.nil ∈ cutMerged syms then .nil
      else cutOfList (sortDedup (cutMerged syms ++ rest)) := by
  unfold cutBody cutMerged
  cases hsc : symClasses syms with
  | nil => simp
  | cons c cs =>
    simp only []
    cases hsx : sym (cs.foldl Cls.inter c) with
    | nil => simp
    | _ => simp [hsx]

theorem cutL_eq' (rs : List RE) :
    cutL rs =
      (if RE.nil ∈ cutFlat rs then .nil
       else cutBody ((cutFlat rs).filter isSym) ((cutFlat rs).filter (not ∘ isSym))) :=
  cutL_eq rs

/-! ### The merged class depends only on the set of `sym` members -/

theorem cutMerged_congr {A B : List RE} (h : ∀ cl : Cls, RE.sym cl ∈ A ↔ RE.sym cl ∈ B) :
    cutMerged A = cutMerged B := by
  have hcl : ∀ cl, cl ∈ symClasses A ↔ cl ∈ symClasses B := by
    intro cl; rw [mem_symClasses, mem_symClasses]; exact h cl
  cases hA : symClasses A with
  | nil =>
    cases hB : symClasses B with
    | nil => simp only [cutMerged, hA, hB]
    | cons d ds => exact absurd (hA ▸ (hcl d).mpr (by rw [hB]; simp)) (by simp)
  | cons c cs =>
    cases hB : symClasses B with
    | nil => exact absurd (hB ▸ (hcl c).mp (by rw [hA]; simp)) (by simp)
    | cons d ds =>
      have hfold : cs.foldl Cls.inter c = ds.foldl Cls.inter d :=
        Cls.foldl_inter_congr (by intro x; rw [← hA, ← hB]; exact hcl x)
      simp only [cutMerged, hA, hB, hfold]

theorem cutMerged_filter (L : List RE) : cutMerged (L.filter isSym) = cutMerged L :=
  cutMerged_congr (by intro cl; simp only [List.mem_filter, isSym, and_true])

/-! ### `cutL` depends only on the set of flattened members -/

theorem cutL_congr_mem {rs ss : List RE} (h : ∀ x, x ∈ cutFlat rs ↔ x ∈ cutFlat ss) :
    cutL rs = cutL ss := by
  rw [cutL_eq', cutL_eq']
  by_cases hnil : RE.nil ∈ cutFlat rs
  · rw [if_pos hnil, if_pos ((h _).mp hnil)]
  · rw [if_neg hnil, if_neg fun hc => hnil ((h _).mpr hc), cutBody_eq', cutBody_eq']
    have hm : cutMerged ((cutFlat rs).filter isSym) = cutMerged ((cutFlat ss).filter isSym) :=
      cutMerged_congr (by intro cl; simp only [List.mem_filter, isSym, h (RE.sym cl)])
    rw [hm]
    congr 2
    apply sortDedup_eq_of_mem_iff
    intro x
    simp only [List.mem_append, List.mem_filter, h x]

theorem cutL_mem_congr {A B : List RE} (h : ∀ y, y ∈ A ↔ y ∈ B) : cutL A = cutL B :=
  cutL_congr_mem (by
    intro x
    simp only [mem_cutFlat]
    exact ⟨fun ⟨r, hr, hx⟩ => ⟨r, (h r).mp hr, hx⟩, fun ⟨r, hr, hx⟩ => ⟨r, (h r).mpr hr, hx⟩⟩)

theorem cutL_cons_append (x : RE) (L T : List RE) :
    cutL (x :: (L ++ T)) = cutL (L ++ (x :: T)) :=
  cutL_mem_congr (by intro y; simp only [List.mem_cons, List.mem_append]; tauto)

theorem cutL_swap2 (x y : RE) (T : List RE) : cutL (x :: y :: T) = cutL (y :: x :: T) :=
  cutL_mem_congr (by intro z; simp only [List.mem_cons]; tauto)

/-- A `top` member of an intersection can be dropped. -/
theorem cutL_cons_top (rs : List RE) : cutL (top :: rs) = cutL rs :=
  cutL_congr_mem (by
    intro x
    rw [cutFlat_cons, show cutToList top = [] from by
      rw [show top = RE.not RE.nil from rfl, Smart.cutToList_not, if_pos rfl], List.nil_append])

theorem cutL_nil_eq : cutL ([] : List RE) = top := by
  rw [cutL_eq']
  simp [cutFlat, cutBody, symClasses, sortDedup, cutOfList]

/-! ### The shape of the rebuilt member list -/

theorem cutMerged_shape (L : List RE) :
    ∀ x ∈ cutMerged L, ∃ cl, x = sym cl := by
  intro x hx
  cases hsc : symClasses L with
  | nil => rw [cutMerged_eq_nil hsc] at hx; simp at hx
  | cons c cs =>
    rw [cutMerged_eq_singleton hsc, List.mem_singleton] at hx
    exact ⟨_, hx⟩

theorem cutL_body_shape (rs : List RE) :
    ∀ x ∈ sortDedup (cutMerged ((cutFlat rs).filter isSym) ++
        (cutFlat rs).filter (not ∘ isSym)), x ≠ top ∧ NotCut x := by
  intro x hx
  rw [mem_sortDedup, List.mem_append] at hx
  rcases hx with hx | hx
  · obtain ⟨cl, rfl⟩ := cutMerged_shape _ x hx
    exact ⟨sym_ne_top' cl, notCut_sym cl⟩
  · have hf := List.mem_of_mem_filter hx
    obtain ⟨r, -, hxr⟩ := mem_cutFlat.mp hf
    exact ⟨(mem_cutToList_shape x hxr).2, (mem_cutToList_shape x hxr).1⟩

theorem cutToList_cutL {rs : List RE} (hnil : RE.nil ∉ cutFlat rs)
    (hm : RE.nil ∉ cutMerged ((cutFlat rs).filter isSym)) :
    cutToList (cutL rs) = sortDedup (cutMerged ((cutFlat rs).filter isSym) ++
      (cutFlat rs).filter (not ∘ isSym)) := by
  rw [cutL_eq', if_neg hnil, cutBody_eq', if_neg hm]
  exact cutToList_cutOfList (cutL_body_shape rs)

theorem nil_not_mem_cutToList_cutL {rs : List RE} (hnil : RE.nil ∉ cutFlat rs)
    (hm : RE.nil ∉ cutMerged ((cutFlat rs).filter isSym)) :
    RE.nil ∉ cutToList (cutL rs) := by
  rw [cutToList_cutL hnil hm]
  intro hx
  rw [mem_sortDedup, List.mem_append] at hx
  rcases hx with hx | hx
  · exact hm hx
  · exact hnil (List.mem_of_mem_filter hx)

/-! ### Idempotence -/

theorem cutL_singleton_of_shape {z : RE} (htop : z ≠ top) (hnil : z ≠ .nil) (hnc : NotCut z)
    (hsym : ∀ cl, z = .sym cl → sym cl = .sym cl) : cutL [z] = z := by
  have hflat : cutFlat [z] = [z] := by
    rw [show cutFlat [z] = cutToList z from by simp [cutFlat], cutToList_eq_singleton htop hnc]
  have hsd : ∀ w : RE, sortDedup [w] = [w] := fun w => sortDedup_eq_self (by simp) (by simp)
  rw [cutL_eq', hflat, if_neg (by simp [Ne.symm hnil]), cutBody_eq']
  by_cases hs : isSym z
  · obtain ⟨cl, rfl⟩ := isSym_iff.mp hs
    have hcm : cutMerged (([RE.sym cl] : List RE).filter isSym) = [RE.sym cl] := by
      rw [show ([RE.sym cl] : List RE).filter isSym = [RE.sym cl] from rfl,
        cutMerged_eq_singleton (show symClasses [RE.sym cl] = [cl] from rfl)]
      rw [show ([] : List Cls).foldl Cls.inter cl = cl from rfl, hsym cl rfl]
    rw [hcm, if_neg (by simp),
      show ([RE.sym cl] : List RE).filter (not ∘ isSym) = [] from rfl, List.append_nil, hsd]
    rfl
  · have hcm : cutMerged (([z] : List RE).filter isSym) = [] := by
      rw [show ([z] : List RE).filter isSym = [] from by simp [List.filter, hs]]
      exact cutMerged_eq_nil rfl
    rw [hcm, if_neg (by simp), List.nil_append,
      show ([z] : List RE).filter (not ∘ isSym) = [z] from by simp [List.filter, hs], hsd]
    rfl

theorem cutL_singleton {z : RE} (h : IsCanon z) : cutL [z] = z := by
  by_cases htop : z = top
  · subst htop; rw [cutL_cons_top, cutL_nil_eq]
  by_cases hnil : z = .nil
  · subst hnil
    rw [cutL_eq', if_pos (by rw [show cutFlat [RE.nil] = [RE.nil] from rfl]; simp)]
  match z, h with
  | .cut a b, h =>
    have : cutL [RE.cut a b] = cutL [a, b] :=
      cutL_congr_mem (by intro x; simp [cutFlat, Smart.cutToList_cut])
    rw [this]
    exact cut2_eq_self h
  | .sym cl, h =>
    exact cutL_singleton_of_shape htop hnil trivial
      (fun cl' heq => by simp only [RE.sym.injEq] at heq; subst heq; exact h)
  | .alt a b, h => exact cutL_singleton_of_shape htop hnil trivial (by simp)
  | .seq a b, h => exact cutL_singleton_of_shape htop hnil trivial (by simp)
  | .rep a, h => exact cutL_singleton_of_shape htop hnil trivial (by simp)
  | .not a, h => exact cutL_singleton_of_shape htop hnil trivial (by simp)
  | .invHom hh a, h => exact cutL_singleton_of_shape htop hnil trivial (by simp)
  | .eps, h => exact cutL_singleton_of_shape htop hnil trivial (by simp)
  | .nil, h => exact absurd rfl hnil

/-! ### Associativity: splicing an intersection member -/

theorem cutL_cons_nil (rs : List RE) : cutL (RE.nil :: rs) = .nil := by
  rw [cutL_eq', if_pos (by rw [cutFlat_cons, show cutToList RE.nil = [RE.nil] from rfl]; simp)]

theorem normal_of_sym_eq {cl : Cls} (h : sym cl = .sym cl) : Cls.Normal cl := by
  rw [Smart.sym_def] at h
  split at h
  · exact absurd h (by simp)
  · exact (RE.sym.injEq _ _ ▸ h : cl.norm = cl)

/-- An empty merged class stays empty when further members are intersected in. -/
theorem cutMerged_nil_mono {A B : List RE} (h : ∀ cl : Cls, RE.sym cl ∈ A → RE.sym cl ∈ B)
    (hA : RE.nil ∈ cutMerged A) : RE.nil ∈ cutMerged B := by
  cases hsc : symClasses A with
  | nil => rw [cutMerged_eq_nil hsc] at hA; simp at hA
  | cons c cs =>
    rw [cutMerged_eq_singleton hsc, List.mem_singleton] at hA
    have hAempty : (cs.foldl Cls.inter c).isEmpty = true := by
      rw [Smart.sym_def] at hA
      split at hA
      · assumption
      · exact absurd hA.symm (by simp)
    have hcB : RE.sym c ∈ B := h c (mem_symClasses.mp (by rw [hsc]; simp))
    cases hscB : symClasses B with
    | nil => exact absurd (hscB ▸ mem_symClasses.mpr hcB) (by simp)
    | cons d ds =>
      rw [cutMerged_eq_singleton hscB, List.mem_singleton]
      have hempty : (ds.foldl Cls.inter d).isEmpty = true := by
        rw [Cls.isEmpty_iff]
        intro ch
        have hA' : inCls ch (cs.foldl Cls.inter c) = false := (Cls.isEmpty_iff _).mp hAempty ch
        have hex : ∃ cl ∈ c :: cs, inCls ch cl = false := by
          by_contra hcon
          push_neg at hcon
          have hall : inCls ch (cs.foldl Cls.inter c) = true := by
            rw [inCls_foldl_inter, Bool.and_eq_true, List.all_eq_true]
            exact ⟨by simpa using hcon c (by simp),
              fun cl hcl => by simpa using hcon cl (by simp [hcl])⟩
          rw [hA'] at hall
          simp at hall
        obtain ⟨cl, hcl, hclch⟩ := hex
        have hclB : cl ∈ d :: ds := by
          rw [← hscB]
          exact mem_symClasses.mpr (h cl (mem_symClasses.mp (by rw [hsc]; exact hcl)))
        rw [inCls_foldl_inter, Bool.and_eq_false_iff]
        rcases List.mem_cons.mp hclB with rfl | hclB
        · exact Or.inl hclch
        · refine Or.inr ?_
          rw [Bool.eq_false_iff, Ne, List.all_eq_true]
          intro hall
          have hcontra := hall cl hclB
          simp [hclch] at hcontra
      rw [Smart.sym_def, if_pos hempty]

/-- Merging an already merged block of `sym` members changes nothing. -/
theorem cutMerged_append_merge {A B : List RE} (hA : SymsSmart A)
    (hnil : RE.nil ∉ cutMerged A) :
    cutMerged (cutMerged A ++ B) = cutMerged (A ++ B) := by
  have hsc : symClasses (A ++ B) = symClasses A ++ symClasses B := by
    simp [symClasses, List.filterMap_append]
  cases hCA : symClasses A with
  | nil =>
    rw [cutMerged_eq_nil hCA, List.nil_append]
    refine (cutMerged_congr ?_).symm
    intro cl
    simp only [List.mem_append]
    constructor
    · rintro (h | h)
      · exact absurd (hCA ▸ mem_symClasses.mpr h) (by simp)
      · exact h
    · exact Or.inr
  | cons c cs =>
    have hnorm : Cls.Normal (cs.foldl Cls.inter c) := by
      refine Cls.normal_foldl_inter (normal_of_sym_eq (hA c ?_)) ?_
      · exact mem_symClasses.mp (by rw [hCA]; simp)
      · intro x hx
        exact normal_of_sym_eq (hA x (mem_symClasses.mp (by rw [hCA]; simp [hx])))
    have hne : sym (cs.foldl Cls.inter c) ≠ .nil := by
      intro hc
      exact hnil (by rw [cutMerged_eq_singleton hCA, hc]; simp)
    have hval : cutMerged A = [RE.sym (cs.foldl Cls.inter c)] := by
      rw [cutMerged_eq_singleton hCA, Smart.sym_def, if_neg, hnorm]
      intro hemp
      exact hne (by rw [Smart.sym_def, if_pos hemp])
    rw [hval]
    have hsc1 : symClasses (RE.sym (cs.foldl Cls.inter c) :: B) =
        (cs.foldl Cls.inter c) :: symClasses B := by simp [symClasses]
    rw [cutMerged_eq_singleton (by rw [List.singleton_append]; exact hsc1),
      cutMerged_eq_singleton (show symClasses (A ++ B) = c :: (cs ++ symClasses B) from by
        rw [hsc, hCA, List.cons_append]), List.foldl_append]

/-- Associativity of the smart intersection. -/
theorem cutL_nest {M rs : List RE} (hM : SymsSmart (cutFlat M)) :
    cutL (cutL M :: rs) = cutL (M ++ rs) := by
  by_cases hnilM : RE.nil ∈ cutFlat M
  · have h1 : cutL M = .nil := by rw [cutL_eq', if_pos hnilM]
    rw [h1, cutL_cons_nil, cutL_eq', if_pos (by rw [cutFlat_append]; simp [hnilM])]
  · by_cases hcol : RE.nil ∈ cutMerged ((cutFlat M).filter isSym)
    · have h1 : cutL M = .nil := by rw [cutL_eq', if_neg hnilM, cutBody_eq', if_pos hcol]
      rw [h1, cutL_cons_nil, cutL_eq']
      by_cases hnilr : RE.nil ∈ cutFlat rs
      · rw [if_pos (by rw [cutFlat_append]; simp [hnilr])]
      · rw [if_neg (by rw [cutFlat_append]; simp [hnilM, hnilr]), cutBody_eq', if_pos]
        refine cutMerged_nil_mono ?_ hcol
        intro cl hcl
        rw [List.mem_filter] at hcl ⊢
        rw [cutFlat_append]
        exact ⟨List.mem_append_left _ hcl.1, hcl.2⟩
    · have hN := cutToList_cutL hnilM hcol
      have hNnil : RE.nil ∉ cutToList (cutL M) := nil_not_mem_cutToList_cutL hnilM hcol
      have hmemN : ∀ x, x ∈ cutToList (cutL M) ↔
          (x ∈ cutMerged ((cutFlat M).filter isSym) ∨ x ∈ (cutFlat M).filter (not ∘ isSym)) := by
        intro x; rw [hN, mem_sortDedup, List.mem_append]
      have hsyms : ∀ cl : Cls, RE.sym cl ∈ cutToList (cutL M) ++ cutFlat rs ↔
          RE.sym cl ∈ cutMerged ((cutFlat M).filter isSym) ++ cutFlat rs := by
        intro cl
        simp only [List.mem_append, hmemN, List.mem_filter, Function.comp_apply,
          isSym, Bool.not_true, Bool.false_eq_true, and_false, or_false]
      have hmerge : cutMerged (cutToList (cutL M) ++ cutFlat rs) =
          cutMerged (cutFlat M ++ cutFlat rs) := by
        have hMf : SymsSmart ((cutFlat M).filter isSym) :=
          fun cl hcl => hM cl (List.mem_of_mem_filter hcl)
        rw [cutMerged_congr hsyms, cutMerged_append_merge hMf hcol]
        exact cutMerged_congr (by
          intro cl
          simp only [List.mem_append, List.mem_filter, isSym, and_true])
      rw [cutL_eq' (cutL M :: rs), cutL_eq' (M ++ rs), cutFlat_cons, cutFlat_append]
      by_cases hnilr : RE.nil ∈ cutFlat rs
      · rw [if_pos (by simp [hnilr]), if_pos (by simp [hnilr])]
      · rw [if_neg (by simp [hNnil, hnilr]), if_neg (by simp [hnilM, hnilr]),
          cutBody_eq', cutBody_eq', cutMerged_filter, cutMerged_filter, hmerge]
        congr 2
        apply sortDedup_eq_of_mem_iff
        intro x
        rw [List.mem_append, List.mem_append]
        refine or_congr Iff.rfl ?_
        simp only [List.mem_filter, Function.comp_apply, Bool.not_eq_true']
        constructor
        · rintro ⟨hx, hns⟩
          refine ⟨?_, hns⟩
          rcases List.mem_append.mp hx with hx | hx
          · rcases (hmemN x).mp hx with hx' | hx'
            · exfalso
              obtain ⟨cl, rfl⟩ := cutMerged_shape _ x hx'
              by_cases hcl : sym cl = RE.nil
              · exact hcol (hcl ▸ hx')
              · rw [Smart.sym_def,
                  if_neg fun hemp => hcl (by rw [Smart.sym_def, if_pos hemp])] at hns
                simp [isSym] at hns
            · exact List.mem_append_left _ (List.mem_of_mem_filter hx')
          · exact List.mem_append_right _ hx
        · rintro ⟨hx, hns⟩
          refine ⟨?_, hns⟩
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ ((hmemN x).mpr (Or.inr (List.mem_filter.mpr
              ⟨hx, by simp [hns]⟩)))
          · exact List.mem_append_right _ hx

end Redgrep

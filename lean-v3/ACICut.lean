import ACIDefs

/-!
# The intersection case of the ACI layer

Dual to `ACIAlt.lean`: everything about `cutToList` / `cutOfList` / `cutL`
needed for the `IsCanon` ↔ `Canonical` equivalence.  The asymmetries with the
union case are that `cutToList` drops `top` (not `nil`), that `nil` is
absorbing, and that the empty intersection is `top`.
-/

namespace Redgrep

open Smart

/-! ### Flattening and rebuilding intersections -/

theorem cutToList_eq_singleton {r : RE} (htop : r ≠ top) (hnc : NotCut r) :
    cutToList r = [r] := by
  cases r with
  | cut a b => exact absurd hnc (by simp)
  | not a =>
    rw [Smart.cutToList_not, if_neg]
    intro hc
    exact htop (by rw [hc]; rfl)
  | _ => rfl

theorem mem_cutToList_shape {r : RE} : ∀ x ∈ cutToList r, NotCut x ∧ x ≠ top := by
  induction r with
  | cut a b iha ihb =>
    intro x hx
    rw [Smart.cutToList_cut, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha x hx
    · exact ihb x hx
  | not a _ =>
    intro x hx
    rw [Smart.cutToList_not] at hx
    split at hx
    · simp at hx
    · rw [List.mem_singleton] at hx
      subst hx
      refine ⟨by trivial, ?_⟩
      intro hc
      rename_i hne
      exact hne (by injection hc)
  | _ =>
    intro x hx
    rw [show cutToList _ = [_] from rfl, List.mem_singleton] at hx
    subst hx
    exact ⟨by trivial, by simp [top]⟩

/-- Members of the flattened intersection of a canonical term are canonical. -/
theorem isCanon_of_mem_cutToList {r : RE} (h : IsCanon r) :
    ∀ x ∈ cutToList r, IsCanon x := by
  induction r with
  | cut a b iha ihb =>
    obtain ⟨ha, hb, -, -, -, -⟩ := isCanon_cut_iff.mp h
    intro x hx
    rw [Smart.cutToList_cut, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha ha x hx
    · exact ihb hb x hx
  | not a _ =>
    intro x hx
    rw [Smart.cutToList_not] at hx
    split at hx
    · simp at hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact h
  | _ =>
    intro x hx
    rw [show cutToList _ = [_] from rfl, List.mem_singleton] at hx
    subst hx
    exact h

theorem cutToList_ne_nil {r : RE} (h : IsCanon r) (htop : r ≠ top) : cutToList r ≠ [] := by
  induction r with
  | cut a b iha _ =>
    obtain ⟨ha, -, -, hatop, -⟩ := isCanon_cut_iff.mp h
    rw [Smart.cutToList_cut]
    simp only [ne_eq, List.append_eq_nil_iff, not_and]
    intro hc
    exact absurd hc (iha ha hatop)
  | _ => rw [cutToList_eq_singleton htop (by trivial)]; simp

/-- Rebuilding a flattened intersection recovers a canonical term. -/
theorem cutOfList_cutToList {r : RE} (h : IsCanon r) (htop : r ≠ top) :
    cutOfList (cutToList r) = r := by
  induction r with
  | cut a b iha ihb =>
    obtain ⟨ha, hb, hnc, hatop, hbtop, -⟩ := isCanon_cut_iff.mp h
    rw [Smart.cutToList_cut, cutToList_eq_singleton hatop hnc, List.singleton_append]
    have hb' : cutToList b ≠ [] := cutToList_ne_nil hb hbtop
    cases hlb : cutToList b with
    | nil => exact absurd hlb hb'
    | cons y ys => rw [Smart.cutOfList_cons, if_neg (by simp), ← hlb, ihb hb hbtop]
  | _ => rw [cutToList_eq_singleton htop (by trivial)]; rfl

/-- Flattening a rebuilt intersection list is the identity, provided its
members are not themselves intersections (and not `top`). -/
theorem cutToList_cutOfList {L : List RE}
    (h : ∀ x ∈ L, x ≠ top ∧ NotCut x) : cutToList (cutOfList L) = L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hxt, hxc⟩ := h x (by simp)
    rw [Smart.cutOfList_cons]
    split
    · rename_i hnil
      subst hnil
      exact cutToList_eq_singleton hxt hxc
    · rw [Smart.cutToList_cut, cutToList_eq_singleton hxt hxc,
        ih fun y hy => h y (by simp [hy])]
      rfl

theorem cutOfList_ne_top {L : List RE} (hne : L ≠ []) (h : ∀ x ∈ L, x ≠ top) :
    cutOfList L ≠ top := by
  cases L with
  | nil => exact absurd rfl hne
  | cons x xs =>
    rw [Smart.cutOfList_cons]
    split
    · exact h x (by simp)
    · simp [top]

/-! ### The merged `sym` member -/

theorem sym_ne_top' (cl : Cls) : sym cl ≠ top := by
  rw [Smart.sym_def]; split <;> simp [top]

theorem notCut_sym (cl : Cls) : NotCut (sym cl) := by
  rw [Smart.sym_def]; split <;> trivial

/-- The body built by `cutL` is either `nil`, or an intersection over the
non-`sym` members together with at most one merged `sym` member. -/
theorem cutBody_cases (syms rest : List RE) :
    cutBody syms rest = .nil ∨
      ∃ M : List RE, (∀ x ∈ M, ∃ cl, x = sym cl ∧ sym cl ≠ .nil) ∧
        M.length ≤ 1 ∧ cutBody syms rest = cutOfList (sortDedup (M ++ rest)) := by
  unfold cutBody
  split
  · exact Or.inr ⟨[], by simp, by simp, by simp⟩
  · rename_i c cs _
    split
    · exact Or.inl rfl
    · rename_i s hs
      refine Or.inr ⟨[sym (List.foldl Cls.inter c cs)], ?_, by simp, by simp⟩
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨_, rfl, hs⟩

theorem mem_filter_append_filter_not' {α : Type*} (p : α → Bool) (L : List α) (x : α) :
    x ∈ L.filter p ++ L.filter (fun y => not (p y)) ↔ x ∈ L := by
  simp only [List.mem_append, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    cases hp : p x
    · exact Or.inr ⟨h, rfl⟩
    · exact Or.inl ⟨h, rfl⟩

/-! ### `cutL` lands in `IsCanon` -/

theorem CutListOK.tail {x : RE} {xs : List RE} (h : CutListOK (x :: xs)) : CutListOK xs := by
  obtain ⟨hp, hn, hm, hs⟩ := h
  refine ⟨hp.of_cons, (List.nodup_cons.mp hn).2, fun y hy => hm y (by simp [hy]), ?_⟩
  rw [List.filter_cons] at hs
  split at hs
  · simp only [List.length_cons] at hs; omega
  · exact hs

/-- A normal member list rebuilds to a canonical intersection. -/
theorem isCanon_cutOfList {L : List RE} (hok : CutListOK L)
    (hc : ∀ x ∈ L, IsCanon x) : IsCanon (cutOfList L) := by
  induction L with
  | nil => exact isCanon_top
  | cons x xs ih =>
    obtain ⟨hp, hn, hm, hsym⟩ := hok
    obtain ⟨hxn, hxt, hxc⟩ := hm x (by simp)
    rw [Smart.cutOfList_cons]
    split
    · exact hc x (by simp)
    · rename_i hxsne
      refine ⟨hc x (by simp), ih (CutListOK.tail ⟨hp, hn, hm, hsym⟩)
        (fun y hy => hc y (by simp [hy])), hxc, hxt, ?_, ?_⟩
      · exact cutOfList_ne_top hxsne (fun y hy => (hm y (by simp [hy])).2.1)
      · rw [cutToList_eq_singleton hxt hxc, List.singleton_append,
          cutToList_cutOfList (fun y hy => ⟨(hm y (by simp [hy])).2.1, (hm y (by simp [hy])).2.2⟩)]
        exact ⟨hp, hn, hm, hsym⟩

/-- The smart n-ary intersection lands in `IsCanon`. -/
theorem isCanon_cutL {l : List RE} (hIH : ∀ x ∈ l, IsCanon x) : IsCanon (cutL l) := by
  rw [Smart.cutL_eq]
  split
  · exact isCanon_nil
  · rename_i hnil
    rcases cutBody_cases ((l.flatMap cutToList).filter isSym)
        ((l.flatMap cutToList).filter (not ∘ isSym)) with hb | ⟨M, hM, hMlen, hb⟩
    · rw [hb]; exact isCanon_nil
    · rw [hb]
      refine isCanon_cutOfList ⟨sortDedup_sorted _, sortDedup_nodup _, ?_, ?_⟩ ?_
      · intro x hx
        rw [mem_sortDedup, List.mem_append] at hx
        rcases hx with hx | hx
        · obtain ⟨cl, rfl, hne⟩ := hM x hx
          exact ⟨hne, sym_ne_top' cl, notCut_sym cl⟩
        · have hf := List.mem_of_mem_filter hx
          have hshape : NotCut x ∧ x ≠ top := by
            obtain ⟨r, -, hxr⟩ := List.mem_flatMap.mp hf
            exact mem_cutToList_shape x hxr
          exact ⟨fun hc => hnil (hc ▸ hf), hshape.2, hshape.1⟩
      · have hsub : (sortDedup (M ++ (l.flatMap cutToList).filter (not ∘ isSym))).filter isSym
            ⊆ M := by
          intro x hx
          rw [List.mem_filter, mem_sortDedup, List.mem_append] at hx
          rcases hx.1 with h | h
          · exact h
          · exfalso
            have h2 := (List.mem_filter.mp h).2
            simp only [Function.comp_apply, Bool.not_eq_true'] at h2
            rw [h2] at hx
            simp at hx
        exact le_trans (List.Subperm.length_le (List.subperm_of_subset
          ((sortDedup_nodup _).filter _) hsub)) hMlen
      · intro x hx
        rw [mem_sortDedup, List.mem_append] at hx
        rcases hx with hx | hx
        · obtain ⟨cl, rfl, -⟩ := hM x hx
          exact isCanon_sym cl
        · obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.mp (List.mem_of_mem_filter hx)
          exact isCanon_of_mem_cutToList (hIH r hr) x hxr

theorem isCanon_cut2 {x y : RE} (hx : IsCanon x) (hy : IsCanon y) : IsCanon (cut2 x y) :=
  isCanon_cutL (by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hx
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hy
      · simp at hr)

/-- A canonical intersection is a fixed point of the smart intersection. -/
theorem cut2_eq_self {a b : RE} (h : IsCanon (.cut a b)) : cut2 a b = .cut a b := by
  obtain ⟨ha, hb, hnc, hatop, hbtop, hok⟩ := isCanon_cut_iff.mp h
  obtain ⟨hp, hn, hm, hlen⟩ := hok
  have hflat : [a, b].flatMap cutToList = cutToList a ++ cutToList b := by simp
  rw [cut2, cutL_eq, hflat]
  set L : List RE := cutToList a ++ cutToList b with hL
  rw [if_neg (fun hc => (hm .nil hc).1 rfl)]
  have hrest : ∀ x, x ∈ L.filter isSym ++ L.filter (not ∘ isSym) ↔ x ∈ L := by
    intro x
    have := mem_filter_append_filter_not' isSym L x
    simpa [Function.comp_def] using this
  have hsort : sortDedup L = L := sortDedup_eq_self hp hn
  have hbody : cutBody (L.filter isSym) (L.filter (not ∘ isSym))
      = cutOfList (sortDedup (L.filter isSym ++ L.filter (not ∘ isSym))) := by
    cases hf : L.filter isSym with
    | nil =>
      show (match symClasses [] with
        | [] => cutOfList (sortDedup (L.filter (not ∘ isSym)))
        | c :: cs => match sym (cs.foldl Cls.inter c) with
            | RE.nil => RE.nil
            | s => cutOfList (sortDedup (s :: L.filter (not ∘ isSym)))) = _
      rw [show symClasses ([] : List RE) = [] from rfl]
      simp
    | cons s ss =>
      have hss : ss = [] := by
        rw [hf] at hlen
        simp only [List.length_cons] at hlen
        exact List.length_eq_zero_iff.mp (by omega)
      subst hss
      have hsmem : s ∈ L := List.mem_of_mem_filter (by rw [hf]; simp)
      have hsis : isSym s = true := (List.mem_filter.mp (by rw [hf]; simp : s ∈ L.filter isSym)).2
      obtain ⟨cl, rfl⟩ := isSym_iff.mp hsis
      have hcanon : IsCanon (RE.sym cl) := by
        rcases List.mem_append.mp hsmem with hs | hs
        · exact isCanon_of_mem_cutToList ha _ hs
        · exact isCanon_of_mem_cutToList hb _ hs
      show (match symClasses [RE.sym cl] with
        | [] => cutOfList (sortDedup (L.filter (not ∘ isSym)))
        | c :: cs => match sym (cs.foldl Cls.inter c) with
            | RE.nil => RE.nil
            | s => cutOfList (sortDedup (s :: L.filter (not ∘ isSym)))) = _
      rw [show symClasses [RE.sym cl] = [cl] from rfl]
      show (match sym cl with
        | RE.nil => RE.nil
        | s => cutOfList (sortDedup (s :: L.filter (not ∘ isSym)))) = _
      rw [hcanon]
      rfl
  rw [hbody, sortDedup_eq_of_mem_iff hrest, hsort, hL, ← Smart.cutToList_cut]
  exact cutOfList_cutToList h (by simp [top])

end Redgrep

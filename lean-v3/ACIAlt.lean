import ACIDefs

/-!
# The union case of the ACI layer

Everything about `altToList` / `altOfList` / `altL` needed for the
`IsCanon` ↔ `Canonical` equivalence:

* the flattening/rebuilding round trips (`altOfList_altToList`,
  `altToList_altOfList`),
* `altL` lands in `IsCanon` (`isCanon_altL`),
* a canonical union is a fixed point of `alt2` (`alt2_eq_self`).

The only genuinely ACI-flavoured step is the last one: `altL` re-sorts and
deduplicates its member list and merges all `sym` members into a single class,
and one has to see that on an already-normal member list all of that is the
identity.  Both directions go through `sortDedup_eq_of_mem_iff`
(`REOrder.lean`): the normal form depends only on the *set* of members.
-/

namespace Redgrep

open Smart

/-! ### Flattening and rebuilding unions -/

theorem altToList_eq_singleton {r : RE} (hnil : r ≠ .nil) (hna : NotAlt r) :
    altToList r = [r] := by
  cases r <;> simp_all [NotAlt]

theorem mem_altToList_shape {r : RE} : ∀ x ∈ altToList r, NotAlt x ∧ x ≠ .nil := by
  induction r with
  | alt a b iha ihb =>
    intro x hx
    rw [Smart.altToList_alt, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha x hx
    · exact ihb x hx
  | nil => intro x hx; simp at hx
  | _ =>
    intro x hx
    rw [altToList_eq_singleton (by simp) (by trivial), List.mem_singleton] at hx
    subst hx
    exact ⟨by trivial, by simp⟩

/-- Members of the flattened union of a canonical term are canonical. -/
theorem isCanon_of_mem_altToList {r : RE} (h : IsCanon r) :
    ∀ x ∈ altToList r, IsCanon x := by
  induction r with
  | alt a b iha ihb =>
    obtain ⟨ha, hb, -, -, -, -⟩ := isCanon_alt_iff.mp h
    intro x hx
    rw [Smart.altToList_alt, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha ha x hx
    · exact ihb hb x hx
  | nil => intro x hx; simp at hx
  | _ =>
    intro x hx
    rw [altToList_eq_singleton (by simp) (by trivial), List.mem_singleton] at hx
    subst hx
    exact h

theorem altToList_ne_nil {r : RE} (h : IsCanon r) (hnil : r ≠ .nil) : altToList r ≠ [] := by
  induction r with
  | alt a b iha _ =>
    obtain ⟨ha, -, -, hanil, -⟩ := isCanon_alt_iff.mp h
    rw [Smart.altToList_alt]
    simp only [ne_eq, List.append_eq_nil_iff, not_and]
    intro hc
    exact absurd hc (iha ha hanil)
  | nil => exact absurd rfl hnil
  | _ => rw [altToList_eq_singleton hnil (by trivial)]; simp

/-- Rebuilding a flattened union recovers a canonical term. -/
theorem altOfList_altToList {r : RE} (h : IsCanon r) (hnil : r ≠ .nil) :
    altOfList (altToList r) = r := by
  induction r with
  | alt a b iha ihb =>
    obtain ⟨ha, hb, hna, hanil, hbnil, -⟩ := isCanon_alt_iff.mp h
    rw [Smart.altToList_alt, altToList_eq_singleton hanil hna, List.singleton_append]
    have hb' : altToList b ≠ [] := altToList_ne_nil hb hbnil
    cases hlb : altToList b with
    | nil => exact absurd hlb hb'
    | cons y ys => rw [Smart.altOfList_cons, if_neg (by simp), ← hlb, ihb hb hbnil]
  | nil => exact absurd rfl hnil
  | _ => rw [altToList_eq_singleton hnil (by trivial)]; rfl

/-- Flattening a rebuilt union list is the identity, provided its members are
not themselves unions (and not `nil`). -/
theorem altToList_altOfList {L : List RE}
    (h : ∀ x ∈ L, x ≠ .nil ∧ NotAlt x) : altToList (altOfList L) = L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hxn, hxa⟩ := h x (by simp)
    rw [Smart.altOfList_cons]
    split
    · rename_i hnil
      subst hnil
      exact altToList_eq_singleton hxn hxa
    · rw [Smart.altToList_alt, altToList_eq_singleton hxn hxa,
        ih fun y hy => h y (by simp [hy])]
      rfl

theorem altOfList_ne_nil {L : List RE} (hne : L ≠ []) (h : ∀ x ∈ L, x ≠ .nil) :
    altOfList L ≠ .nil := by
  cases L with
  | nil => exact absurd rfl hne
  | cons x xs =>
    rw [Smart.altOfList_cons]
    split
    · exact h x (by simp)
    · simp

/-! ### The merged `sym` member -/

theorem sym_ne_top (cl : Cls) : sym cl ≠ top := by
  rw [Smart.sym_def]; split <;> simp [top]

theorem notAlt_sym (cl : Cls) : NotAlt (sym cl) := by
  rw [Smart.sym_def]; split <;> trivial

theorem altMerged_cases (syms : List RE) :
    altMerged syms = [] ∨ ∃ cl : Cls, altMerged syms = [sym cl] ∧ sym cl ≠ .nil := by
  unfold altMerged
  split
  · exact Or.inl rfl
  · rename_i c cs _
    split
    · exact Or.inl rfl
    · rename_i s hs
      exact Or.inr ⟨List.foldl Cls.union c cs, rfl, hs⟩

theorem altMerged_length (syms : List RE) : (altMerged syms).length ≤ 1 := by
  rcases altMerged_cases syms with h | ⟨cl, h, -⟩ <;> rw [h] <;> simp

/-- Merging a single already-smart `sym` member is the identity. -/
theorem altMerged_singleton {cl : Cls} (h : sym cl = .sym cl) :
    altMerged [RE.sym cl] = [RE.sym cl] := by
  show (match symClasses [RE.sym cl] with
    | [] => []
    | c :: cs => match sym (cs.foldl Cls.union c) with | .nil => [] | s => [s]) = _
  rw [show symClasses [RE.sym cl] = [cl] from rfl]
  show (match sym cl with | .nil => [] | s => [s]) = _
  rw [h]

theorem mem_filter_append_filter_not {α : Type*} (p : α → Bool) (L : List α) (x : α) :
    x ∈ L.filter p ++ L.filter (fun y => not (p y)) ↔ x ∈ L := by
  simp only [List.mem_append, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    cases hp : p x
    · exact Or.inr ⟨h, rfl⟩
    · exact Or.inl ⟨h, rfl⟩

/-! ### `altL` lands in `IsCanon` -/

theorem AltListOK.tail {x : RE} {xs : List RE} (h : AltListOK (x :: xs)) : AltListOK xs := by
  obtain ⟨hp, hn, hm, hs⟩ := h
  refine ⟨hp.of_cons, (List.nodup_cons.mp hn).2, fun y hy => hm y (by simp [hy]), ?_⟩
  rw [List.filter_cons] at hs
  split at hs
  · simp only [List.length_cons] at hs; omega
  · exact hs

/-- A normal member list rebuilds to a canonical union. -/
theorem isCanon_altOfList {L : List RE} (hok : AltListOK L)
    (hc : ∀ x ∈ L, IsCanon x) : IsCanon (altOfList L) := by
  induction L with
  | nil => exact isCanon_nil
  | cons x xs ih =>
    obtain ⟨hp, hn, hm, hsym⟩ := hok
    obtain ⟨hxn, hxt, hxa⟩ := hm x (by simp)
    rw [Smart.altOfList_cons]
    split
    · exact hc x (by simp)
    · rename_i hxsne
      refine ⟨hc x (by simp), ih (AltListOK.tail ⟨hp, hn, hm, hsym⟩)
        (fun y hy => hc y (by simp [hy])), hxa, hxn, ?_, ?_⟩
      · exact altOfList_ne_nil hxsne (fun y hy => (hm y (by simp [hy])).1)
      · rw [altToList_eq_singleton hxn hxa, List.singleton_append,
          altToList_altOfList (fun y hy => ⟨(hm y (by simp [hy])).1, (hm y (by simp [hy])).2.2⟩)]
        exact ⟨hp, hn, hm, hsym⟩

/-- The smart n-ary union lands in `IsCanon`. -/
theorem isCanon_altL {l : List RE} (hIH : ∀ x ∈ l, IsCanon x) : IsCanon (altL l) := by
  rw [Smart.altL_eq]
  split
  · exact isCanon_top
  · rename_i htop
    refine isCanon_altOfList ⟨sortDedup_sorted _, sortDedup_nodup _, ?_, ?_⟩ ?_
    · intro x hx
      rw [mem_sortDedup, List.mem_append] at hx
      rcases hx with hx | hx
      · rcases altMerged_cases ((l.flatMap altToList).filter isSym) with h0 | ⟨cl, h0, hne⟩
        · rw [h0] at hx; simp at hx
        · rw [h0, List.mem_singleton] at hx
          subst hx
          exact ⟨hne, sym_ne_top cl, notAlt_sym cl⟩
      · have hf := List.mem_of_mem_filter hx
        have hshape : NotAlt x ∧ x ≠ .nil := by
          obtain ⟨r, -, hxr⟩ := List.mem_flatMap.mp hf
          exact mem_altToList_shape x hxr
        exact ⟨hshape.2, fun hc => htop (hc ▸ hf), hshape.1⟩
    · have hsub : (sortDedup (altMerged ((l.flatMap altToList).filter isSym) ++
          (l.flatMap altToList).filter (not ∘ isSym))).filter isSym ⊆
          altMerged ((l.flatMap altToList).filter isSym) := by
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
        ((sortDedup_nodup _).filter _) hsub)) (altMerged_length _)
    · intro x hx
      rw [mem_sortDedup, List.mem_append] at hx
      rcases hx with hx | hx
      · rcases altMerged_cases ((l.flatMap altToList).filter isSym) with h0 | ⟨cl, h0, -⟩
        · rw [h0] at hx; simp at hx
        · rw [h0, List.mem_singleton] at hx
          subst hx
          exact isCanon_sym cl
      · obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.mp (List.mem_of_mem_filter hx)
        exact isCanon_of_mem_altToList (hIH r hr) x hxr

theorem isCanon_alt2 {x y : RE} (hx : IsCanon x) (hy : IsCanon y) : IsCanon (alt2 x y) :=
  isCanon_altL (by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hx
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hy
      · simp at hr)

/-- A canonical union is a fixed point of the smart union: this is the union
half of `canon r = r` for canonical `r`. -/
theorem alt2_eq_self {a b : RE} (h : IsCanon (.alt a b)) : alt2 a b = .alt a b := by
  obtain ⟨ha, hb, hna, hanil, hbnil, hok⟩ := isCanon_alt_iff.mp h
  obtain ⟨hp, hn, hm, hlen⟩ := hok
  have hflat : [a, b].flatMap altToList = altToList a ++ altToList b := by simp
  rw [alt2, altL_eq, hflat]
  set L : List RE := altToList a ++ altToList b with hL
  rw [if_neg (fun hc => (hm top hc).2.1 rfl)]
  have hrest : ∀ x, x ∈ L.filter isSym ++ L.filter (not ∘ isSym) ↔ x ∈ L := by
    intro x
    have := mem_filter_append_filter_not isSym L x
    simpa [Function.comp_def] using this
  have hsort : sortDedup L = L := sortDedup_eq_self hp hn
  have hmerge : altMerged (L.filter isSym) = L.filter isSym := by
    cases hf : L.filter isSym with
    | nil => rfl
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
        · exact isCanon_of_mem_altToList ha _ hs
        · exact isCanon_of_mem_altToList hb _ hs
      exact altMerged_singleton hcanon
  rw [hmerge, sortDedup_eq_of_mem_iff hrest, hsort, hL, ← Smart.altToList_alt]
  exact altOfList_altToList h (by simp)

end Redgrep

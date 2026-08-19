import ClsAlg
import ACIAlt

/-!
# The ACI algebra of the smart union

`ACIAlt.lean` shows that `altL` *lands* in the canonical fragment.  This file
proves the laws it satisfies there, which is what the derivative-closure
programme (`Closure.lean`, `Bounds.lean`) needs:

* `altL_congr_mem` — `altL rs` depends only on the *set* of flattened members;
* `altL_singleton` — `altL [z] = z` on canonical `z` (so `altL` is idempotent);
* `altL_nest` — a union member that is itself a union can be spliced in
  (`altL (altL M :: rs) = altL (M ++ rs)`), the associativity law;
* `altL_map_hom` — any operation that is a homomorphism for `.alt`, `nil`,
  `top` and class union commutes with `altL`.  Instantiated at `deriv c` and
  `derivW u` in `Closure.lean`, this is what makes the reachable state set of
  a union the (finite) set of pairwise unions of the two component states.

The `sym` members are the delicate part throughout: `altL` merges them into a
single class by folding `Cls.union`, so all the laws above rest on the fold
being independent of the order and multiplicity of the classes folded
(`ClsAlg.lean`).
-/

namespace Redgrep

open Smart

/-- The flattened member list of a list of union operands. -/
def altFlat (rs : List RE) : List RE := rs.flatMap altToList

@[simp] theorem altFlat_nil : altFlat [] = [] := rfl

@[simp] theorem altFlat_cons (r : RE) (rs : List RE) :
    altFlat (r :: rs) = altToList r ++ altFlat rs := rfl

theorem altFlat_append (rs ss : List RE) :
    altFlat (rs ++ ss) = altFlat rs ++ altFlat ss := List.flatMap_append

theorem mem_altFlat {x : RE} {rs : List RE} :
    x ∈ altFlat rs ↔ ∃ r ∈ rs, x ∈ altToList r := List.mem_flatMap

theorem altL_eq' (rs : List RE) :
    altL rs =
      (if top ∈ altFlat rs then top
       else altOfList (sortDedup (altMerged ((altFlat rs).filter isSym) ++
              (altFlat rs).filter (not ∘ isSym)))) := altL_eq rs

/-- Every `sym` member of `L` is already smart. -/
def SymsSmart (L : List RE) : Prop := ∀ cl : Cls, RE.sym cl ∈ L → sym cl = .sym cl

theorem symsSmart_of_isCanon {L : List RE} (h : ∀ x ∈ L, IsCanon x) : SymsSmart L :=
  fun _ hcl => h _ hcl

/-! ### The merged `sym` member depends only on the set of classes -/

theorem altMerged_congr {A B : List RE} (h : ∀ cl : Cls, RE.sym cl ∈ A ↔ RE.sym cl ∈ B) :
    altMerged A = altMerged B := by
  have hcl : ∀ cl, cl ∈ symClasses A ↔ cl ∈ symClasses B := by
    intro cl; rw [mem_symClasses, mem_symClasses]; exact h cl
  cases hA : symClasses A with
  | nil =>
    cases hB : symClasses B with
    | nil => simp only [altMerged, hA, hB]
    | cons d ds =>
      exact absurd (hA ▸ (hcl d).mpr (by rw [hB]; simp)) (by simp)
  | cons c cs =>
    cases hB : symClasses B with
    | nil =>
      exact absurd (hB ▸ (hcl c).mp (by rw [hA]; simp)) (by simp)
    | cons d ds =>
      have hfold : cs.foldl Cls.union c = ds.foldl Cls.union d :=
        Cls.foldl_union_congr (by intro x; rw [← hA, ← hB]; exact hcl x)
      simp only [altMerged, hA, hB, hfold]

/-! ### `altL` depends only on the set of flattened members -/

theorem altL_congr_mem {rs ss : List RE} (h : ∀ x, x ∈ altFlat rs ↔ x ∈ altFlat ss) :
    altL rs = altL ss := by
  rw [altL_eq', altL_eq']
  by_cases htop : top ∈ altFlat rs
  · rw [if_pos htop, if_pos ((h top).mp htop)]
  · rw [if_neg htop, if_neg fun hc => htop ((h top).mpr hc)]
    have hm : altMerged ((altFlat rs).filter isSym) = altMerged ((altFlat ss).filter isSym) :=
      altMerged_congr (by
        intro cl
        simp only [List.mem_filter, isSym, h (RE.sym cl)])
    rw [hm, sortDedup_eq_of_mem_iff]
    intro x
    simp only [List.mem_append, List.mem_filter, h x]

theorem altL_perm {rs ss : List RE} (h : rs.Perm ss) : altL rs = altL ss :=
  altL_congr_mem (by
    intro x
    simp only [mem_altFlat]
    exact ⟨fun ⟨r, hr, hx⟩ => ⟨r, h.mem_iff.mp hr, hx⟩,
      fun ⟨r, hr, hx⟩ => ⟨r, h.mem_iff.mpr hr, hx⟩⟩)

theorem altL_nil_eq : altL ([] : List RE) = .nil := by
  rw [altL_eq']
  simp [altFlat, altMerged, symClasses, sortDedup, altOfList]

/-- A `nil` member of a union can be dropped. -/
theorem altL_cons_nil (rs : List RE) : altL (RE.nil :: rs) = altL rs :=
  altL_congr_mem (by intro x; simp [altFlat, altToList])

/-! ### The shape of the rebuilt member list -/

theorem altL_body_shape (rs : List RE) :
    ∀ x ∈ sortDedup (altMerged ((altFlat rs).filter isSym) ++
        (altFlat rs).filter (not ∘ isSym)), x ≠ .nil ∧ NotAlt x := by
  intro x hx
  rw [mem_sortDedup, List.mem_append] at hx
  rcases hx with hx | hx
  · rcases altMerged_cases ((altFlat rs).filter isSym) with h0 | ⟨cl, h0, hne⟩
    · rw [h0] at hx; simp at hx
    · rw [h0, List.mem_singleton] at hx
      subst hx
      exact ⟨hne, notAlt_sym cl⟩
  · have hf := List.mem_of_mem_filter hx
    obtain ⟨r, -, hxr⟩ := mem_altFlat.mp hf
    exact ⟨(mem_altToList_shape x hxr).2, (mem_altToList_shape x hxr).1⟩

theorem altToList_altL {rs : List RE} (htop : top ∉ altFlat rs) :
    altToList (altL rs) = sortDedup (altMerged ((altFlat rs).filter isSym) ++
      (altFlat rs).filter (not ∘ isSym)) := by
  rw [altL_eq', if_neg htop]
  exact altToList_altOfList (altL_body_shape rs)

/-- `top` never appears in the rebuilt member list of a `top`-free union. -/
theorem top_not_mem_altToList_altL {rs : List RE} (htop : top ∉ altFlat rs) :
    top ∉ altToList (altL rs) := by
  rw [altToList_altL htop]
  intro hx
  rw [mem_sortDedup, List.mem_append] at hx
  rcases hx with hx | hx
  · rcases altMerged_cases ((altFlat rs).filter isSym) with h0 | ⟨cl, h0, -⟩
    · rw [h0] at hx; simp at hx
    · rw [h0, List.mem_singleton] at hx
      exact sym_ne_top cl hx.symm
  · exact htop (List.mem_of_mem_filter hx)

/-! ### Idempotence -/

theorem altL_singleton_of_shape {z : RE} (hnil : z ≠ .nil) (htop : z ≠ top) (hna : NotAlt z)
    (hsym : ∀ cl, z = .sym cl → sym cl = .sym cl) : altL [z] = z := by
  have hflat : altFlat [z] = [z] := by
    rw [show altFlat [z] = altToList z from by simp [altFlat], altToList_eq_singleton hnil hna]
  rw [altL_eq', hflat, if_neg (by simp [Ne.symm htop])]
  have hsd : ∀ w : RE, sortDedup [w] = [w] := fun w =>
    sortDedup_eq_self (by simp) (by simp)
  by_cases hs : isSym z
  · obtain ⟨cl, rfl⟩ := isSym_iff.mp hs
    rw [show ([RE.sym cl] : List RE).filter isSym = [RE.sym cl] from rfl,
      show ([RE.sym cl] : List RE).filter (not ∘ isSym) = [] from rfl,
      altMerged_singleton (hsym cl rfl), List.append_nil, hsd]
    rfl
  · rw [show ([z] : List RE).filter isSym = [] from by simp [List.filter, hs],
      show ([z] : List RE).filter (not ∘ isSym) = [z] from by
        simp [List.filter, hs],
      show altMerged ([] : List RE) = [] from rfl, List.nil_append, hsd]
    rfl

theorem altL_singleton {z : RE} (h : IsCanon z) : altL [z] = z := by
  by_cases htop : z = top
  · subst htop
    rw [altL_eq', if_pos (by rw [show altFlat [(top : RE)] = [top] from rfl]; simp)]
  by_cases hnil : z = .nil
  · subst hnil; rw [altL_cons_nil, altL_nil_eq]
  match z, h with
  | .alt a b, h =>
    have : altL [RE.alt a b] = altL [a, b] :=
      altL_congr_mem (by intro x; simp [altFlat, Smart.altToList_alt])
    rw [this]
    exact alt2_eq_self h
  | .sym cl, h => exact altL_singleton_of_shape hnil htop trivial (fun cl' heq => by simp only [RE.sym.injEq] at heq; subst heq; exact h)
  | .cut a b, h => exact altL_singleton_of_shape hnil htop trivial (by simp)
  | .seq a b, h => exact altL_singleton_of_shape hnil htop trivial (by simp)
  | .rep a, h => exact altL_singleton_of_shape hnil htop trivial (by simp)
  | .not a, h => exact altL_singleton_of_shape hnil htop trivial (by simp)
  | .invHom hh a, h => exact altL_singleton_of_shape hnil htop trivial (by simp)
  | .eps, h => exact altL_singleton_of_shape hnil htop trivial (by simp)
  | .nil, h => exact absurd rfl hnil

/-! ### Associativity: splicing a union member -/

/-- `altMerged` only looks at the `sym` members. -/
theorem altMerged_filter (L : List RE) : altMerged (L.filter isSym) = altMerged L :=
  altMerged_congr (by
    intro cl
    simp only [List.mem_filter, isSym, and_true])

theorem altToList_top : altToList top = [top] :=
  altToList_eq_singleton (by simp [top]) trivial

/-- The class of a smart `sym` member is inhabited. -/
theorem exists_inCls_of_sym_eq {cl : Cls} (h : sym cl = .sym cl) : ∃ c, inCls c cl = true := by
  by_contra hc
  push_neg at hc
  have : cl.isEmpty = true := (Cls.isEmpty_iff cl).mpr (by
    intro c; simpa using hc c)
  rw [Smart.sym_def, if_pos this] at h
  exact absurd h (by simp)

theorem altMerged_eq_singleton {L : List RE} {c : Cls} {cs : List Cls}
    (hsc : symClasses L = c :: cs) (hne : sym (cs.foldl Cls.union c) ≠ .nil) :
    altMerged L = [sym (cs.foldl Cls.union c)] := by
  simp only [altMerged, hsc]

theorem altMerged_eq_nil {L : List RE} (hsc : symClasses L = []) : altMerged L = [] := by
  simp only [altMerged, hsc]

/-- A fold of inhabited classes is inhabited, so the merged member survives. -/
theorem sym_foldl_ne_nil {c : Cls} {cs : List Cls} (h : sym c = .sym c) :
    sym (cs.foldl Cls.union c) ≠ .nil := by
  obtain ⟨ch, hch⟩ := exists_inCls_of_sym_eq h
  have hfold : inCls ch (cs.foldl Cls.union c) = true := by
    rw [inCls_foldl_union, hch]; rfl
  intro hnil
  rw [Smart.sym_def] at hnil
  split at hnil
  · rename_i hemp
    rw [(Cls.isEmpty_iff _).mp hemp ch] at hfold
    exact absurd hfold (by simp)
  · exact absurd hnil (by simp)

/-- Merging an already merged block of `sym` members changes nothing. -/
theorem altMerged_append_merge {A B : List RE} (hA : SymsSmart A) :
    altMerged (altMerged A ++ B) = altMerged (A ++ B) := by
  have hsc : symClasses (A ++ B) = symClasses A ++ symClasses B := by
    simp [symClasses, List.filterMap_append]
  cases hCA : symClasses A with
  | nil =>
    have hAmerged : altMerged A = [] := by simp only [altMerged, hCA]
    rw [hAmerged, List.nil_append]
    refine (altMerged_congr ?_).symm
    intro cl
    simp only [List.mem_append]
    constructor
    · rintro (h | h)
      · exact absurd (hCA ▸ mem_symClasses.mpr h) (by simp)
      · exact h
    · exact Or.inr
  | cons c cs =>
    have hcA : RE.sym c ∈ A := mem_symClasses.mp (by rw [hCA]; simp)
    obtain ⟨ch, hch⟩ := exists_inCls_of_sym_eq (hA c hcA)
    set F := cs.foldl Cls.union c with hF
    have hFne : F.isEmpty = false := by
      have : inCls ch F = true := by
        rw [hF, inCls_foldl_union, hch]; rfl
      cases hFe : F.isEmpty with
      | false => rfl
      | true =>
        rw [(Cls.isEmpty_iff F).mp hFe ch] at this
        exact absurd this (by simp)
    have hsymF : sym F = .sym F.norm := by rw [Smart.sym_def, if_neg (by simp [hFne])]
    have hAmerged : altMerged A = [RE.sym F.norm] := by
      simp only [altMerged, hCA, ← hF]
      rw [hsymF]
    rw [hAmerged]
    have hsc1 : symClasses (RE.sym F.norm :: B) = F.norm :: symClasses B := by
      simp [symClasses]
    have hnorm : ((symClasses B).foldl Cls.union F.norm).norm =
        ((symClasses B).foldl Cls.union F).norm :=
      Cls.norm_foldl_union_congr (Cls.norm_idem F) _
    simp only [altMerged, hsc1, hsc, hCA, List.singleton_append, List.cons_append,
      List.nil_append, List.foldl_append, ← hF]
    rw [Cls.sym_eq_of_norm_eq hnorm]

/-- Associativity of the smart union: a member that is itself a union may be
spliced into the member list. -/
theorem altL_nest {M rs : List RE} (hM : SymsSmart (altFlat M)) :
    altL (altL M :: rs) = altL (M ++ rs) := by
  rw [altL_eq' (altL M :: rs), altL_eq' (M ++ rs), altFlat_cons, altFlat_append]
  by_cases htopM : top ∈ altFlat M
  · have h1 : altL M = top := by rw [altL_eq', if_pos htopM]
    rw [h1, altToList_top, if_pos (by simp), if_pos (by simp [htopM])]
  · have hN := altToList_altL htopM
    have hNtop : top ∉ altToList (altL M) := top_not_mem_altToList_altL htopM
    have hmemN : ∀ x, x ∈ altToList (altL M) ↔
        (x ∈ altMerged ((altFlat M).filter isSym) ∨ x ∈ (altFlat M).filter (not ∘ isSym)) := by
      intro x; rw [hN, mem_sortDedup, List.mem_append]
    by_cases htopr : top ∈ altFlat rs
    · rw [if_pos (by simp [htopr]), if_pos (by simp [htopr])]
    · rw [if_neg (by simp [hNtop, htopr]), if_neg (by simp [htopM, htopr])]
      have hsym : ∀ cl : Cls, RE.sym cl ∈ altToList (altL M) ++ altFlat rs ↔
          RE.sym cl ∈ altMerged ((altFlat M).filter isSym) ++ altFlat rs := by
        intro cl
        simp only [List.mem_append, hmemN, List.mem_filter, Function.comp_apply,
          isSym, Bool.not_true, Bool.false_eq_true, and_false, or_false]
      have hm : altMerged (altToList (altL M) ++ altFlat rs) =
          altMerged (altFlat M ++ altFlat rs) := by
        rw [altMerged_congr hsym, altMerged_filter, altMerged_append_merge hM]
      rw [altMerged_filter, altMerged_filter, hm, sortDedup_eq_of_mem_iff]
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
            rcases altMerged_cases ((altFlat M).filter isSym) with h0 | ⟨cl, h0, hne⟩
            · rw [h0] at hx'; simp at hx'
            · rw [h0, List.mem_singleton] at hx'
              subst hx'
              have hcl : sym cl = RE.sym cl.norm := by
                rw [Smart.sym_def, if_neg fun hemp => hne (by rw [Smart.sym_def, if_pos hemp])]
              rw [hcl] at hns
              simp [isSym] at hns
          · exact List.mem_append_left _ (List.mem_of_mem_filter hx')
        · exact List.mem_append_right _ hx
      · rintro ⟨hx, hns⟩
        refine ⟨?_, hns⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ ((hmemN x).mpr (Or.inr (List.mem_filter.mpr
            ⟨hx, by simp [hns]⟩)))
        · exact List.mem_append_right _ hx

/-! ### Homomorphisms of the smart union -/

theorem altL_mem_congr {A B : List RE} (h : ∀ y, y ∈ A ↔ y ∈ B) : altL A = altL B :=
  altL_congr_mem (by
    intro x
    simp only [mem_altFlat]
    exact ⟨fun ⟨r, hr, hx⟩ => ⟨r, (h r).mp hr, hx⟩, fun ⟨r, hr, hx⟩ => ⟨r, (h r).mpr hr, hx⟩⟩)

theorem altL_cons_append (x : RE) (L T : List RE) :
    altL (x :: (L ++ T)) = altL (L ++ (x :: T)) :=
  altL_mem_congr (by intro y; simp only [List.mem_cons, List.mem_append]; tauto)

theorem altL_swap2 (x y : RE) (T : List RE) : altL (x :: y :: T) = altL (y :: x :: T) :=
  altL_mem_congr (by intro z; simp only [List.mem_cons]; tauto)

theorem symsSmart_altFlat {L : List RE} (h : ∀ x ∈ L, IsCanon x) : SymsSmart (altFlat L) := by
  intro cl hcl
  obtain ⟨r, hr, hx⟩ := mem_altFlat.mp hcl
  exact isCanon_of_mem_altToList (h r hr) _ hx

theorem altL_nest_canon {M rs : List RE} (h : ∀ x ∈ M, IsCanon x) :
    altL (altL M :: rs) = altL (M ++ rs) :=
  altL_nest (symsSmart_altFlat h)

/-- In a canonical term, `top` can only occur as the whole term. -/
theorem eq_top_of_mem_altToList {z : RE} (hz : IsCanon z) (h : top ∈ altToList z) : z = top := by
  by_cases hna : NotAlt z
  · by_cases hnil : z = .nil
    · subst hnil; simp [altToList] at h
    · rw [altToList_eq_singleton hnil hna, List.mem_singleton] at h
      exact h.symm
  · exfalso
    cases z with
    | alt a b =>
      obtain ⟨-, -, -, -, -, hok⟩ := isCanon_alt_iff.mp hz
      rw [Smart.altToList_alt] at h
      exact (hok.2.2.1 top h).2.1 rfl
    | _ => exact hna trivial

/-- The axioms making an operation commute with the smart union: it is a
homomorphism for `.alt`, fixes `nil` and `top`, turns a merged class back into
a union, agrees on smart and raw `sym` nodes, and preserves canonicity. -/
structure AltHom (F : RE → RE) : Prop where
  map_alt : ∀ a b, F (.alt a b) = alt2 (F a) (F b)
  map_nil : F .nil = .nil
  map_top : F top = top
  map_symUnion : ∀ c₁ c₂ : Cls, F (sym (c₁.union c₂)) = alt2 (F (sym c₁)) (F (sym c₂))
  map_symSmart : ∀ cl : Cls, F (.sym cl) = F (sym cl)
  map_canon : ∀ x, IsCanon x → IsCanon (F x)

namespace AltHom

variable {F : RE → RE}

/-- Flattening commutes with an `AltHom`. -/
theorem flat (hF : AltHom F) {z : RE} (hz : IsCanon z) (T : List RE) :
    altL ((altToList z).map F ++ T) = altL (F z :: T) := by
  induction z generalizing T with
  | alt a b iha ihb =>
    obtain ⟨ha, hb, -, -, -, -⟩ := isCanon_alt_iff.mp hz
    rw [Smart.altToList_alt, List.map_append, List.append_assoc, iha ha,
      altL_cons_append (F a) ((altToList b).map F) T, ihb hb,
      altL_swap2 (F b) (F a) T,
      show altL (F a :: F b :: T) = altL ([F a, F b] ++ T) from rfl,
      ← altL_nest_canon (M := [F a, F b]) (by
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hF.map_canon a ha
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hF.map_canon b hb
          · simp at hx),
      hF.map_alt, alt2]
  | nil => rw [show altToList RE.nil = [] from rfl, List.map_nil, List.nil_append,
      hF.map_nil, altL_cons_nil]
  | _ => rfl

/-- The flattened member list may be used in place of the operand list. -/
theorem flat_list (hF : AltHom F) {rs : List RE} (h : ∀ x ∈ rs, IsCanon x) (T : List RE) :
    altL ((altFlat rs).map F ++ T) = altL (rs.map F ++ T) := by
  induction rs generalizing T with
  | nil => rfl
  | cons z rs ih =>
    rw [altFlat_cons, List.map_append, List.append_assoc,
      hF.flat (h z (by simp)) ((altFlat rs).map F ++ T),
      altL_cons_append (F z) ((altFlat rs).map F) T,
      ih (fun x hx => h x (by simp [hx])) (F z :: T)]
    exact (altL_cons_append (F z) (rs.map F) T).symm

/-- The merged class member may be replaced by the `sym` members it came from. -/
theorem merge (hF : AltHom F) (c : Cls) (cs : List Cls) (T : List RE) :
    altL (F (sym (cs.foldl Cls.union c)) :: T) =
      altL ((c :: cs).map (fun cl => F (.sym cl)) ++ T) := by
  induction cs generalizing c with
  | nil => rw [List.map_cons, List.map_nil, List.singleton_append, hF.map_symSmart]; rfl
  | cons d ds ih =>
    rw [show (d :: ds).foldl Cls.union c = ds.foldl Cls.union (c.union d) from rfl,
      ih (c.union d), List.map_cons, List.cons_append, hF.map_symSmart, hF.map_symUnion, alt2,
      altL_nest_canon (M := [F (sym c), F (sym d)]) (by
        rintro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hF.map_canon _ (isCanon_sym c)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hF.map_canon _ (isCanon_sym d)
          · simp at hx)]
    refine altL_mem_congr ?_
    intro y
    simp only [List.cons_append, List.nil_append, List.map_cons, List.mem_cons,
      hF.map_symSmart, List.mem_append, List.mem_map]

/-- Rebuilding a member list commutes with an `AltHom`. -/
theorem altOfList (hF : AltHom F) {L : List RE} (h : ∀ x ∈ L, IsCanon x) :
    F (Redgrep.altOfList L) = altL (L.map F) := by
  induction L with
  | nil => rw [show Redgrep.altOfList ([] : List RE) = .nil from rfl, hF.map_nil, List.map_nil,
      altL_nil_eq]
  | cons x xs ih =>
    rw [Smart.altOfList_cons]
    split
    · rename_i hxs
      subst hxs
      rw [List.map_cons, List.map_nil, altL_singleton (hF.map_canon x (h x (by simp)))]
    · rw [hF.map_alt, ih (fun y hy => h y (by simp [hy])), alt2,
        altL_swap2 (F x) (Redgrep.altL (xs.map F)) [],
        altL_nest_canon (M := xs.map F) (by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
          exact hF.map_canon w (h w (by simp [hw])))]
      exact altL_mem_congr (by intro y; simp only [List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.map_cons]; tauto)

/-- The merged block of `sym` members may be traded for the raw members. -/
theorem merged_rest (hF : AltHom F) {f : List RE} (hcanon : ∀ x ∈ f, IsCanon x) :
    Redgrep.altL ((altMerged (f.filter isSym) ++ f.filter (not ∘ isSym)).map F) =
      Redgrep.altL (f.map F) := by
  rw [List.map_append]
  rcases altMerged_cases (f.filter isSym) with h0 | ⟨cl, h0, hne⟩
  · -- no `sym` members survive the merge; under canonicity there are none at all
    have hsc : symClasses (f.filter isSym) = [] := by
      cases hsc : symClasses (f.filter isSym) with
      | nil => rfl
      | cons d ds =>
        exfalso
        have hd : RE.sym d ∈ f.filter isSym := mem_symClasses.mp (by rw [hsc]; simp)
        have := altMerged_eq_singleton hsc
          (sym_foldl_ne_nil (hcanon _ (List.mem_of_mem_filter hd)))
        rw [h0] at this
        simp at this
    have hnosym : ∀ x ∈ f, isSym x = false := by
      intro x hx
      cases hs : isSym x with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨c, rfl⟩ := isSym_iff.mp hs
        have : c ∈ symClasses (f.filter isSym) :=
          mem_symClasses.mpr (List.mem_filter.mpr ⟨hx, hs⟩)
        rw [hsc] at this
        simp at this
    rw [h0, List.map_nil, List.nil_append]
    refine altL_mem_congr ?_
    intro y
    simp only [List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, List.mem_of_mem_filter hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, List.mem_filter.mpr ⟨hx, by simp [hnosym x hx]⟩, rfl⟩
  · obtain ⟨c, cs, hcs⟩ : ∃ c cs, symClasses (f.filter isSym) = c :: cs := by
      cases hsc : symClasses (f.filter isSym) with
      | nil => rw [altMerged_eq_nil hsc] at h0; simp at h0
      | cons c cs => exact ⟨c, cs, rfl⟩
    have hcmem : RE.sym c ∈ f.filter isSym := mem_symClasses.mp (by rw [hcs]; simp)
    have hmerged : altMerged (f.filter isSym) = [sym (cs.foldl Cls.union c)] :=
      altMerged_eq_singleton hcs (sym_foldl_ne_nil (hcanon _ (List.mem_of_mem_filter hcmem)))
    rw [hmerged, List.map_cons, List.map_nil, List.singleton_append,
      hF.merge c cs ((f.filter (not ∘ isSym)).map F)]
    refine altL_mem_congr ?_
    intro y
    simp only [List.mem_append, List.mem_map, List.mem_cons]
    constructor
    · rintro (⟨d, hd, rfl⟩ | ⟨x, hx, rfl⟩)
      · refine ⟨RE.sym d, ?_, rfl⟩
        have : d ∈ symClasses (f.filter isSym) := by rw [hcs]; exact List.mem_cons.mpr hd
        exact List.mem_of_mem_filter (mem_symClasses.mp this)
      · exact ⟨x, List.mem_of_mem_filter hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      cases hs : isSym x with
      | true =>
        obtain ⟨d, rfl⟩ := isSym_iff.mp hs
        refine Or.inl ⟨d, ?_, rfl⟩
        have : d ∈ symClasses (f.filter isSym) :=
          mem_symClasses.mpr (List.mem_filter.mpr ⟨hx, hs⟩)
        rw [hcs] at this
        exact List.mem_cons.mp this
      | false => exact Or.inr ⟨x, List.mem_filter.mpr ⟨hx, by simp [hs]⟩, rfl⟩

/-- **An `AltHom` commutes with the smart n-ary union.** -/
theorem altL (hF : AltHom F) {rs : List RE} (h : ∀ x ∈ rs, IsCanon x) :
    F (Redgrep.altL rs) = Redgrep.altL (rs.map F) := by
  have hcanon : ∀ x ∈ altFlat rs, IsCanon x := by
    intro x hx
    obtain ⟨r, hr, hxr⟩ := mem_altFlat.mp hx
    exact isCanon_of_mem_altToList (h r hr) _ hxr
  by_cases htop : top ∈ altFlat rs
  · obtain ⟨r, hr, hxr⟩ := mem_altFlat.mp htop
    have hrtop : r = top := eq_top_of_mem_altToList (h r hr) hxr
    subst hrtop
    rw [Redgrep.altL_eq' rs, if_pos htop, hF.map_top, Redgrep.altL_eq' (rs.map F),
      if_pos (mem_altFlat.mpr ⟨top, by rw [← hF.map_top]; exact List.mem_map_of_mem hr,
        by rw [altToList_top]; simp⟩)]
  · have hbody : ∀ x ∈ sortDedup (altMerged ((altFlat rs).filter isSym) ++
        (altFlat rs).filter (not ∘ isSym)), IsCanon x := by
      intro x hx
      rw [mem_sortDedup, List.mem_append] at hx
      rcases hx with hx | hx
      · rcases altMerged_cases ((altFlat rs).filter isSym) with h0 | ⟨cl, h0, -⟩
        · rw [h0] at hx; simp at hx
        · rw [h0, List.mem_singleton] at hx
          subst hx
          exact isCanon_sym cl
      · exact hcanon x (List.mem_of_mem_filter hx)
    have hfl := hF.flat_list h []
    simp only [List.append_nil] at hfl
    rw [Redgrep.altL_eq' rs, if_neg htop, hF.altOfList hbody, ← hfl,
      show Redgrep.altL ((sortDedup (altMerged ((altFlat rs).filter isSym) ++
          (altFlat rs).filter (not ∘ isSym))).map F) =
        Redgrep.altL ((altMerged ((altFlat rs).filter isSym) ++
          (altFlat rs).filter (not ∘ isSym)).map F) from
        altL_mem_congr (by intro y; simp only [List.mem_map, mem_sortDedup])]
    exact hF.merged_rest hcanon

end AltHom

end Redgrep

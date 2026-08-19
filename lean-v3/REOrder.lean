import Core
import Mathlib

/-!
# Lawfulness of the total order on `RE`, and the `sortDedup` normal form

`Core.lean` defines the comparator `RE.cmp` (constructor tag first, then
fields lexicographically) and leaves its "order-theoretic laws" as later work.
They are needed by the ACI layer: `sortDedup = dedup ∘ mergeSort` is a normal
form for finite *sets* of regexes only if `RE.le` is a lawful linear order.

This file proves the comparator laws for `Cls.cmp`, `RE.cmpHomEntry`,
`RE.cmpHom` and `RE.cmp`, and derives the `sortDedup` API:

* `mem_sortDedup`, `sortDedup_nodup`, `sortDedup_sorted`;
* `sortDedup_eq_of_mem_iff` — `sortDedup` only sees the *set* of members;
* `sortDedup_eq_self` — it fixes sorted duplicate-free lists.

The same normal-form facts are proved for the hom association lists
normalised inside `invHom_` (`homNorm`).
-/

namespace Redgrep

/-! ### `Cls.cmp` -/

theorem sort_inj {a b : Finset Char} (h : a.sort (· ≤ ·) = b.sort (· ≤ ·)) : a = b := by
  rw [← Finset.sort_toFinset a (· ≤ ·), ← Finset.sort_toFinset b (· ≤ ·), h]

theorem Cls.cmp_eq_iff (a b : Cls) : Cls.cmp a b = .eq ↔ a = b := by
  cases a <;> cases b <;> simp [Cls.cmp] <;>
    exact ⟨fun h => sort_inj h, fun h => by rw [h]⟩

theorem Cls.cmp_swap (a b : Cls) : Cls.cmp a b = (Cls.cmp b a).swap := by
  cases a <;> cases b <;> simp [Cls.cmp] <;> exact Std.OrientedCmp.eq_swap

theorem Cls.cmp_trans {a b c : Cls} :
    Cls.cmp a b = .lt → Cls.cmp b c = .lt → Cls.cmp a c = .lt := by
  cases a <;> cases b <;> cases c <;> simp [Cls.cmp] <;> intro h1 h2 <;>
    exact Std.TransCmp.lt_trans h1 h2

namespace RE

/-! ### `RE.cmpHomEntry` and `RE.cmpHom` -/

theorem cmpHomEntry_eq_iff (a b : Char × List Char) : cmpHomEntry a b = .eq ↔ a = b := by
  simp [cmpHomEntry, Ordering.then_eq_eq, Prod.ext_iff]

theorem cmpHomEntry_swap (a b : Char × List Char) :
    cmpHomEntry a b = (cmpHomEntry b a).swap := by
  simp only [cmpHomEntry, Ordering.swap_then]
  rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := a.1) (b := b.1),
      Std.OrientedCmp.eq_swap (cmp := compare) (a := a.2) (b := b.2)]

theorem cmpHomEntry_trans {a b c : Char × List Char} :
    cmpHomEntry a b = .lt → cmpHomEntry b c = .lt → cmpHomEntry a c = .lt := by
  simp only [cmpHomEntry, Ordering.then_eq_lt]
  rintro (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
  · exact Or.inl (Std.TransCmp.lt_trans h1 h2)
  · rw [Std.compare_eq_iff_eq.mp h2] at h1; exact Or.inl h1
  · rw [Std.compare_eq_iff_eq.mp h1]; exact Or.inl h2
  · rw [Std.compare_eq_iff_eq.mp h1]
    exact Or.inr ⟨h2, Std.TransCmp.lt_trans h1' h2'⟩

theorem cmpHom_eq_iff (a b : List (Char × List Char)) : cmpHom a b = .eq ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [cmpHom]
  | cons x xs ih =>
    cases b with
    | nil => simp [cmpHom]
    | cons y ys => simp [cmpHom, Ordering.then_eq_eq, ih, cmpHomEntry_eq_iff]

theorem cmpHom_swap (a b : List (Char × List Char)) : cmpHom a b = (cmpHom b a).swap := by
  induction a generalizing b with
  | nil => cases b <;> simp [cmpHom]
  | cons x xs ih =>
    cases b with
    | nil => simp [cmpHom]
    | cons y ys => rw [cmpHom, cmpHom, Ordering.swap_then, ← ih, ← cmpHomEntry_swap]

theorem cmpHom_trans {a b c : List (Char × List Char)} :
    cmpHom a b = .lt → cmpHom b c = .lt → cmpHom a c = .lt := by
  induction a generalizing b c with
  | nil => cases b <;> cases c <;> simp [cmpHom]
  | cons x xs ih =>
    cases b with
    | nil => simp [cmpHom]
    | cons y ys =>
      cases c with
      | nil => simp [cmpHom]
      | cons z zs =>
        simp only [cmpHom, Ordering.then_eq_lt]
        rintro (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
        · exact Or.inl (cmpHomEntry_trans h1 h2)
        · rw [(cmpHomEntry_eq_iff _ _).mp h2] at h1; exact Or.inl h1
        · rw [(cmpHomEntry_eq_iff _ _).mp h1]; exact Or.inl h2
        · rw [(cmpHomEntry_eq_iff _ _).mp h1]
          exact Or.inr ⟨h2, ih h1' h2'⟩

/-! ### `RE.cmp` -/

theorem cmp_eq_iff (a b : RE) : cmp a b = .eq ↔ a = b := by
  induction a generalizing b with
  | sym c => cases b <;> simp [cmp, Cls.cmp_eq_iff, RE.ctorIdx]
  | alt x y ihx ihy => cases b <;> simp [cmp, Ordering.then_eq_eq, ihx, ihy, RE.ctorIdx]
  | cut x y ihx ihy => cases b <;> simp [cmp, Ordering.then_eq_eq, ihx, ihy, RE.ctorIdx]
  | seq x y ihx ihy => cases b <;> simp [cmp, Ordering.then_eq_eq, ihx, ihy, RE.ctorIdx]
  | rep x ihx => cases b <;> simp [cmp, ihx, RE.ctorIdx]
  | not x ihx => cases b <;> simp [cmp, ihx, RE.ctorIdx]
  | invHom h x ihx =>
    cases b <;> simp [cmp, Ordering.then_eq_eq, ihx, cmpHom_eq_iff, RE.ctorIdx]
  | eps => cases b <;> simp [cmp, RE.ctorIdx]
  | nil => cases b <;> simp [cmp, RE.ctorIdx]

theorem cmp_swap (a b : RE) : cmp a b = (cmp b a).swap := by
  induction a generalizing b with
  | sym c =>
    cases b <;> simp only [cmp, RE.ctorIdx] <;>
      first
        | exact Cls.cmp_swap _ _
        | exact Std.OrientedCmp.eq_swap
  | alt x y ihx ihy =>
    cases b <;> simp [cmp, RE.ctorIdx, Ordering.swap_then, ← ihx, ← ihy] <;>
      exact Std.OrientedCmp.eq_swap
  | cut x y ihx ihy =>
    cases b <;> simp [cmp, RE.ctorIdx, Ordering.swap_then, ← ihx, ← ihy] <;>
      exact Std.OrientedCmp.eq_swap
  | seq x y ihx ihy =>
    cases b <;> simp [cmp, RE.ctorIdx, Ordering.swap_then, ← ihx, ← ihy] <;>
      exact Std.OrientedCmp.eq_swap
  | rep x ihx => cases b <;> simp [cmp, RE.ctorIdx, ← ihx] <;> exact Std.OrientedCmp.eq_swap
  | not x ihx => cases b <;> simp [cmp, RE.ctorIdx, ← ihx] <;> exact Std.OrientedCmp.eq_swap
  | invHom h x ihx =>
    cases b <;>
      simp [cmp, RE.ctorIdx, Ordering.swap_then, ← ihx, ← cmpHom_swap] <;>
      exact Std.OrientedCmp.eq_swap
  | eps => cases b <;> simp [cmp, RE.ctorIdx] <;> exact Std.OrientedCmp.eq_swap
  | nil => cases b <;> simp [cmp, RE.ctorIdx] <;> exact Std.OrientedCmp.eq_swap

/-- The lexicographic step used in the `alt`/`cut`/`seq` cases of
`RE.cmp_trans`. -/
private theorem lexStep {x1 x2 x3 y1 y2 y3 : RE}
    (ihx : ∀ b c, cmp x1 b = .lt → cmp b c = .lt → cmp x1 c = .lt)
    (ihy : ∀ b c, cmp y1 b = .lt → cmp b c = .lt → cmp y1 c = .lt)
    (h1 : (cmp x1 x2).then (cmp y1 y2) = .lt)
    (h2 : (cmp x2 x3).then (cmp y2 y3) = .lt) :
    (cmp x1 x3).then (cmp y1 y3) = .lt := by
  rw [Ordering.then_eq_lt] at h1 h2 ⊢
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact Or.inl (ihx _ _ h1 h2)
  · rw [← (cmp_eq_iff _ _).mp e2]; exact Or.inl h1
  · rw [(cmp_eq_iff _ _).mp e1]; exact Or.inl h2
  · rw [(cmp_eq_iff _ _).mp e1]
    exact Or.inr ⟨e2, ihy _ _ h1 h2⟩

/-- Mismatched constructor tags: the comparator is the tag comparison. -/
theorem cmp_of_ctorIdx_ne {a b : RE} (h : a.ctorIdx ≠ b.ctorIdx) :
    cmp a b = compare a.ctorIdx b.ctorIdx := by
  cases a <;> cases b <;> simp_all [cmp, RE.ctorIdx]

theorem ctorIdx_le_of_cmp_lt {a b : RE} (h : cmp a b = .lt) : a.ctorIdx ≤ b.ctorIdx := by
  by_cases e : a.ctorIdx = b.ctorIdx
  · omega
  · rw [cmp_of_ctorIdx_ne e, Nat.compare_eq_lt] at h; omega

private theorem trans_of_ctorIdx_ne {a b c : RE} (h1 : cmp a b = .lt) (h2 : cmp b c = .lt)
    (h : a.ctorIdx ≠ b.ctorIdx ∨ b.ctorIdx ≠ c.ctorIdx) : cmp a c = .lt := by
  have hab := ctorIdx_le_of_cmp_lt h1
  have hbc := ctorIdx_le_of_cmp_lt h2
  have hlt : a.ctorIdx < c.ctorIdx := by rcases h with h | h <;> omega
  rw [cmp_of_ctorIdx_ne (by omega), Nat.compare_eq_lt]
  exact hlt

private theorem eq_sym_of_ctorIdx {b : RE} (h : b.ctorIdx = 0) : ∃ cl, b = .sym cl := by
  cases b <;> simp_all [RE.ctorIdx]

private theorem eq_alt_of_ctorIdx {b : RE} (h : b.ctorIdx = 1) : ∃ x y, b = .alt x y := by
  cases b <;> simp_all [RE.ctorIdx]

private theorem eq_cut_of_ctorIdx {b : RE} (h : b.ctorIdx = 2) : ∃ x y, b = .cut x y := by
  cases b <;> simp_all [RE.ctorIdx]

private theorem eq_seq_of_ctorIdx {b : RE} (h : b.ctorIdx = 3) : ∃ x y, b = .seq x y := by
  cases b <;> simp_all [RE.ctorIdx]

private theorem eq_rep_of_ctorIdx {b : RE} (h : b.ctorIdx = 4) : ∃ x, b = .rep x := by
  cases b <;> simp_all [RE.ctorIdx]

private theorem eq_not_of_ctorIdx {b : RE} (h : b.ctorIdx = 5) : ∃ x, b = .not x := by
  cases b <;> simp_all [RE.ctorIdx]

private theorem eq_invHom_of_ctorIdx {b : RE} (h : b.ctorIdx = 6) :
    ∃ hm x, b = .invHom hm x := by
  cases b <;> simp_all [RE.ctorIdx]

theorem cmp_trans : ∀ {a b c : RE}, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt := by
  intro a
  induction a with
  | sym cl =>
    intro b c h1 h2
    by_cases hab : b.ctorIdx = 0
    · by_cases hbc : c.ctorIdx = 0
      · obtain ⟨cl2, rfl⟩ := eq_sym_of_ctorIdx hab
        obtain ⟨cl3, rfl⟩ := eq_sym_of_ctorIdx hbc
        exact Cls.cmp_trans h1 h2
      · exact trans_of_ctorIdx_ne h1 h2 (Or.inr (by omega))
    · exact trans_of_ctorIdx_ne h1 h2 (Or.inl (by simpa [RE.ctorIdx] using fun hx => hab hx.symm))
  | alt x y ihx ihy =>
    intro b c h1 h2
    by_cases hab : b.ctorIdx = 1
    · by_cases hbc : c.ctorIdx = 1
      · obtain ⟨x2, y2, rfl⟩ := eq_alt_of_ctorIdx hab
        obtain ⟨x3, y3, rfl⟩ := eq_alt_of_ctorIdx hbc
        exact lexStep (fun _ _ => ihx) (fun _ _ => ihy) h1 h2
      · exact trans_of_ctorIdx_ne h1 h2 (Or.inr (by omega))
    · exact trans_of_ctorIdx_ne h1 h2 (Or.inl (by simpa [RE.ctorIdx] using fun hx => hab hx.symm))
  | cut x y ihx ihy =>
    intro b c h1 h2
    by_cases hab : b.ctorIdx = 2
    · by_cases hbc : c.ctorIdx = 2
      · obtain ⟨x2, y2, rfl⟩ := eq_cut_of_ctorIdx hab
        obtain ⟨x3, y3, rfl⟩ := eq_cut_of_ctorIdx hbc
        exact lexStep (fun _ _ => ihx) (fun _ _ => ihy) h1 h2
      · exact trans_of_ctorIdx_ne h1 h2 (Or.inr (by omega))
    · exact trans_of_ctorIdx_ne h1 h2 (Or.inl (by simpa [RE.ctorIdx] using fun hx => hab hx.symm))
  | seq x y ihx ihy =>
    intro b c h1 h2
    by_cases hab : b.ctorIdx = 3
    · by_cases hbc : c.ctorIdx = 3
      · obtain ⟨x2, y2, rfl⟩ := eq_seq_of_ctorIdx hab
        obtain ⟨x3, y3, rfl⟩ := eq_seq_of_ctorIdx hbc
        exact lexStep (fun _ _ => ihx) (fun _ _ => ihy) h1 h2
      · exact trans_of_ctorIdx_ne h1 h2 (Or.inr (by omega))
    · exact trans_of_ctorIdx_ne h1 h2 (Or.inl (by simpa [RE.ctorIdx] using fun hx => hab hx.symm))
  | rep x ihx =>
    intro b c h1 h2
    by_cases hab : b.ctorIdx = 4
    · by_cases hbc : c.ctorIdx = 4
      · obtain ⟨x2, rfl⟩ := eq_rep_of_ctorIdx hab
        obtain ⟨x3, rfl⟩ := eq_rep_of_ctorIdx hbc
        exact ihx h1 h2
      · exact trans_of_ctorIdx_ne h1 h2 (Or.inr (by omega))
    · exact trans_of_ctorIdx_ne h1 h2 (Or.inl (by simpa [RE.ctorIdx] using fun hx => hab hx.symm))
  | not x ihx =>
    intro b c h1 h2
    by_cases hab : b.ctorIdx = 5
    · by_cases hbc : c.ctorIdx = 5
      · obtain ⟨x2, rfl⟩ := eq_not_of_ctorIdx hab
        obtain ⟨x3, rfl⟩ := eq_not_of_ctorIdx hbc
        exact ihx h1 h2
      · exact trans_of_ctorIdx_ne h1 h2 (Or.inr (by omega))
    · exact trans_of_ctorIdx_ne h1 h2 (Or.inl (by simpa [RE.ctorIdx] using fun hx => hab hx.symm))
  | invHom hm x ihx =>
    intro b c h1 h2
    by_cases hab : b.ctorIdx = 6
    · by_cases hbc : c.ctorIdx = 6
      · obtain ⟨hm2, x2, rfl⟩ := eq_invHom_of_ctorIdx hab
        obtain ⟨hm3, x3, rfl⟩ := eq_invHom_of_ctorIdx hbc
        show (cmpHom hm hm3).then (cmp x x3) = .lt
        rw [show cmp (RE.invHom hm x) (RE.invHom hm2 x2)
              = (cmpHom hm hm2).then (cmp x x2) from rfl] at h1
        rw [show cmp (RE.invHom hm2 x2) (RE.invHom hm3 x3)
              = (cmpHom hm2 hm3).then (cmp x2 x3) from rfl] at h2
        rw [Ordering.then_eq_lt] at h1 h2 ⊢
        rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with hb | ⟨e2, hb⟩
        · exact Or.inl (cmpHom_trans h1 hb)
        · rw [← (cmpHom_eq_iff _ _).mp e2]; exact Or.inl h1
        · rw [(cmpHom_eq_iff _ _).mp e1]; exact Or.inl hb
        · rw [(cmpHom_eq_iff _ _).mp e1]
          exact Or.inr ⟨e2, ihx h1 hb⟩
      · exact trans_of_ctorIdx_ne h1 h2 (Or.inr (by omega))
    · exact trans_of_ctorIdx_ne h1 h2 (Or.inl (by simpa [RE.ctorIdx] using fun hx => hab hx.symm))
  | eps =>
    intro b c h1 h2
    by_cases hab : b.ctorIdx = 7
    · by_cases hbc : c.ctorIdx = 7
      · obtain rfl : b = RE.eps := by cases b <;> simp_all [RE.ctorIdx]
        obtain rfl : c = RE.eps := by cases c <;> simp_all [RE.ctorIdx]
        exact absurd h2 (by decide)
      · exact trans_of_ctorIdx_ne h1 h2 (Or.inr (by omega))
    · exact trans_of_ctorIdx_ne h1 h2 (Or.inl (by simpa [RE.ctorIdx] using fun hx => hab hx.symm))
  | nil =>
    intro b c h1 h2
    by_cases hab : b.ctorIdx = 8
    · by_cases hbc : c.ctorIdx = 8
      · obtain rfl : b = RE.nil := by cases b <;> simp_all [RE.ctorIdx]
        obtain rfl : c = RE.nil := by cases c <;> simp_all [RE.ctorIdx]
        exact absurd h2 (by decide)
      · exact trans_of_ctorIdx_ne h1 h2 (Or.inr (by omega))
    · exact trans_of_ctorIdx_ne h1 h2 (Or.inl (by simpa [RE.ctorIdx] using fun hx => hab hx.symm))

/-! ### The boolean order `RE.le` -/

@[simp] theorem cmp_self (a : RE) : cmp a a = .eq := (cmp_eq_iff a a).mpr rfl

theorem le_refl (a : RE) : le a a = true := by simp [le]

theorem le_trans {a b c : RE} (h1 : le a b = true) (h2 : le b c = true) : le a c = true := by
  simp only [le] at h1 h2 ⊢
  rcases hab : cmp a b with _ | _ | _ <;> rw [hab] at h1 <;>
    rcases hbc : cmp b c with _ | _ | _ <;> rw [hbc] at h2 <;>
    first
      | exact absurd h1 (by decide)
      | exact absurd h2 (by decide)
      | (rw [cmp_trans hab hbc]; rfl)
      | (rw [← (cmp_eq_iff _ _).mp hbc, hab]; rfl)
      | (rw [(cmp_eq_iff _ _).mp hab, hbc]; rfl)

theorem le_total (a b : RE) : (le a b || le b a) = true := by
  simp only [le]
  rcases h : cmp a b with _ | _ | _
  · rfl
  · rfl
  · rw [cmp_swap b a, h]; rfl

theorem le_antisymm {a b : RE} (h1 : le a b = true) (h2 : le b a = true) : a = b := by
  simp only [le] at h1 h2
  rw [cmp_swap b a] at h2
  rcases h : cmp a b with _ | _ | _ <;> rw [h] at h1 h2 <;>
    first
      | exact absurd h1 (by decide)
      | exact absurd h2 (by decide)
      | exact (cmp_eq_iff _ _).mp h

end RE

/-! ### `sortDedup` -/

@[simp] theorem mem_sortDedup {x : RE} {l : List RE} : x ∈ sortDedup l ↔ x ∈ l := by
  simp only [sortDedup, List.mem_dedup]
  exact (List.mergeSort_perm l RE.le).mem_iff

theorem sortDedup_nodup (l : List RE) : (sortDedup l).Nodup := List.nodup_dedup _

theorem sortDedup_sorted (l : List RE) :
    (sortDedup l).Pairwise (fun a b => RE.le a b = true) := by
  have hs : (l.mergeSort RE.le).Pairwise (fun a b => RE.le a b = true) :=
    List.pairwise_mergeSort (le := RE.le) (fun _ _ _ h1 h2 => RE.le_trans h1 h2) RE.le_total l
  exact hs.sublist (List.dedup_sublist _)

/-- A sorted, duplicate-free list is its own `sortDedup`. -/
theorem sortDedup_eq_self {l : List RE} (hs : l.Pairwise (fun a b => RE.le a b = true))
    (hn : l.Nodup) : sortDedup l = l := by
  refine List.Perm.eq_of_pairwise (le := fun a b => RE.le a b = true)
    (fun a b _ _ hab hba => RE.le_antisymm hab hba) (sortDedup_sorted l) hs ?_
  refine (List.perm_ext_iff_of_nodup (sortDedup_nodup l) hn).mpr fun x => ?_
  exact mem_sortDedup

/-- `sortDedup` depends only on the set of members: it is a normal form for
finite sets of regexes. -/
theorem sortDedup_eq_of_mem_iff {l l' : List RE} (h : ∀ x, x ∈ l ↔ x ∈ l') :
    sortDedup l = sortDedup l' := by
  refine List.Perm.eq_of_pairwise (le := fun a b => RE.le a b = true)
    (fun a b _ _ hab hba => RE.le_antisymm hab hba) (sortDedup_sorted l) (sortDedup_sorted l') ?_
  refine (List.perm_ext_iff_of_nodup (sortDedup_nodup l) (sortDedup_nodup l')).mpr fun x => ?_
  simp only [mem_sortDedup]
  exact h x

@[simp] theorem sortDedup_idem (l : List RE) : sortDedup (sortDedup l) = sortDedup l :=
  sortDedup_eq_self (sortDedup_sorted l) (sortDedup_nodup l)

/-! ### The same normal form for hom association lists -/

/-- The hom normal form computed inside `invHom_`. -/
def homNorm (h : List (Char × List Char)) : List (Char × List Char) :=
  ((h.filter fun p => p.2 != [p.1]).mergeSort
    fun a b => (RE.cmpHomEntry a b).isLE).dedup

theorem invHom_eq_ite (h : List (Char × List Char)) (r : RE) :
    invHom_ h r =
      if r = .nil then .nil else if homNorm h = [] then r else .invHom (homNorm h) r := by
  cases r <;> simp [invHom_, homNorm]

@[simp] theorem mem_homNorm {p : Char × List Char} {h : List (Char × List Char)} :
    p ∈ homNorm h ↔ p ∈ h ∧ p.2 ≠ [p.1] := by
  simp only [homNorm, List.mem_dedup]
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filter]
  simp

theorem homNorm_nodup (h : List (Char × List Char)) : (homNorm h).Nodup := List.nodup_dedup _

theorem homEntry_le_trans {a b c : Char × List Char}
    (h1 : (RE.cmpHomEntry a b).isLE = true) (h2 : (RE.cmpHomEntry b c).isLE = true) :
    (RE.cmpHomEntry a c).isLE = true := by
  rcases hab : RE.cmpHomEntry a b with _ | _ | _ <;> rw [hab] at h1 <;>
    rcases hbc : RE.cmpHomEntry b c with _ | _ | _ <;> rw [hbc] at h2 <;>
    first
      | exact absurd h1 (by decide)
      | exact absurd h2 (by decide)
      | (rw [RE.cmpHomEntry_trans hab hbc]; rfl)
      | (rw [← (RE.cmpHomEntry_eq_iff _ _).mp hbc, hab]; rfl)
      | (rw [(RE.cmpHomEntry_eq_iff _ _).mp hab, hbc]; rfl)

theorem homEntry_le_total (a b : Char × List Char) :
    ((RE.cmpHomEntry a b).isLE || (RE.cmpHomEntry b a).isLE) = true := by
  rcases h : RE.cmpHomEntry a b with _ | _ | _
  · rfl
  · rfl
  · rw [RE.cmpHomEntry_swap b a, h]; rfl

theorem homEntry_le_antisymm {a b : Char × List Char} (h1 : (RE.cmpHomEntry a b).isLE = true)
    (h2 : (RE.cmpHomEntry b a).isLE = true) : a = b := by
  rw [RE.cmpHomEntry_swap b a] at h2
  rcases h : RE.cmpHomEntry a b with _ | _ | _ <;> rw [h] at h1 h2 <;>
    first
      | exact absurd h1 (by decide)
      | exact absurd h2 (by decide)
      | exact (RE.cmpHomEntry_eq_iff _ _).mp h

theorem homNorm_sorted (h : List (Char × List Char)) :
    (homNorm h).Pairwise (fun a b => (RE.cmpHomEntry a b).isLE = true) := by
  have hs : (((h.filter fun p => p.2 != [p.1]).mergeSort
      fun a b => (RE.cmpHomEntry a b).isLE)).Pairwise
      (fun a b => (RE.cmpHomEntry a b).isLE = true) :=
    List.pairwise_mergeSort (le := fun a b => (RE.cmpHomEntry a b).isLE)
      (fun _ _ _ h1 h2 => homEntry_le_trans h1 h2) homEntry_le_total _
  exact hs.sublist (List.dedup_sublist _)

@[simp] theorem homNorm_idem (h : List (Char × List Char)) : homNorm (homNorm h) = homNorm h := by
  refine List.Perm.eq_of_pairwise (le := fun a b => (RE.cmpHomEntry a b).isLE = true)
    (fun a b _ _ hab hba => homEntry_le_antisymm hab hba) (homNorm_sorted _) (homNorm_sorted h) ?_
  refine (List.perm_ext_iff_of_nodup (homNorm_nodup _) (homNorm_nodup h)).mpr fun x => ?_
  simp only [mem_homNorm]
  tauto

end Redgrep

import ACIDefs

/-!
# The remaining constructors of the ACI layer

`seq2`, `rep_`, `not_`, `invHom_`: each lands in `IsCanon`, and each
fixes the canonical terms of its own shape.  Concatenation is the only case
with a flattening layer (`seqToList`/`seqOfList`), and it is simpler than the
union and intersection cases because there is no sorting, deduplication or
class merging: a canonical concatenation is just a right-nested chain of
non-`eps`, non-`nil`, non-`seq` factors.
-/

namespace Redgrep

/-! ### Flattening and rebuilding concatenations -/

theorem seqToList_eq_singleton {r : RE} (hne : r ≠ .eps) (hns : NotSeq r) :
    seqToList r = [r] := by
  cases r <;> simp_all [NotSeq]

/-- Members of the flattened concatenation of a canonical term are canonical. -/
theorem isCanon_of_mem_seqToList {r : RE} (h : IsCanon r) :
    ∀ x ∈ seqToList r, IsCanon x := by
  induction r with
  | seq a b iha ihb =>
    obtain ⟨ha, hb, -, -, -, -, -⟩ := isCanon_seq_iff.mp h
    intro x hx
    rw [Smart.seqToList_seq, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha ha x hx
    · exact ihb hb x hx
  | eps => intro x hx; simp at hx
  | _ =>
    intro x hx
    rw [seqToList_eq_singleton (by simp) (by trivial), List.mem_singleton] at hx
    subst hx
    exact h

theorem mem_seqToList_notSeq {r : RE} : ∀ x ∈ seqToList r, NotSeq x ∧ x ≠ .eps := by
  induction r with
  | seq a b iha ihb =>
    intro x hx
    rw [Smart.seqToList_seq, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha x hx
    · exact ihb x hx
  | eps => intro x hx; simp at hx
  | _ =>
    intro x hx
    rw [seqToList_eq_singleton (by simp) (by trivial), List.mem_singleton] at hx
    subst hx
    exact ⟨by trivial, by simp⟩

theorem mem_seqToList_ne_nil {r : RE} (h : IsCanon r) (hnil : r ≠ .nil) :
    ∀ x ∈ seqToList r, x ≠ .nil := by
  induction r with
  | seq a b iha ihb =>
    obtain ⟨ha, hb, -, -, hanil, -, hbnil⟩ := isCanon_seq_iff.mp h
    intro x hx
    rw [Smart.seqToList_seq, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha ha hanil x hx
    · exact ihb hb hbnil x hx
  | eps => intro x hx; simp at hx
  | nil => exact absurd rfl hnil
  | _ =>
    intro x hx
    rw [seqToList_eq_singleton (by simp) (by trivial), List.mem_singleton] at hx
    subst hx
    simp

theorem seqToList_ne_nil {r : RE} (h : IsCanon r) (hne : r ≠ .eps) : seqToList r ≠ [] := by
  induction r with
  | seq a b iha _ =>
    obtain ⟨ha, -, -, hae, -⟩ := isCanon_seq_iff.mp h
    rw [Smart.seqToList_seq]
    simp only [ne_eq, List.append_eq_nil_iff, not_and]
    intro hc
    exact absurd hc (iha ha hae)
  | eps => exact absurd rfl hne
  | _ => rw [seqToList_eq_singleton hne (by trivial)]; simp

/-- Rebuilding a flattened concatenation recovers a canonical term. -/
theorem seqOfList_seqToList {r : RE} (h : IsCanon r) (heps : r ≠ .eps) :
    seqOfList (seqToList r) = r := by
  induction r with
  | seq a b iha ihb =>
    obtain ⟨ha, hb, hns, hae, -, hbe, -⟩ := isCanon_seq_iff.mp h
    rw [Smart.seqToList_seq, seqToList_eq_singleton hae hns, List.singleton_append]
    have hb' : seqToList b ≠ [] := seqToList_ne_nil hb hbe
    cases hlb : seqToList b with
    | nil => exact absurd hlb hb'
    | cons y ys => rw [Smart.seqOfList_cons, if_neg (by simp), ← hlb, ihb hb hbe]
  | eps => exact absurd rfl heps
  | _ => rw [seqToList_eq_singleton heps (by trivial)]; rfl

/-- Flattening a rebuilt concatenation list is the identity, provided its
members are not themselves concatenations (and not `eps`). -/
theorem seqToList_seqOfList {L : List RE}
    (h : ∀ x ∈ L, x ≠ .eps ∧ NotSeq x) : seqToList (seqOfList L) = L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hxe, hxs⟩ := h x (by simp)
    rw [Smart.seqOfList_cons]
    split
    · rename_i hnil
      subst hnil
      exact seqToList_eq_singleton hxe hxs
    · rw [Smart.seqToList_seq, seqToList_eq_singleton hxe hxs,
        ih fun y hy => h y (by simp [hy])]
      rfl

theorem seqOfList_ne_eps_nil {L : List RE} (hne : L ≠ [])
    (h : ∀ x ∈ L, x ≠ .eps ∧ x ≠ .nil) : seqOfList L ≠ .eps ∧ seqOfList L ≠ .nil := by
  cases L with
  | nil => exact absurd rfl hne
  | cons x xs =>
    rw [Smart.seqOfList_cons]
    split
    · exact h x (by simp)
    · exact ⟨by simp, by simp⟩

theorem isCanon_seqOfList {L : List RE}
    (hsh : ∀ x ∈ L, x ≠ .eps ∧ x ≠ .nil ∧ NotSeq x)
    (hc : ∀ x ∈ L, IsCanon x) : IsCanon (seqOfList L) := by
  induction L with
  | nil => exact isCanon_eps
  | cons x xs ih =>
    obtain ⟨hxe, hxn, hxs⟩ := hsh x (by simp)
    rw [Smart.seqOfList_cons]
    split
    · exact hc x (by simp)
    · rename_i hxsne
      have ihx := ih (fun y hy => hsh y (by simp [hy])) (fun y hy => hc y (by simp [hy]))
      obtain ⟨h1, h2⟩ := seqOfList_ne_eps_nil hxsne
        (fun y hy => ⟨(hsh y (by simp [hy])).1, (hsh y (by simp [hy])).2.1⟩)
      exact ⟨hc x (by simp), ihx, hxs, hxe, hxn, h1, h2⟩

/-! ### The smart constructors land in `IsCanon` -/

theorem isCanon_seq2 {x y : RE} (hx : IsCanon x) (hy : IsCanon y) : IsCanon (seq2 x y) := by
  rw [Smart.seq2_eq]
  split
  · exact isCanon_nil
  · rename_i hnil
    push_neg at hnil
    split
    · exact hy
    · split
      · exact hx
      · refine isCanon_seqOfList (fun z hz => ?_) (fun z hz => ?_) <;>
          rcases List.mem_append.mp hz with hz' | hz'
        · exact ⟨(mem_seqToList_notSeq z hz').2, mem_seqToList_ne_nil hx hnil.1 z hz',
            (mem_seqToList_notSeq z hz').1⟩
        · exact ⟨(mem_seqToList_notSeq z hz').2, mem_seqToList_ne_nil hy hnil.2 z hz',
            (mem_seqToList_notSeq z hz').1⟩
        · exact isCanon_of_mem_seqToList hx z hz'
        · exact isCanon_of_mem_seqToList hy z hz'

theorem isCanon_rep_ {x : RE} (hx : IsCanon x) : IsCanon (rep_ x) := by
  cases x with
  | nil => exact isCanon_eps
  | eps => exact isCanon_eps
  | rep r => exact hx
  | sym cl => exact ⟨hx, by simp, by simp, by simp [top], trivial⟩
  | alt a b => exact ⟨hx, by simp, by simp, by simp [top], trivial⟩
  | cut a b => exact ⟨hx, by simp, by simp, by simp [top], trivial⟩
  | seq a b => exact ⟨hx, by simp, by simp, by simp [top], trivial⟩
  | invHom h a => exact ⟨hx, by simp, by simp, by simp [top], trivial⟩
  | not a =>
    show IsCanon (if RE.not a = top then top else RE.rep (.not a))
    split
    · exact isCanon_top
    · exact ⟨hx, by simp, by simp, by assumption, trivial⟩

theorem isCanon_not_ {x : RE} (hx : IsCanon x) : IsCanon (not_ x) := by
  cases x with
  | not a => exact (isCanon_not_iff.mp hx).1
  | _ => exact ⟨hx, trivial⟩

theorem isCanon_invHom_ (h : List (Char × List Char)) {x : RE} (hx : IsCanon x) :
    IsCanon (invHom_ h x) := by
  rw [invHom_eq_ite]
  split
  · exact isCanon_nil
  · split
    · exact hx
    · exact ⟨hx, homNorm_idem h, by assumption, by assumption⟩

/-! ### Canonical terms are fixed points of their smart constructor -/

/-- A canonical concatenation is a fixed point of the smart concatenation. -/
theorem seq2_eq_self {a b : RE} (h : IsCanon (.seq a b)) : seq2 a b = .seq a b := by
  obtain ⟨-, hb, hns, hae, han, hbe, hbn⟩ := isCanon_seq_iff.mp h
  rw [Smart.seq2_eq, if_neg (by push_neg; exact ⟨han, hbn⟩), if_neg hae, if_neg hbe,
    seqToList_eq_singleton hae hns, List.singleton_append]
  have hb' : seqToList b ≠ [] := seqToList_ne_nil hb hbe
  cases hlb : seqToList b with
  | nil => exact absurd hlb hb'
  | cons y ys => rw [Smart.seqOfList_cons, if_neg (by simp), ← hlb, seqOfList_seqToList hb hbe]

/-- A canonical star is a fixed point of the smart star. -/
theorem rep_eq_self {r : RE} (h : IsCanon (.rep r)) : rep_ r = .rep r := by
  obtain ⟨-, hnil, heps, htop, hrep⟩ := isCanon_rep_iff.mp h
  cases r with
  | nil => exact absurd rfl hnil
  | eps => exact absurd rfl heps
  | rep s => exact absurd hrep (by simp)
  | not s =>
    show (if RE.not s = top then top else RE.rep (.not s)) = _
    rw [if_neg htop]
  | _ => rfl

/-- A canonical complement is a fixed point of the smart complement. -/
theorem not_eq_self {r : RE} (h : IsCanon (.not r)) : not_ r = .not r := by
  obtain ⟨-, hnot⟩ := isCanon_not_iff.mp h
  cases r <;> simp_all [not_, NotNot]

/-- A canonical inverse homomorphism is a fixed point of the smart one. -/
theorem invHom_eq_self {hh : List (Char × List Char)} {r : RE}
    (h : IsCanon (.invHom hh r)) : invHom_ hh r = .invHom hh r := by
  obtain ⟨-, hnorm, hne, hrnil⟩ := isCanon_invHom_iff.mp h
  rw [invHom_eq_ite, if_neg hrnil, hnorm, if_neg hne]

end Redgrep

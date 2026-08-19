import DerivCanon

/-!
# Bounded character classes

`altL` merges the `sym` members of a union by folding `Cls.union` over their
classes, and `cutL` does the same with `Cls.inter`, so the set of `sym` states
a regex can reach is closed under both operations.  The point of this file is
that this closure is **finite**: every one of `Cls.union`, `Cls.inter`,
`Cls.norm` builds its result finset out of `∪`, `∩` and `\` of the operands,
so all of them stay inside the powerset of a fixed finset `U`.

`ClsOK U` is that bound, and `symSet U` is the resulting (finite) set of
smart `sym` states.
-/

namespace Redgrep

/-- The underlying finset of a class is contained in `U`. -/
def ClsOK (U : Finset Char) : Cls → Prop
  | .pos s => s ⊆ U
  | .neg s => s ⊆ U

/-- The underlying finset of a class. -/
def Cls.carrier : Cls → Finset Char
  | .pos s => s
  | .neg s => s

theorem clsOK_iff (U : Finset Char) (cl : Cls) : ClsOK U cl ↔ cl.carrier ⊆ U := by
  cases cl <;> rfl

theorem clsOK_mono {U V : Finset Char} (h : U ⊆ V) {cl : Cls} (hcl : ClsOK U cl) :
    ClsOK V cl := by
  rw [clsOK_iff] at hcl ⊢
  exact hcl.trans h

theorem clsOK_self (cl : Cls) : ClsOK cl.carrier cl := by rw [clsOK_iff]

theorem clsOK_union {U : Finset Char} {a b : Cls} (ha : ClsOK U a) (hb : ClsOK U b) :
    ClsOK U (a.union b) := by
  cases a <;> cases b <;>
    (simp_all [ClsOK, Cls.union, Finset.subset_iff, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_union]
     try tauto)

theorem clsOK_inter {U : Finset Char} {a b : Cls} (ha : ClsOK U a) (hb : ClsOK U b) :
    ClsOK U (a.inter b) := by
  cases a <;> cases b <;>
    (simp_all [ClsOK, Cls.inter, Finset.subset_iff, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_union]
     try tauto)

theorem clsOK_empty (U : Finset Char) : ClsOK U (.neg ∅) := by
  simp [ClsOK]

theorem clsOK_norm {U : Finset Char} {a : Cls} (ha : ClsOK U a) : ClsOK U a.norm := by
  unfold Cls.norm
  split
  · exact clsOK_empty U
  · exact ha

theorem clsOK_foldl_union {U : Finset Char} {c : Cls} {cs : List Cls} (hc : ClsOK U c)
    (hcs : ∀ d ∈ cs, ClsOK U d) : ClsOK U (cs.foldl Cls.union c) := by
  induction cs generalizing c with
  | nil => exact hc
  | cons d ds ih =>
    exact ih (clsOK_union hc (hcs d (by simp))) fun x hx => hcs x (by simp [hx])

theorem clsOK_foldl_inter {U : Finset Char} {c : Cls} {cs : List Cls} (hc : ClsOK U c)
    (hcs : ∀ d ∈ cs, ClsOK U d) : ClsOK U (cs.foldl Cls.inter c) := by
  induction cs generalizing c with
  | nil => exact hc
  | cons d ds ih =>
    exact ih (clsOK_inter hc (hcs d (by simp))) fun x hx => hcs x (by simp [hx])

theorem clsOK_finite (U : Finset Char) : {cl : Cls | ClsOK U cl}.Finite := by
  have himg : {cl : Cls | ClsOK U cl} ⊆
      (fun s : Finset Char => (Cls.pos s)) '' ↑U.powerset ∪
      (fun s : Finset Char => (Cls.neg s)) '' ↑U.powerset := by
    rintro (s | s) hs
    · exact Or.inl ⟨s, by simpa using hs, rfl⟩
    · exact Or.inr ⟨s, by simpa using hs, rfl⟩
  exact Set.Finite.subset
    (((U.powerset : Finset (Finset Char)).finite_toSet.image _).union
      ((U.powerset : Finset (Finset Char)).finite_toSet.image _)) himg

/-- Every smart `sym` state whose class is bounded by `U`. -/
def symSet (U : Finset Char) : Set RE := (fun cl => sym cl) '' {cl : Cls | ClsOK U cl}

theorem symSet_finite (U : Finset Char) : (symSet U).Finite :=
  (clsOK_finite U).image _

theorem sym_mem_symSet {U : Finset Char} {cl : Cls} (h : ClsOK U cl) : sym cl ∈ symSet U :=
  ⟨cl, h, rfl⟩

/-- The classes of the `sym` states in `symSet U` are bounded by `U`. -/
theorem clsOK_of_mem_symSet {U : Finset Char} {cl : Cls} (h : (RE.sym cl) ∈ symSet U) :
    ClsOK U cl := by
  obtain ⟨d, hd, hsym⟩ := h
  simp only [] at hsym
  rw [Smart.sym_def] at hsym
  split at hsym
  · exact absurd hsym (by simp)
  · rw [RE.sym.injEq] at hsym
    subst hsym
    exact clsOK_norm hd

end Redgrep

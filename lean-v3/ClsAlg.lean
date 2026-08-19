import CharCard
import ACIDefs

/-!
# Semilattice algebra of character classes

`altL` merges the `sym` members of a union by folding `Cls.union` over their
classes *in list order*, and `cutL` does the same with `Cls.inter`.  Both
operations are commutative, associative and idempotent **on the nose**
(`CharCard.lean`), so such a fold depends only on the *set* of classes folded.
That is `Cls.foldl_congr` below, the fact that makes the ACI normal form
independent of the order in which members happen to be listed.

The second group of lemmas concerns `Cls.norm`, which collapses a full class
to `neg ∅`.  Two classes with the same normal form are interchangeable inside
`sym` (`sym_eq_of_norm_eq`), and `norm` is a congruence for the two class
operations (`Cls.norm_union_congr`, `Cls.norm_inter_congr`) — that is what
lets the merged `sym` member of a union be re-merged with further members.
-/

namespace Redgrep

namespace Cls

/-! ### Folds of an ACI operation -/

section Fold

variable {op : Cls → Cls → Cls}

theorem foldl_self_absorb (hassoc : ∀ a b c, op (op a b) c = op a (op b c)) (hidem : ∀ a, op a a = a)
    (c : Cls) (cs : List Cls) : op c (cs.foldl op c) = cs.foldl op c := by
  induction cs generalizing c with
  | nil => simpa using hidem c
  | cons x xs ih =>
    have h1 := ih (op c x)
    show op c (List.foldl op (op c x) xs) = List.foldl op (op c x) xs
    set F := List.foldl op (op c x) xs with hF
    have e0 : op c (op c x) = op c x := by rw [← hassoc, hidem]
    calc op c F = op c (op (op c x) F) := by rw [h1]
      _ = op (op c (op c x)) F := (hassoc _ _ _).symm
      _ = op (op c x) F := by rw [e0]
      _ = F := h1

theorem foldl_mem_absorb (hcomm : ∀ a b, op a b = op b a)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c)) (hidem : ∀ a, op a a = a)
    (c : Cls) (cs : List Cls) : ∀ x ∈ c :: cs, op x (cs.foldl op c) = cs.foldl op c := by
  induction cs generalizing c with
  | nil =>
    intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    simpa using hidem x
  | cons y ys ih =>
    intro x hx
    have hF := foldl_self_absorb hassoc hidem (op c y) ys
    show op x (List.foldl op (op c y) ys) = List.foldl op (op c y) ys
    set F := List.foldl op (op c y) ys with hFdef
    have hcy : op (op c y) F = F := hF
    have e0 : op c (op c y) = op c y := by rw [← hassoc, hidem]
    have hc : op c F = F := by
      calc op c F = op c (op (op c y) F) := by rw [hcy]
        _ = op (op c (op c y)) F := (hassoc _ _ _).symm
        _ = op (op c y) F := by rw [e0]
        _ = F := hcy
    have e1 : op y (op c y) = op c y := by
      rw [← hassoc, hcomm y c, hassoc, hidem]
    have hy : op y F = F := by
      calc op y F = op y (op (op c y) F) := by rw [hcy]
        _ = op (op y (op c y)) F := (hassoc _ _ _).symm
        _ = op (op c y) F := by rw [e1]
        _ = F := hcy
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact ih (op c y) x (by simp [hx])

theorem foldl_ub (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (c : Cls) (cs : List Cls) (d : Cls) (h : ∀ x ∈ c :: cs, op x d = d) :
    op (cs.foldl op c) d = d := by
  induction cs generalizing c with
  | nil => exact h c (by simp)
  | cons y ys ih =>
    refine ih (op c y) ?_
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hassoc, h y (by simp), h c (by simp)]
    · exact h x (by simp [hx])

/-- A fold of a commutative, associative and idempotent class operation
depends only on the *set* of classes folded. -/
theorem foldl_congr (hcomm : ∀ a b, op a b = op b a)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c)) (hidem : ∀ a, op a a = a)
    {c c' : Cls} {cs cs' : List Cls} (h : ∀ x, x ∈ c :: cs ↔ x ∈ c' :: cs') :
    cs.foldl op c = cs'.foldl op c' := by
  have h1 : op (cs'.foldl op c') (cs.foldl op c) = cs.foldl op c :=
    foldl_ub hassoc c' cs' _ fun x hx =>
      foldl_mem_absorb hcomm hassoc hidem c cs x ((h x).mpr hx)
  have h2 : op (cs.foldl op c) (cs'.foldl op c') = cs'.foldl op c' :=
    foldl_ub hassoc c cs _ fun x hx =>
      foldl_mem_absorb hcomm hassoc hidem c' cs' x ((h x).mp hx)
  rw [← h1, hcomm, h2]

end Fold

theorem foldl_union_congr {c c' : Cls} {cs cs' : List Cls}
    (h : ∀ x, x ∈ c :: cs ↔ x ∈ c' :: cs') :
    cs.foldl Cls.union c = cs'.foldl Cls.union c' :=
  foldl_congr Cls.union_comm Cls.union_assoc Cls.union_self h

theorem foldl_inter_congr {c c' : Cls} {cs cs' : List Cls}
    (h : ∀ x, x ∈ c :: cs ↔ x ∈ c' :: cs') :
    cs.foldl Cls.inter c = cs'.foldl Cls.inter c' :=
  foldl_congr Cls.inter_comm Cls.inter_assoc Cls.inter_self h

/-! ### `Cls.norm` as a congruence -/

theorem norm_eq_neg_empty_iff (a : Cls) : a.norm = .neg ∅ ↔ a.isFull = true := by
  unfold Cls.norm
  constructor
  · intro h
    split at h
    · assumption
    · subst h; simp [Cls.isFull]
  · intro h; rw [if_pos h]

theorem isFull_of_norm_eq {a b : Cls} (h : a.norm = b.norm) (ha : a.isFull = true) :
    b.isFull = true := by
  rw [← norm_eq_neg_empty_iff] at ha ⊢
  rw [← h]; exact ha

/-- Two classes with the same normal form are interchangeable under `sym`. -/
theorem sym_eq_of_norm_eq {a b : Cls} (h : a.norm = b.norm) : sym a = sym b := by
  rw [Smart.sym_def, Smart.sym_def, ← Cls.isEmpty_norm_eq a, ← Cls.isEmpty_norm_eq b, h]

/-- Classes with the same normal form have the same normal form after a union
with any further class. -/
theorem norm_union_congr {a b : Cls} (h : a.norm = b.norm) (d : Cls) :
    (a.union d).norm = (b.union d).norm := by
  by_cases ha : a.isFull = true
  · have hb : b.isFull = true := isFull_of_norm_eq h ha
    have hfull : ∀ x : Cls, x.isFull = true → ((x.union d).norm = .neg ∅) := by
      intro x hx
      rw [norm_eq_neg_empty_iff, Cls.isFull_iff]
      intro c
      rw [inCls_union, (Cls.isFull_iff x).mp hx c]
      rfl
    rw [hfull a ha, hfull b hb]
  · have hb : ¬ b.isFull = true := fun hb => ha (isFull_of_norm_eq h.symm hb)
    have hna : a.norm = a := by unfold Cls.norm; rw [if_neg ha]
    have hnb : b.norm = b := by unfold Cls.norm; rw [if_neg hb]
    rw [← hna, ← hnb, h]

/-- A class is *normal* when `Cls.norm` fixes it: it is not full, or it is the
canonical full class `neg ∅`.  Every class occurring in a canonical term is
normal. -/
def Normal (cl : Cls) : Prop := cl.norm = cl

theorem normal_of_isFull {a : Cls} (hn : Normal a) (hf : a.isFull = true) : a = .neg ∅ := by
  rw [← hn]
  exact (norm_eq_neg_empty_iff a).mpr hf

theorem isFull_inter {a b : Cls} (h : (a.inter b).isFull = true) :
    a.isFull = true ∧ b.isFull = true := by
  rw [Cls.isFull_iff] at h
  refine ⟨(Cls.isFull_iff a).mpr fun c => ?_, (Cls.isFull_iff b).mpr fun c => ?_⟩ <;>
    · have hc := h c
      rw [inCls_inter] at hc
      simp only [Bool.and_eq_true] at hc
      simp [hc.1, hc.2]

/-- Intersection preserves normality of classes. -/
theorem normal_inter {a b : Cls} (ha : Normal a) (hb : Normal b) : Normal (a.inter b) := by
  unfold Normal Cls.norm
  split
  · rename_i hf
    obtain ⟨hfa, hfb⟩ := isFull_inter hf
    rw [normal_of_isFull ha hfa, normal_of_isFull hb hfb]
    simp [Cls.inter]
  · rfl

theorem normal_foldl_inter {c : Cls} (hc : Normal c) {cs : List Cls}
    (hcs : ∀ x ∈ cs, Normal x) : Normal (cs.foldl Cls.inter c) := by
  induction cs generalizing c with
  | nil => exact hc
  | cons x xs ih =>
    exact ih (normal_inter hc (hcs x (by simp))) fun y hy => hcs y (by simp [hy])

theorem norm_foldl_union_congr {a b : Cls} (h : a.norm = b.norm) (ds : List Cls) :
    (ds.foldl Cls.union a).norm = (ds.foldl Cls.union b).norm := by
  induction ds generalizing a b with
  | nil => exact h
  | cons d ds ih => exact ih (norm_union_congr h d)

end Cls

end Redgrep

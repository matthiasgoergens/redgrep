import Core
import Mathlib

/-!
# Cardinality of `Char` and the resulting `Cls` facts

`Core.lean` tests emptiness/fullness of a character class against the constant
`charCount = 1112064`.  Making that test *mean* anything requires knowing that
`Char` really has `charCount` elements — the proof obligation the core module
records but does not discharge.  This file discharges it (`card_char`) and
derives the class-level consequences used by the semantics:

* `Cls.isEmpty_iff` / `Cls.isFull_iff` — the total emptiness/fullness tests are
  correct;
* `inCls_norm`, `inCls_union`, `inCls_inter`, `inCls_compl` — the class
  operations denote the boolean operations on membership;
* `Cls.union`/`Cls.inter` are commutative, associative and idempotent *on the
  nose* (needed by the ACI layer, which folds them over unordered member
  lists).
-/

namespace Redgrep

/-- Every character, as a `Finset Char`. -/
def allChars : Finset Char :=
  ((Finset.range 0x110000).filter (fun n => n < 0xd800 ∨ 0xdfff < n)).image Char.ofNat

theorem mem_allChars (c : Char) : c ∈ allChars := by
  have hv : c.toNat = c.val.toNat := rfl
  simp only [allChars, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  refine ⟨c.toNat, ⟨?_, ?_⟩, Char.ofNat_toNat c⟩
  · rcases c.valid with h | ⟨_, h⟩ <;> omega
  · rcases c.valid with h | ⟨h, _⟩
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

theorem card_allChars : allChars.card = charCount := by
  rw [allChars, Finset.card_image_of_injOn]
  · have hset : ((Finset.range 0x110000).filter (fun n => n < 0xd800 ∨ 0xdfff < n))
        = Finset.range 55296 ∪ Finset.Ico 57344 1114112 := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    rw [hset, Finset.card_union_of_disjoint, Finset.card_range, Nat.card_Ico]
    · rfl
    · rw [Finset.disjoint_left]
      intro n hn hn'
      simp only [Finset.mem_range] at hn
      simp only [Finset.mem_Ico] at hn'
      omega
  · intro n hn m hm hnm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hn hm
    have hn' : Nat.isValidChar n := by unfold Nat.isValidChar; omega
    have hm' : Nat.isValidChar m := by unfold Nat.isValidChar; omega
    have := congrArg Char.toNat hnm
    rwa [Char.toNat_ofNat, Char.toNat_ofNat, if_pos hn', if_pos hm'] at this

instance : Fintype Char := ⟨allChars, mem_allChars⟩

theorem card_char : Fintype.card Char = charCount := card_allChars

/-- A finset of characters is everything exactly when it has `charCount`
elements. -/
theorem card_eq_charCount_iff (s : Finset Char) : s.card = charCount ↔ ∀ c, c ∈ s := by
  constructor
  · intro hs c
    have hsub : s ⊆ allChars := fun x _ => mem_allChars x
    have : s = allChars :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_allChars, hs])
    rw [this]; exact mem_allChars c
  · intro hs
    have : s = allChars := Finset.ext fun c => ⟨fun _ => mem_allChars c, fun _ => hs c⟩
    rw [this, card_allChars]

/-! ### Consequences for `Cls` -/

theorem Cls.isEmpty_iff (cl : Cls) : cl.isEmpty = true ↔ ∀ c, inCls c cl = false := by
  cases cl with
  | pos s =>
    simp only [Cls.isEmpty, inCls, decide_eq_true_eq, decide_eq_false_iff_not]
    constructor
    · rintro rfl c; simp
    · intro h; exact Finset.eq_empty_of_forall_notMem h
  | neg s =>
    simp only [Cls.isEmpty, inCls, decide_eq_true_eq, decide_eq_false_iff_not,
      Decidable.not_not]
    exact card_eq_charCount_iff s

theorem Cls.isFull_iff (cl : Cls) : cl.isFull = true ↔ ∀ c, inCls c cl = true := by
  cases cl with
  | pos s =>
    simp only [Cls.isFull, inCls, decide_eq_true_eq]
    exact card_eq_charCount_iff s
  | neg s =>
    simp only [Cls.isFull, inCls, decide_eq_true_eq]
    constructor
    · rintro rfl c; simp
    · intro h
      refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
      exact h c hc

@[simp] theorem inCls_norm (c : Char) (cl : Cls) : inCls c cl.norm = inCls c cl := by
  unfold Cls.norm
  split
  · rename_i hfull
    rw [(Cls.isFull_iff cl).mp hfull c]
    simp [inCls]
  · rfl

@[simp] theorem inCls_union (c : Char) (a b : Cls) :
    inCls c (a.union b) = (inCls c a || inCls c b) := by
  cases a <;> cases b <;>
    simp [Cls.union, inCls, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
      Bool.or_comm]

@[simp] theorem inCls_inter (c : Char) (a b : Cls) :
    inCls c (a.inter b) = (inCls c a && inCls c b) := by
  cases a <;> cases b <;>
    simp [Cls.inter, inCls, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
      Bool.and_comm]

@[simp] theorem inCls_compl (c : Char) (a : Cls) :
    inCls c a.compl = !inCls c a := by
  cases a <;> simp [Cls.compl, inCls]

/-- `Cls.union` is commutative (on the nose, not just semantically). -/
theorem Cls.union_comm (a b : Cls) : a.union b = b.union a := by
  cases a <;> cases b <;> simp [Cls.union, Finset.union_comm, Finset.inter_comm]

/-- `Cls.union` is associative. -/
theorem Cls.union_assoc (a b c : Cls) : (a.union b).union c = a.union (b.union c) := by
  cases a <;> cases b <;> cases c <;>
    simp [Cls.union, Finset.union_assoc, Finset.inter_assoc] <;>
    ext x <;> simp [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] <;> tauto

/-- `Cls.union` is idempotent. -/
@[simp] theorem Cls.union_self (a : Cls) : a.union a = a := by
  cases a <;> simp [Cls.union]

/-- `Cls.inter` is commutative. -/
theorem Cls.inter_comm (a b : Cls) : a.inter b = b.inter a := by
  cases a <;> cases b <;> simp [Cls.inter, Finset.union_comm, Finset.inter_comm]

/-- `Cls.inter` is associative. -/
theorem Cls.inter_assoc (a b c : Cls) : (a.inter b).inter c = a.inter (b.inter c) := by
  cases a <;> cases b <;> cases c <;>
    simp [Cls.inter, Finset.union_assoc, Finset.inter_assoc] <;>
    ext x <;> simp [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] <;> tauto

/-- `Cls.inter` is idempotent. -/
@[simp] theorem Cls.inter_self (a : Cls) : a.inter a = a := by
  cases a <;> simp [Cls.inter]

end Redgrep

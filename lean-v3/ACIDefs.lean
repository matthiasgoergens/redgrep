import REOrder
import CharCard
import SmartLang

/-!
# Structural canonicity: the definitions

`Core.lean` builds canonical terms with the smart constructors `sym`, `altL`,
`cutL`, `seq2`, `rep_`, `not_`, `invHom_`, and calls a term *canonical*
(`Canonical r`, i.e. `canon r = r`) when the bottom-up rebuild fixes it.  That
definition is convenient to state but opaque to work with, so this file
introduces the equivalent **structural** description `IsCanon` — "every node
has the shape its smart constructor produces".

The interesting case is the union: `altL` flattens, merges the `sym` members
into a single class, sorts and deduplicates, so a canonical union is a
right-nested chain whose member list is strictly sorted and contains at most
one `sym`.  That is exactly `AltListOK`; `CutListOK` is its dual.

The equivalence with `Canonical` is assembled in `ACI.lean` out of the
per-constructor files `ACIAlt.lean`, `ACICut.lean` and `ACISeq.lean`.
-/

namespace Redgrep

/-! ### Shape predicates

Naming the "is not a nested `alt`/`cut`/`seq`/`rep`/`not`" side conditions
keeps them from being generalised away when they appear as hypotheses. -/

/-- `r` is not a union node. -/
def NotAlt : RE → Prop | .alt _ _ => False | _ => True
/-- `r` is not an intersection node. -/
def NotCut : RE → Prop | .cut _ _ => False | _ => True
/-- `r` is not a concatenation node. -/
def NotSeq : RE → Prop | .seq _ _ => False | _ => True
/-- `r` is not a star node. -/
def NotRep : RE → Prop | .rep _ => False | _ => True
/-- `r` is not a complement node. -/
def NotNot : RE → Prop | .not _ => False | _ => True

@[simp] theorem notAlt_alt (a b : RE) : ¬ NotAlt (.alt a b) := id
@[simp] theorem notCut_cut (a b : RE) : ¬ NotCut (.cut a b) := id
@[simp] theorem notSeq_seq (a b : RE) : ¬ NotSeq (.seq a b) := id
@[simp] theorem notRep_rep (a : RE) : ¬ NotRep (.rep a) := id
@[simp] theorem notNot_not (a : RE) : ¬ NotNot (.not a) := id

/-- The member list of a canonical union: sorted and duplicate-free for
`RE.le`, no `nil`, no `top`, no nested `alt`, and at most one `sym` (the
others having been merged into it). -/
def AltListOK (L : List RE) : Prop :=
  L.Pairwise (fun a b => RE.le a b = true) ∧ L.Nodup ∧
  (∀ x ∈ L, x ≠ .nil ∧ x ≠ top ∧ NotAlt x) ∧
  (L.filter isSym).length ≤ 1

/-- The member list of a canonical intersection: dual to `AltListOK`. -/
def CutListOK (L : List RE) : Prop :=
  L.Pairwise (fun a b => RE.le a b = true) ∧ L.Nodup ∧
  (∀ x ∈ L, x ≠ .nil ∧ x ≠ top ∧ NotCut x) ∧
  (L.filter isSym).length ≤ 1

/-- Structural canonicity: every node has the shape its smart constructor
produces.  `canonical_iff_isCanon` (in `ACI.lean`) identifies this with
`Canonical`. -/
def IsCanon : RE → Prop
  | .sym cl => sym cl = .sym cl
  | .alt a b =>
      IsCanon a ∧ IsCanon b ∧ NotAlt a ∧
        a ≠ .nil ∧ b ≠ .nil ∧ AltListOK (altToList a ++ altToList b)
  | .cut a b =>
      IsCanon a ∧ IsCanon b ∧ NotCut a ∧
        a ≠ top ∧ b ≠ top ∧ CutListOK (cutToList a ++ cutToList b)
  | .seq a b =>
      IsCanon a ∧ IsCanon b ∧ NotSeq a ∧
        a ≠ .eps ∧ a ≠ .nil ∧ b ≠ .eps ∧ b ≠ .nil
  | .rep r =>
      IsCanon r ∧ r ≠ .nil ∧ r ≠ .eps ∧ r ≠ top ∧ NotRep r
  | .not r => IsCanon r ∧ NotNot r
  | .invHom h r => IsCanon r ∧ homNorm h = h ∧ h ≠ [] ∧ r ≠ .nil
  | .eps => True
  | .nil => True

/-! ### Character classes -/

theorem Cls.norm_idem (cl : Cls) : cl.norm.norm = cl.norm := by
  unfold Cls.norm
  split
  · rw [if_pos (by simp [Cls.isFull])]
  · rfl

theorem Cls.isEmpty_norm_eq (cl : Cls) : cl.norm.isEmpty = cl.isEmpty := by
  unfold Cls.norm
  split
  · rename_i hfull
    rw [show (Cls.neg ∅).isEmpty = false from by simp [Cls.isEmpty, charCount]]
    rcases cl with s | s
    · simp only [Cls.isFull, decide_eq_true_eq] at hfull
      simp only [Cls.isEmpty, eq_comm (a := false), decide_eq_false_iff_not]
      intro hs
      rw [hs] at hfull
      simp [charCount] at hfull
    · simp only [Cls.isFull, decide_eq_true_eq] at hfull
      subst hfull
      simp [Cls.isEmpty, charCount]
  · rfl

theorem isCanon_top : IsCanon top := ⟨trivial, trivial⟩

theorem isCanon_eps : IsCanon .eps := trivial

theorem isCanon_nil : IsCanon .nil := trivial

/-- The smart `sym` always lands in `IsCanon`. -/
theorem isCanon_sym (cl : Cls) : IsCanon (sym cl) := by
  rw [Smart.sym_def]
  split
  · exact isCanon_nil
  · rename_i hemp
    show sym cl.norm = .sym cl.norm
    rw [Smart.sym_def, if_neg (by rw [Cls.isEmpty_norm_eq]; exact hemp), Cls.norm_idem]

theorem isCanon_alt_iff {a b : RE} :
    IsCanon (.alt a b) ↔
      IsCanon a ∧ IsCanon b ∧ NotAlt a ∧
        a ≠ .nil ∧ b ≠ .nil ∧ AltListOK (altToList a ++ altToList b) := Iff.rfl

theorem isCanon_cut_iff {a b : RE} :
    IsCanon (.cut a b) ↔
      IsCanon a ∧ IsCanon b ∧ NotCut a ∧
        a ≠ top ∧ b ≠ top ∧ CutListOK (cutToList a ++ cutToList b) := Iff.rfl

theorem isCanon_seq_iff {a b : RE} :
    IsCanon (.seq a b) ↔
      IsCanon a ∧ IsCanon b ∧ NotSeq a ∧
        a ≠ .eps ∧ a ≠ .nil ∧ b ≠ .eps ∧ b ≠ .nil := Iff.rfl

theorem isCanon_rep_iff {r : RE} :
    IsCanon (.rep r) ↔
      IsCanon r ∧ r ≠ .nil ∧ r ≠ .eps ∧ r ≠ top ∧ NotRep r := Iff.rfl

theorem isCanon_not_iff {r : RE} :
    IsCanon (.not r) ↔ IsCanon r ∧ NotNot r := Iff.rfl

theorem isCanon_invHom_iff {h : List (Char × List Char)} {r : RE} :
    IsCanon (.invHom h r) ↔ IsCanon r ∧ homNorm h = h ∧ h ≠ [] ∧ r ≠ .nil := Iff.rfl

end Redgrep

import Semantics
import CharCard
import REOrder

/-!
# Languages of the smart constructors

The semantic half of the ACI story: every smart constructor of `Core.lean`
denotes exactly the language of the plain constructor it canonicalises.  These
are the lemmas that let the engine — which is routed through the smart
constructors — be verified against `lang` by the ordinary Brzozowski argument.

`invHom_` normalises its association list (`homNorm`).  Because `applyHom`
resolves a key by "first hit wins", normalisation deduplicates *by key* —
keeping the first binding — before dropping identity entries, sorting and
deduplicating; it therefore preserves the denoted homomorphism pointwise
(`homNorm_applyHom`), and the language-preservation statement for `invHom_`
(`Engine.lean`, `Correctness.lean`) needs no side condition.
-/

open Language Computability

namespace Redgrep

/-! The smart-constructor language lemmas live in the `Smart` namespace, so that
`Correctness.lean` can state the user-facing contracts under their own names. -/
namespace Smart

/-! ### Membership in `lang`, constructor by constructor -/

@[simp] theorem mem_lang_sym {cl : Cls} {w : List Char} :
    w ∈ lang (.sym cl) ↔ ∃ c, inCls c cl = true ∧ w = [c] := Iff.rfl

@[simp] theorem mem_lang_alt {a b : RE} {w : List Char} :
    w ∈ lang (.alt a b) ↔ w ∈ lang a ∨ w ∈ lang b := Iff.rfl

@[simp] theorem mem_lang_cut {a b : RE} {w : List Char} :
    w ∈ lang (.cut a b) ↔ w ∈ lang a ∧ w ∈ lang b := Iff.rfl

@[simp] theorem mem_lang_not {a : RE} {w : List Char} :
    w ∈ lang (.not a) ↔ w ∉ lang a := Iff.rfl

@[simp] theorem mem_lang_nil {w : List Char} : w ∈ lang .nil ↔ False :=
  ⟨fun h => (Set.notMem_empty w) (by rwa [show (lang .nil) = (∅ : Set (List Char)) from rfl] at h),
    fun h => h.elim⟩

@[simp] theorem mem_lang_eps {w : List Char} : w ∈ lang .eps ↔ w = [] := by
  show w ∈ (1 : Language Char) ↔ w = []
  exact Language.mem_one w

@[simp] theorem mem_lang_top {w : List Char} : w ∈ lang top := by
  show w ∉ lang .nil
  simp

@[simp] theorem lang_top : lang top = Set.univ :=
  Set.eq_univ_of_forall fun _ => mem_lang_top

@[simp] theorem mem_lang_seq {a b : RE} {w : List Char} :
    w ∈ lang (.seq a b) ↔ ∃ x ∈ lang a, ∃ y ∈ lang b, x ++ y = w := by
  show w ∈ lang a * lang b ↔ _
  simp [Language.mem_mul]

@[simp] theorem mem_lang_invHom {h : List (Char × List Char)} {r : RE} {w : List Char} :
    w ∈ lang (.invHom h r) ↔ (w.flatMap (applyHom h)) ∈ lang r := Iff.rfl

theorem lang_rep (r : RE) : lang (.rep r) = (lang r)∗ := rfl

/-! ### Character classes -/

theorem sym_def (cl : Cls) : sym cl = if cl.isEmpty then .nil else .sym cl.norm := rfl

theorem lang_smart_sym (cls : Cls) : lang (sym cls) = lang (.sym cls) := by
  rw [sym_def]
  split
  · rename_i hempty
    ext w
    simp only [mem_lang_nil, mem_lang_sym, false_iff, not_exists]
    intro c
    rw [(Cls.isEmpty_iff cls).mp hempty c]
    simp
  · ext w; simp

theorem inCls_foldl_union (c : Char) (c0 : Cls) (cs : List Cls) :
    inCls c (cs.foldl Cls.union c0) = (inCls c c0 || cs.any (fun cl => inCls c cl)) := by
  induction cs generalizing c0 with
  | nil => simp
  | cons x xs ih => simp [ih, inCls_union, Bool.or_assoc]

theorem inCls_foldl_inter (c : Char) (c0 : Cls) (cs : List Cls) :
    inCls c (cs.foldl Cls.inter c0) = (inCls c c0 && cs.all (fun cl => inCls c cl)) := by
  induction cs generalizing c0 with
  | nil => simp
  | cons x xs ih => simp [ih, inCls_inter, Bool.and_assoc]

@[simp] theorem mem_symClasses {cl : Cls} {rs : List RE} :
    cl ∈ symClasses rs ↔ RE.sym cl ∈ rs := by
  simp only [symClasses, List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, hcl⟩
    cases r <;> simp_all
  · intro h
    exact ⟨.sym cl, h, rfl⟩


/-! ### Flattening and rebuilding: `altToList`/`altOfList` -/

@[simp] theorem altToList_alt (a b : RE) : altToList (.alt a b) = altToList a ++ altToList b := rfl
@[simp] theorem altToList_nil : altToList .nil = [] := rfl
@[simp] theorem altToList_sym (cl : Cls) : altToList (.sym cl) = [.sym cl] := rfl
@[simp] theorem altToList_cut (a b : RE) : altToList (.cut a b) = [.cut a b] := rfl
@[simp] theorem altToList_seq (a b : RE) : altToList (.seq a b) = [.seq a b] := rfl
@[simp] theorem altToList_rep (a : RE) : altToList (.rep a) = [.rep a] := rfl
@[simp] theorem altToList_not (a : RE) : altToList (.not a) = [.not a] := rfl
@[simp] theorem altToList_invHom (h : List (Char × List Char)) (a : RE) :
    altToList (.invHom h a) = [.invHom h a] := rfl
@[simp] theorem altToList_eps : altToList .eps = [.eps] := rfl

@[simp] theorem cutToList_cut (a b : RE) : cutToList (.cut a b) = cutToList a ++ cutToList b := rfl
@[simp] theorem cutToList_sym (cl : Cls) : cutToList (.sym cl) = [.sym cl] := rfl
@[simp] theorem cutToList_alt (a b : RE) : cutToList (.alt a b) = [.alt a b] := rfl
@[simp] theorem cutToList_seq (a b : RE) : cutToList (.seq a b) = [.seq a b] := rfl
@[simp] theorem cutToList_rep (a : RE) : cutToList (.rep a) = [.rep a] := rfl
@[simp] theorem cutToList_invHom (h : List (Char × List Char)) (a : RE) :
    cutToList (.invHom h a) = [.invHom h a] := rfl
@[simp] theorem cutToList_eps : cutToList .eps = [.eps] := rfl
@[simp] theorem cutToList_nil : cutToList .nil = [.nil] := rfl
theorem cutToList_not (a : RE) : cutToList (.not a) = if a = .nil then [] else [.not a] := by
  show (if RE.not a = top then [] else [RE.not a]) = _
  by_cases h : a = RE.nil <;> simp [h, top]

@[simp] theorem seqToList_seq (a b : RE) : seqToList (.seq a b) = seqToList a ++ seqToList b := rfl
@[simp] theorem seqToList_eps : seqToList .eps = [] := rfl
@[simp] theorem seqToList_sym (cl : Cls) : seqToList (.sym cl) = [.sym cl] := rfl
@[simp] theorem seqToList_alt (a b : RE) : seqToList (.alt a b) = [.alt a b] := rfl
@[simp] theorem seqToList_cut (a b : RE) : seqToList (.cut a b) = [.cut a b] := rfl
@[simp] theorem seqToList_rep (a : RE) : seqToList (.rep a) = [.rep a] := rfl
@[simp] theorem seqToList_not (a : RE) : seqToList (.not a) = [.not a] := rfl
@[simp] theorem seqToList_invHom (h : List (Char × List Char)) (a : RE) :
    seqToList (.invHom h a) = [.invHom h a] := rfl
@[simp] theorem seqToList_nil : seqToList .nil = [.nil] := rfl

theorem altOfList_cons (r : RE) (l : List RE) :
    altOfList (r :: l) = if l = [] then r else .alt r (altOfList l) := by cases l <;> rfl
theorem cutOfList_cons (r : RE) (l : List RE) :
    cutOfList (r :: l) = if l = [] then r else .cut r (cutOfList l) := by cases l <;> rfl
theorem seqOfList_cons (r : RE) (l : List RE) :
    seqOfList (r :: l) = if l = [] then r else .seq r (seqOfList l) := by cases l <;> rfl

theorem mem_lang_altOfList (l : List RE) (w : List Char) :
    w ∈ lang (altOfList l) ↔ ∃ r ∈ l, w ∈ lang r := by
  induction l with
  | nil => simp [altOfList]
  | cons r rs ih =>
    rw [altOfList_cons]
    split
    · rename_i h; subst h; simp
    · simp only [mem_lang_alt, ih, List.mem_cons]
      aesop

theorem mem_lang_cutOfList (l : List RE) (w : List Char) :
    w ∈ lang (cutOfList l) ↔ ∀ r ∈ l, w ∈ lang r := by
  induction l with
  | nil =>
    show w ∈ lang top ↔ _
    simp only [List.not_mem_nil, false_implies, implies_true, iff_true]
    exact mem_lang_top
  | cons r rs ih =>
    rw [cutOfList_cons]
    split
    · rename_i h; subst h; simp
    · simp only [mem_lang_cut, ih, List.mem_cons]
      aesop

theorem mem_lang_altToList (r : RE) (w : List Char) :
    w ∈ lang r ↔ ∃ x ∈ altToList r, w ∈ lang x := by
  induction r with
  | alt a b iha ihb =>
    simp only [altToList_alt, mem_lang_alt, iha, ihb, List.mem_append]
    aesop
  | _ => simp

theorem mem_lang_cutToList (r : RE) (w : List Char) :
    w ∈ lang r ↔ ∀ x ∈ cutToList r, w ∈ lang x := by
  induction r with
  | cut a b iha ihb =>
    simp only [cutToList_cut, mem_lang_cut, iha, ihb, List.mem_append]
    aesop
  | not a iha =>
    rw [cutToList_not]
    split
    · rename_i h; subst h; simp
    · simp
  | _ => simp

/-! ### `altL` -/

/-- The merged `sym` member produced by `altL` (at most one). -/
def altMerged (syms : List RE) : List RE :=
  match symClasses syms with
  | [] => []
  | c :: cs =>
    match sym (cs.foldl Cls.union c) with
    | .nil => []
    | s => [s]

theorem isSym_iff {r : RE} : isSym r = true ↔ ∃ cl, r = .sym cl := by
  cases r <;> simp [isSym]

theorem altL_eq (rs : List RE) :
    altL rs =
      (if top ∈ rs.flatMap altToList then top
       else altOfList (sortDedup (altMerged ((rs.flatMap altToList).filter isSym) ++
              (rs.flatMap altToList).filter (not ∘ isSym)))) := by
  simp only [altL, altMerged, List.partition_eq_filter_filter]
  rfl

/-- The merged class member has the same language as the `sym` members it replaces. -/
theorem mem_lang_altMerged {syms : List RE} (hs : ∀ x ∈ syms, isSym x = true)
    (w : List Char) :
    (∃ s ∈ altMerged syms, w ∈ lang s) ↔ ∃ x ∈ syms, w ∈ lang x := by
  unfold altMerged
  split
  · rename_i hsc
    simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_exists]
    rintro x ⟨hx, hw⟩
    obtain ⟨cl, rfl⟩ := isSym_iff.mp (hs x hx)
    have hcl : cl ∈ symClasses syms := mem_symClasses.mpr hx
    rw [hsc] at hcl; simp at hcl
  · rename_i c cs hsc
    have hmem : ∀ cl : Cls, (RE.sym cl ∈ syms) ↔ (cl = c ∨ cl ∈ cs) := by
      intro cl
      rw [← mem_symClasses, hsc]; simp
    have key : (∃ x ∈ syms, w ∈ lang x) ↔
        ∃ ch, inCls ch (cs.foldl Cls.union c) = true ∧ w = [ch] := by
      constructor
      · rintro ⟨x, hx, hw⟩
        obtain ⟨cl, rfl⟩ := isSym_iff.mp (hs x hx)
        obtain ⟨ch, hch, rfl⟩ := hw
        refine ⟨ch, ?_, rfl⟩
        rw [inCls_foldl_union]
        rcases (hmem cl).mp hx with rfl | hcl
        · simp [hch]
        · simp only [Bool.or_eq_true, List.any_eq_true]
          exact Or.inr ⟨cl, hcl, hch⟩
      · rintro ⟨ch, hch, rfl⟩
        rw [inCls_foldl_union] at hch
        simp only [Bool.or_eq_true, List.any_eq_true] at hch
        rcases hch with hch | ⟨cl, hcl, hch⟩
        · exact ⟨.sym c, (hmem c).mpr (Or.inl rfl), ch, hch, rfl⟩
        · exact ⟨.sym cl, (hmem cl).mpr (Or.inr hcl), ch, hch, rfl⟩
    rw [key]
    split
    · rename_i hsym
      have hempty : (cs.foldl Cls.union c).isEmpty = true := by
        rw [sym_def] at hsym; split at hsym
        · assumption
        · simp at hsym
      simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_exists]
      rintro ch ⟨hch, -⟩
      rw [(Cls.isEmpty_iff _).mp hempty ch] at hch
      simp at hch
    · simp only [List.mem_singleton, exists_eq_left]
      rw [lang_smart_sym]
      simp

theorem mem_lang_flatMap_altToList (rs : List RE) (w : List Char) :
    (∃ r ∈ rs, w ∈ lang r) ↔ ∃ x ∈ rs.flatMap altToList, w ∈ lang x := by
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, hw⟩
    obtain ⟨x, hx, hwx⟩ := (mem_lang_altToList r w).mp hw
    exact ⟨x, ⟨r, hr, hx⟩, hwx⟩
  · rintro ⟨x, ⟨r, hr, hx⟩, hwx⟩
    exact ⟨r, hr, (mem_lang_altToList r w).mpr ⟨x, hx, hwx⟩⟩

theorem mem_lang_altL (rs : List RE) (w : List Char) :
    w ∈ lang (altL rs) ↔ ∃ r ∈ rs, w ∈ lang r := by
  rw [altL_eq, mem_lang_flatMap_altToList]
  split
  · rename_i htop
    simp only [mem_lang_top, true_iff]
    exact ⟨top, htop, mem_lang_top⟩
  · rw [mem_lang_altOfList]
    simp only [mem_sortDedup, List.mem_append]
    rw [show (∃ x, (x ∈ altMerged ((rs.flatMap altToList).filter isSym) ∨
            x ∈ (rs.flatMap altToList).filter (not ∘ isSym)) ∧ w ∈ lang x) ↔
        (∃ x ∈ altMerged ((rs.flatMap altToList).filter isSym), w ∈ lang x) ∨
          (∃ x ∈ (rs.flatMap altToList).filter (not ∘ isSym), w ∈ lang x) by aesop]
    rw [mem_lang_altMerged (fun x hx => (List.mem_filter.mp hx).2)]
    simp only [List.mem_filter, Function.comp_apply, Bool.not_eq_true']
    constructor
    · rintro (⟨x, ⟨hx, -⟩, hw⟩ | ⟨x, ⟨hx, -⟩, hw⟩) <;> exact ⟨x, hx, hw⟩
    · rintro ⟨x, hx, hw⟩
      by_cases hs : isSym x = true
      · exact Or.inl ⟨x, ⟨hx, hs⟩, hw⟩
      · exact Or.inr ⟨x, ⟨hx, by simpa using hs⟩, hw⟩

theorem lang_alt2 (r₁ r₂ : RE) : lang (alt2 r₁ r₂) = lang r₁ ⊔ lang r₂ := by
  refine Set.ext fun w => ?_
  show w ∈ lang (altL [r₁, r₂]) ↔ (w ∈ lang r₁ ∨ w ∈ lang r₂)
  rw [mem_lang_altL]
  simp

/-! ### `cutL` -/

/-- The body built by `cutL` from its `sym` members and the rest. -/
def cutBody (syms rest : List RE) : RE :=
  match symClasses syms with
  | [] => cutOfList (sortDedup rest)
  | c :: cs =>
    match sym (cs.foldl Cls.inter c) with
    | .nil => .nil
    | s => cutOfList (sortDedup (s :: rest))

theorem cutL_eq (rs : List RE) :
    cutL rs =
      (if RE.nil ∈ rs.flatMap cutToList then .nil
       else cutBody ((rs.flatMap cutToList).filter isSym)
              ((rs.flatMap cutToList).filter (not ∘ isSym))) := by
  simp only [cutL, cutBody, List.partition_eq_filter_filter]
  rfl

theorem mem_lang_flatMap_cutToList (rs : List RE) (w : List Char) :
    (∀ r ∈ rs, w ∈ lang r) ↔ ∀ x ∈ rs.flatMap cutToList, w ∈ lang x := by
  simp only [List.mem_flatMap]
  constructor
  · rintro h x ⟨r, hr, hx⟩
    exact (mem_lang_cutToList r w).mp (h r hr) x hx
  · intro h r hr
    exact (mem_lang_cutToList r w).mpr fun x hx => h x ⟨r, hr, hx⟩

theorem mem_lang_cutBody {syms : List RE} (hs : ∀ x ∈ syms, isSym x = true)
    (rest : List RE) (w : List Char) :
    w ∈ lang (cutBody syms rest) ↔ (∀ x ∈ syms, w ∈ lang x) ∧ (∀ x ∈ rest, w ∈ lang x) := by
  unfold cutBody
  split
  · rename_i hsc
    have hnil : syms = [] := by
      rcases hsyms : syms with _ | ⟨x, xs⟩
      · rfl
      · exfalso
        obtain ⟨cl, rfl⟩ := isSym_iff.mp (hs x (by rw [hsyms]; simp))
        have hcl : cl ∈ symClasses syms := mem_symClasses.mpr (by rw [hsyms]; simp)
        rw [hsc] at hcl; simp at hcl
    subst hnil
    rw [mem_lang_cutOfList]
    simp
  · rename_i c cs hsc
    have hmem : ∀ cl : Cls, (RE.sym cl ∈ syms) ↔ (cl = c ∨ cl ∈ cs) := by
      intro cl
      rw [← mem_symClasses, hsc]; simp
    have key : (∀ x ∈ syms, w ∈ lang x) ↔
        ∃ ch, inCls ch (cs.foldl Cls.inter c) = true ∧ w = [ch] := by
      constructor
      · intro h
        obtain ⟨ch, hch, rfl⟩ := h (.sym c) ((hmem c).mpr (Or.inl rfl))
        refine ⟨ch, ?_, rfl⟩
        rw [inCls_foldl_inter]
        simp only [Bool.and_eq_true, List.all_eq_true, hch, true_and]
        intro cl hcl
        obtain ⟨ch', hch', he⟩ := h (.sym cl) ((hmem cl).mpr (Or.inr hcl))
        simp only [List.cons.injEq, and_true] at he
        rwa [he]
      · rintro ⟨ch, hch, rfl⟩ x hx
        obtain ⟨cl, rfl⟩ := isSym_iff.mp (hs x hx)
        rw [inCls_foldl_inter] at hch
        simp only [Bool.and_eq_true, List.all_eq_true] at hch
        refine ⟨ch, ?_, rfl⟩
        rcases (hmem cl).mp hx with rfl | hcl
        · exact hch.1
        · exact hch.2 cl hcl
    rw [key]
    split
    · rename_i hsym
      have hempty : (cs.foldl Cls.inter c).isEmpty = true := by
        rw [sym_def] at hsym; split at hsym
        · assumption
        · simp at hsym
      simp only [mem_lang_nil, false_iff, not_and]
      rintro ⟨ch, hch, -⟩ -
      rw [(Cls.isEmpty_iff _).mp hempty ch] at hch
      simp at hch
    · rw [mem_lang_cutOfList]
      simp only [mem_sortDedup, List.mem_cons, forall_eq_or_imp]
      rw [lang_smart_sym]
      simp

theorem mem_lang_cutL (rs : List RE) (w : List Char) :
    w ∈ lang (cutL rs) ↔ ∀ r ∈ rs, w ∈ lang r := by
  rw [cutL_eq, mem_lang_flatMap_cutToList]
  split
  · rename_i hnil
    simp only [mem_lang_nil, false_iff]
    intro h
    exact (mem_lang_nil (w := w)).mp (h RE.nil hnil)
  · rw [mem_lang_cutBody (fun x hx => (List.mem_filter.mp hx).2)]
    simp only [List.mem_filter, Function.comp_apply, Bool.not_eq_true']
    constructor
    · rintro ⟨h1, h2⟩ x hx
      by_cases hs : isSym x = true
      · exact h1 x ⟨hx, hs⟩
      · exact h2 x ⟨hx, by simpa using hs⟩
    · intro h
      exact ⟨fun x hx => h x hx.1, fun x hx => h x hx.1⟩

theorem lang_cut2 (r₁ r₂ : RE) : lang (cut2 r₁ r₂) = lang r₁ ⊓ lang r₂ := by
  refine Set.ext fun w => ?_
  show w ∈ lang (cutL [r₁, r₂]) ↔ (w ∈ lang r₁ ∧ w ∈ lang r₂)
  rw [mem_lang_cutL]
  simp

/-! ### `seq2` -/

theorem lang_seqOfList_append (l₁ l₂ : List RE) :
    lang (seqOfList (l₁ ++ l₂)) = lang (seqOfList l₁) * lang (seqOfList l₂) := by
  induction l₁ with
  | nil => simp [seqOfList, show lang RE.eps = 1 from rfl]
  | cons r rs ih =>
    rw [List.cons_append, seqOfList_cons, seqOfList_cons (l := rs)]
    by_cases hrs : rs = []
    · subst hrs
      simp only [List.nil_append, ite_true]
      cases l₂ with
      | nil => simp [seqOfList, show lang RE.eps = 1 from rfl]
      | cons a as => rw [if_neg (by simp)]; rfl
    · rw [if_neg hrs, if_neg (by simp [hrs])]
      show lang r * lang (seqOfList (rs ++ l₂)) = lang r * lang (seqOfList rs) * lang (seqOfList l₂)
      rw [ih, mul_assoc]

theorem lang_seqToList (r : RE) : lang (seqOfList (seqToList r)) = lang r := by
  induction r with
  | seq a b iha ihb =>
    rw [seqToList_seq, lang_seqOfList_append, iha, ihb]; rfl
  | _ => rfl

theorem seq2_eq (x y : RE) :
    seq2 x y =
      if x = .nil ∨ y = .nil then .nil
      else if x = .eps then y
      else if y = .eps then x
      else seqOfList (seqToList x ++ seqToList y) := by
  cases x <;> cases y <;> simp [seq2]

theorem lang_seq2 (r₁ r₂ : RE) : lang (seq2 r₁ r₂) = lang r₁ * lang r₂ := by
  rw [seq2_eq]
  split
  · rename_i h
    rcases h with h | h <;> subst h <;>
      simp [show lang RE.nil = 0 from rfl]
  · split
    · rename_i hx; subst hx; simp [show lang RE.eps = 1 from rfl]
    · split
      · rename_i hy; subst hy; simp [show lang RE.eps = 1 from rfl]
      · rw [lang_seqOfList_append, lang_seqToList, lang_seqToList]

/-! ### `rep_` and `not_` -/

theorem lang_rep_ (r : RE) : lang (rep_ r) = (lang r)∗ := by
  cases r with
  | nil =>
    rw [show rep_ RE.nil = .eps from rfl]
    simp [show lang RE.nil = 0 from rfl, show lang RE.eps = 1 from rfl]
  | eps =>
    rw [show rep_ RE.eps = .eps from rfl]
    simp [show lang RE.eps = 1 from rfl]
  | rep s =>
    rw [show rep_ (RE.rep s) = .rep s from rfl, lang_rep]
    exact (kstar_idem _).symm
  | not s =>
    rw [show rep_ (RE.not s) = (if RE.not s = top then top else RE.rep (.not s)) from rfl]
    split
    · rename_i h
      have hstar : (lang top)∗ = lang top := by
        apply Set.eq_of_subset_of_subset
        · intro x _
          exact mem_lang_top
        · intro x _
          refine Language.mem_kstar.2 ⟨[x], by simp, fun y hy => ?_⟩
          simp only [List.mem_singleton] at hy
          subst hy
          exact mem_lang_top
      rw [h, hstar]
    · rfl
  | _ => rfl

theorem lang_not_ (r : RE) : lang (not_ r) = (lang r)ᶜ := by
  cases r with
  | not s => rw [show not_ (RE.not s) = s from rfl]; exact (compl_compl _).symm
  | _ => rfl


@[simp] theorem mem_lang_alt2 {x y : RE} {w : List Char} :
    w ∈ lang (alt2 x y) ↔ w ∈ lang x ∨ w ∈ lang y := by
  rw [lang_alt2]; exact Iff.rfl

@[simp] theorem mem_lang_cut2 {x y : RE} {w : List Char} :
    w ∈ lang (cut2 x y) ↔ w ∈ lang x ∧ w ∈ lang y := by
  rw [lang_cut2]; exact Iff.rfl

theorem mem_lang_seq2 {x y : RE} {w : List Char} :
    w ∈ lang (seq2 x y) ↔ ∃ p ∈ lang x, ∃ q ∈ lang y, p ++ q = w := by
  rw [lang_seq2]; exact Language.mem_mul

theorem mem_lang_not_ {x : RE} {w : List Char} : w ∈ lang (not_ x) ↔ w ∉ lang x := by
  rw [lang_not_]; exact Iff.rfl

theorem mem_lang_rep_ {x : RE} {w : List Char} : w ∈ lang (rep_ x) ↔ w ∈ (lang x)∗ := by
  rw [lang_rep_]

theorem altMerged_sym (syms : List RE) : ∀ x ∈ altMerged syms, ∃ cl, x = sym cl := by
  unfold altMerged
  split
  · simp
  · split
    · simp
    · intro x hx
      simp only [List.mem_singleton] at hx
      exact ⟨_, hx⟩

theorem cutBody_eq_or (syms rest : List RE) :
    cutBody syms rest = RE.nil ∨
      ∃ l : List RE, (∀ x ∈ l, x ∈ rest ∨ ∃ cl, x = sym cl) ∧
        cutBody syms rest = cutOfList (sortDedup l) := by
  unfold cutBody
  split
  · exact Or.inr ⟨rest, fun _ hx => Or.inl hx, rfl⟩
  · split
    · exact Or.inl rfl
    · refine Or.inr ⟨_, fun x hx => ?_, rfl⟩
      rcases List.mem_cons.mp hx with rfl | h
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl h

/-- A class that has a member and a non-member is its own smart form. -/
theorem sym_eq_self {cl : Cls} (h1 : ∃ c, inCls c cl = true) (h2 : ∃ c, inCls c cl = false) :
    sym cl = .sym cl := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  rw [sym_def, if_neg, Cls.norm, if_neg]
  · intro hfull
    rw [(Cls.isFull_iff cl).mp hfull c2] at hc2
    simp at hc2
  · intro hemp
    rw [(Cls.isEmpty_iff cl).mp hemp c1] at hc1
    simp at hc1

end Smart

end Redgrep

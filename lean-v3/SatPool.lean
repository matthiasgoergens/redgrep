import ClosureSpan

/-!
# Building saturated pools

`ClosureSpan.lean` introduced the saturation predicate `Sat U P` and the two
spans `AltSpan`/`CutSpan`.  This file supplies the *constructors*:

* `sat_symBase` — the smallest saturated set: the three constants together
  with every `U`-bounded `sym` state;
* `sat_altPool` / `sat_cutPool` — a span is saturated as soon as its atom set
  is, the point being that all the derivative conditions only have to be
  checked on atoms (`altSpan_map` pushes them through the span);
* the bookkeeping lemmas that make the conditions on *non-concatenation*
  states (`suffix_mem`, `headD_mem`, `headW_mem`) free.
-/

namespace Redgrep

open Smart

/-! ### Chains of a non-concatenation state -/

@[simp] theorem seqOfList_nil' : seqOfList ([] : List RE) = .eps := rfl

@[simp] theorem seqOfList_singleton' (x : RE) : seqOfList [x] = x := rfl

theorem seqToList_of_notSeq {x : RE} (h : NotSeq x) :
    seqToList x = if x = .eps then [] else [x] := by
  cases x <;> simp_all [NotSeq]

theorem seqOfList_seqToList_notSeq {x : RE} (h : NotSeq x) : seqOfList (seqToList x) = x := by
  rw [seqToList_of_notSeq h]
  by_cases hx : x = .eps <;> simp [hx]

/-- Every chain suffix of a non-concatenation state is that state or `eps`. -/
theorem suffix_of_notSeq {x : RE} (h : NotSeq x) (i : Nat) :
    seqOfList ((seqToList x).drop i) = x ∨ seqOfList ((seqToList x).drop i) = .eps := by
  rw [seqToList_of_notSeq h]
  by_cases hx : x = .eps
  · subst hx; simp
  · rw [if_neg hx]
    cases i with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr (by simp)

/-- The chain decomposition of a non-concatenation state is trivial. -/
theorem head_of_notSeq {x h : RE} {rest : List RE} (hns : NotSeq x)
    (hx : seqToList x = h :: rest) : h = x ∧ rest = [] := by
  rw [seqToList_of_notSeq hns] at hx
  by_cases he : x = .eps
  · simp [he] at hx
  · rw [if_neg he, List.cons.injEq] at hx
    exact ⟨hx.1.symm, hx.2.symm⟩

/-! ### The base saturated set -/

/-- The three constants together with every `U`-bounded `sym` state. -/
def symBase (U : Finset Char) : Set RE := symSet U ∪ {RE.eps, RE.nil, top}

theorem symBase_finite (U : Finset Char) : (symBase U).Finite :=
  (symSet_finite U).union (Set.toFinite _)

theorem eps_mem_symBase (U : Finset Char) : (RE.eps) ∈ symBase U := by
  simp [symBase]

theorem nil_mem_symBase (U : Finset Char) : (RE.nil) ∈ symBase U := by
  simp [symBase]

theorem top_mem_symBase (U : Finset Char) : top ∈ symBase U := by
  simp [symBase]

theorem sym_mem_symBase {U : Finset Char} {cl : Cls} (h : ClsOK U cl) : sym cl ∈ symBase U :=
  Or.inl (sym_mem_symSet h)

theorem symBase_cases {U : Finset Char} {x : RE} (hx : x ∈ symBase U) :
    (∃ cl, ClsOK U cl ∧ x = .sym cl) ∨ x = .eps ∨ x = .nil ∨ x = top := by
  rcases hx with ⟨cl, hcl, rfl⟩ | hx
  · show (∃ cl', ClsOK U cl' ∧ sym cl = .sym cl') ∨ sym cl = .eps ∨ sym cl = .nil ∨ sym cl = top
    rw [sym_def]
    by_cases h : cl.isEmpty
    · rw [if_pos h]; exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl ⟨cl.norm, clsOK_norm hcl, by rw [if_neg h]⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    exact Or.inr hx

theorem symBase_notSeq {U : Finset Char} {x : RE} (hx : x ∈ symBase U) : NotSeq x := by
  rcases symBase_cases hx with ⟨cl, -, rfl⟩ | rfl | rfl | rfl <;> trivial

theorem symBase_notAlt {U : Finset Char} {x : RE} (hx : x ∈ symBase U) : NotAlt x := by
  rcases symBase_cases hx with ⟨cl, -, rfl⟩ | rfl | rfl | rfl <;> trivial

theorem symBase_notCut {U : Finset Char} {x : RE} (hx : x ∈ symBase U) : NotCut x := by
  rcases symBase_cases hx with ⟨cl, -, rfl⟩ | rfl | rfl | rfl <;> trivial

theorem deriv_mem_symBase (U : Finset Char) {x : RE} (hx : x ∈ symBase U) (c : Char) :
    deriv c x ∈ symBase U := by
  rcases symBase_cases hx with ⟨cl, -, rfl⟩ | rfl | rfl | rfl
  · rw [deriv_sym]
    split
    · exact eps_mem_symBase U
    · exact nil_mem_symBase U
  · rw [deriv_eps]; exact nil_mem_symBase U
  · rw [deriv_nil]; exact nil_mem_symBase U
  · rw [deriv_top]; exact top_mem_symBase U

theorem derivW_mem_symBase (U : Finset Char) {x : RE} (hx : x ∈ symBase U) (w : List Char) :
    derivW w x ∈ symBase U := by
  rcases symBase_cases hx with ⟨cl, hcl, rfl⟩ | rfl | rfl | rfl
  · match w with
    | [] => rw [derivW_sym_nil]; exact sym_mem_symBase hcl
    | [c] =>
      rw [derivW_sym_one]
      split
      · exact eps_mem_symBase U
      · exact nil_mem_symBase U
    | c :: d :: w => rw [derivW_sym_two]; exact nil_mem_symBase U
  · match w with
    | [] => rw [derivW_eps_nil]; exact eps_mem_symBase U
    | c :: w => rw [derivW_eps_cons]; exact nil_mem_symBase U
  · rw [derivW_nilRE]; exact nil_mem_symBase U
  · rw [derivW_top]; exact top_mem_symBase U

theorem atomSet_symBase (U : Finset Char) : AtomSet U (symBase U) := by
  refine ⟨symBase_finite U, eps_mem_symBase U, nil_mem_symBase U, top_mem_symBase U,
    fun cl h => sym_mem_symBase h, ?_, ?_, ?_⟩
  · intro cl hcl
    rcases symBase_cases hcl with ⟨cl', h, hx⟩ | h | h | h
    · rw [RE.sym.injEq] at hx; exact hx ▸ h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp [top])
  · intro x hx y hy
    rw [altToList_eq_singleton ?_ (symBase_notAlt hx), List.mem_singleton] at hy
    · exact hy ▸ hx
    · rintro rfl
      rw [altToList_nil] at hy
      simp at hy
  · intro x hx y hy
    by_cases hxt : x = top
    · subst hxt
      rw [show top = RE.not .nil from rfl, cutToList_not, if_pos rfl] at hy
      simp at hy
    · rw [cutToList_eq_singleton hxt (symBase_notCut hx), List.mem_singleton] at hy
      exact hy ▸ hx

theorem sat_symBase (U : Finset Char) : Sat U (symBase U) := by
  refine ⟨atomSet_symBase U, ?_, fun x hx c => deriv_mem_symBase U hx c,
    fun x hx w => derivW_mem_symBase U hx w, ?_, ?_, ?_⟩
  · intro y hy
    rcases symBase_cases hy with ⟨cl, -, hx⟩ | hx | hx | hx
    · exact absurd hx (by simp)
    · exact absurd hx (by simp)
    · exact absurd hx (by simp)
    · rw [show top = RE.not .nil from rfl, RE.not.injEq] at hx
      exact hx ▸ nil_mem_symBase U
  · intro x hx i
    rcases suffix_of_notSeq (symBase_notSeq hx) i with h | h
    · rw [h]; exact hx
    · rw [h]; exact eps_mem_symBase U
  · intro x hx h rest hrest c
    obtain ⟨rfl, rfl⟩ := head_of_notSeq (symBase_notSeq hx) hrest
    rw [List.append_nil, seqOfList_seqToList_notSeq (symBase_notSeq (deriv_mem_symBase U hx c))]
    exact deriv_mem_symBase U hx c
  · intro x hx h rest hrest w
    obtain ⟨rfl, rfl⟩ := head_of_notSeq (symBase_notSeq hx) hrest
    rw [List.append_nil, seqOfList_seqToList_notSeq (symBase_notSeq (derivW_mem_symBase U hx w))]
    exact derivW_mem_symBase U hx w

/-! ### Generic conditions for non-concatenation states -/

theorem suffix_mem_of_notSeq {P : Set RE} (heps : (RE.eps) ∈ P) {x : RE} (hx : x ∈ P)
    (hns : NotSeq x) (i : Nat) : seqOfList ((seqToList x).drop i) ∈ P := by
  rcases suffix_of_notSeq hns i with h | h
  · rw [h]; exact hx
  · rw [h]; exact heps

theorem headD_mem_of_notSeq {P : Set RE} {x : RE} (hx : x ∈ P) (hns : NotSeq x)
    (hdx : ∀ z ∈ P, ∀ c, deriv c z ∈ P)
    (hsuf0 : ∀ z ∈ P, seqOfList (seqToList z) ∈ P) :
    ∀ h rest, seqToList x = h :: rest → ∀ c, seqOfList (seqToList (deriv c h) ++ rest) ∈ P := by
  intro h rest hrest c
  obtain ⟨rfl, rfl⟩ := head_of_notSeq hns hrest
  rw [List.append_nil]
  exact hsuf0 _ (hdx _ hx c)

theorem headW_mem_of_notSeq {P : Set RE} {x : RE} (hx : x ∈ P) (hns : NotSeq x)
    (hwx : ∀ z ∈ P, ∀ w, derivW w z ∈ P)
    (hsuf0 : ∀ z ∈ P, seqOfList (seqToList z) ∈ P) :
    ∀ h rest, seqToList x = h :: rest → ∀ w, seqOfList (seqToList (derivW w h) ++ rest) ∈ P := by
  intro h rest hrest w
  obtain ⟨rfl, rfl⟩ := head_of_notSeq hns hrest
  rw [List.append_nil]
  exact hsuf0 _ (hwx _ hx w)

/-! ### Spans of a saturated atom set are saturated -/

theorem altSpan_cases {U : Finset Char} {A : Set RE} (hA : AtomSet U A) {x : RE}
    (hx : x ∈ AltSpan A) : x = top ∨ x = .nil ∨ (∃ p q, x = .alt p q) ∨ x ∈ A := by
  obtain ⟨L, hL, rfl⟩ := hx
  exact altL_shape hA hL

theorem cutSpan_cases {U : Finset Char} {A : Set RE} (hA : AtomSet U A) {x : RE}
    (hx : x ∈ CutSpan A) : x = top ∨ x = .nil ∨ (∃ p q, x = .cut p q) ∨ x ∈ A := by
  obtain ⟨L, hL, rfl⟩ := hx
  exact cutL_shape hA hL

theorem altPool_deriv {U : Finset Char} {A : Set RE} (hA : AtomSet U A)
    (hd : ∀ x ∈ A, ∀ c, deriv c x ∈ AltPool A) :
    ∀ x ∈ AltPool A, ∀ c, deriv c x ∈ AltPool A := by
  rintro x (hx | hx) c
  · exact hd x hx c
  · exact altSpan_map hA (deriv c) (fun p q => rfl) rfl (deriv_top c) (fun y hy => hd y hy c) x hx

theorem altPool_derivW {U : Finset Char} {A : Set RE} (hA : AtomSet U A)
    (hw : ∀ x ∈ A, ∀ w, derivW w x ∈ AltPool A) :
    ∀ x ∈ AltPool A, ∀ w, derivW w x ∈ AltPool A := by
  rintro x (hx | hx) w
  · exact hw x hx w
  · exact altSpan_map hA (derivW w) (derivW_alt w) (derivW_nilRE w) (derivW_top w)
      (fun y hy => hw y hy w) x hx

theorem cutPool_deriv {U : Finset Char} {A : Set RE} (hA : AtomSet U A)
    (hd : ∀ x ∈ A, ∀ c, deriv c x ∈ CutPool A) :
    ∀ x ∈ CutPool A, ∀ c, deriv c x ∈ CutPool A := by
  rintro x (hx | hx) c
  · exact hd x hx c
  · exact cutSpan_map hA (deriv c) (fun p q => rfl) rfl (deriv_top c) (fun y hy => hd y hy c) x hx

theorem cutPool_derivW {U : Finset Char} {A : Set RE} (hA : AtomSet U A)
    (hw : ∀ x ∈ A, ∀ w, derivW w x ∈ CutPool A) :
    ∀ x ∈ CutPool A, ∀ w, derivW w x ∈ CutPool A := by
  rintro x (hx | hx) w
  · exact hw x hx w
  · exact cutSpan_map hA (derivW w) (derivW_cut w) (derivW_nilRE w) (derivW_top w)
      (fun y hy => hw y hy w) x hx

theorem altPool_suffix {U : Finset Char} {A : Set RE} (hA : AtomSet U A)
    (hsuf : ∀ x ∈ A, ∀ i, seqOfList ((seqToList x).drop i) ∈ AltPool A) :
    ∀ x ∈ AltPool A, ∀ i, seqOfList ((seqToList x).drop i) ∈ AltPool A := by
  have heps : (RE.eps) ∈ AltPool A := Or.inl hA.eps_mem
  rintro x (hx | hx) i
  · exact hsuf x hx i
  · rcases altSpan_cases hA hx with rfl | rfl | ⟨p, q, rfl⟩ | hx'
    · exact suffix_mem_of_notSeq heps (Or.inl hA.top_mem) trivial i
    · exact suffix_mem_of_notSeq heps (Or.inl hA.nil_mem) trivial i
    · exact suffix_mem_of_notSeq (x := RE.alt p q) heps (Or.inr hx) trivial i
    · exact hsuf _ hx' i

theorem altPool_suffix_zero {U : Finset Char} {A : Set RE} (hA : AtomSet U A)
    (hsuf : ∀ x ∈ A, ∀ i, seqOfList ((seqToList x).drop i) ∈ AltPool A) :
    ∀ z ∈ AltPool A, seqOfList (seqToList z) ∈ AltPool A := by
  intro z hz
  have := altPool_suffix hA hsuf z hz 0
  rwa [List.drop_zero] at this

theorem cutPool_suffix {U : Finset Char} {A : Set RE} (hA : AtomSet U A)
    (hsuf : ∀ x ∈ A, ∀ i, seqOfList ((seqToList x).drop i) ∈ CutPool A) :
    ∀ x ∈ CutPool A, ∀ i, seqOfList ((seqToList x).drop i) ∈ CutPool A := by
  have heps : (RE.eps) ∈ CutPool A := Or.inl hA.eps_mem
  rintro x (hx | hx) i
  · exact hsuf x hx i
  · rcases cutSpan_cases hA hx with rfl | rfl | ⟨p, q, rfl⟩ | hx'
    · exact suffix_mem_of_notSeq heps (Or.inl hA.top_mem) trivial i
    · exact suffix_mem_of_notSeq heps (Or.inl hA.nil_mem) trivial i
    · exact suffix_mem_of_notSeq (x := RE.cut p q) heps (Or.inr hx) trivial i
    · exact hsuf _ hx' i

theorem cutPool_suffix_zero {U : Finset Char} {A : Set RE} (hA : AtomSet U A)
    (hsuf : ∀ x ∈ A, ∀ i, seqOfList ((seqToList x).drop i) ∈ CutPool A) :
    ∀ z ∈ CutPool A, seqOfList (seqToList z) ∈ CutPool A := by
  intro z hz
  have := cutPool_suffix hA hsuf z hz 0
  rwa [List.drop_zero] at this

theorem sat_altPool {U : Finset Char} {A : Set RE} (hA : AtomSet U A)
    (hnot : ∀ y : RE, (RE.not y) ∈ A → y ∈ AltPool A)
    (hd : ∀ x ∈ A, ∀ c, deriv c x ∈ AltPool A)
    (hw : ∀ x ∈ A, ∀ w, derivW w x ∈ AltPool A)
    (hsuf : ∀ x ∈ A, ∀ i, seqOfList ((seqToList x).drop i) ∈ AltPool A)
    (hhd : ∀ x ∈ A, ∀ h rest, seqToList x = h :: rest → ∀ c,
        seqOfList (seqToList (deriv c h) ++ rest) ∈ AltPool A)
    (hhw : ∀ x ∈ A, ∀ h rest, seqToList x = h :: rest → ∀ w,
        seqOfList (seqToList (derivW w h) ++ rest) ∈ AltPool A) :
    Sat U (AltPool A) := by
  have hAP : A ⊆ AltPool A := Set.subset_union_left
  have hfin : (AltPool A).Finite := hA.finite.union (altSpan_finite hA.finite)
  have heps : (RE.eps) ∈ AltPool A := hAP hA.eps_mem
  have hnil : (RE.nil) ∈ AltPool A := hAP hA.nil_mem
  have htop : top ∈ AltPool A := hAP hA.top_mem
  have hderiv := altPool_deriv hA hd
  have hderivW := altPool_derivW hA hw
  have hsuffix := altPool_suffix hA hsuf
  have hsuf0 := altPool_suffix_zero hA hsuf
  refine ⟨⟨hfin, heps, hnil, htop, fun cl h => hAP (hA.sym_mem cl h), ?_, ?_, ?_⟩,
    ?_, hderiv, hderivW, hsuffix, ?_, ?_⟩
  · rintro cl (hx | hx)
    · exact hA.sym_cls cl hx
    · rcases altSpan_cases hA hx with h | h | ⟨p, q, h⟩ | h
      · exact absurd h (by simp [top])
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · exact hA.sym_cls cl h
  · rintro x (hx | ⟨L, hL, rfl⟩) y hy
    · exact hAP (hA.alt_atom x hx y hy)
    · exact hAP (altL_mem_atoms hA hL y hy)
  · rintro x (hx | hx) y hy
    · exact hAP (hA.cut_atom x hx y hy)
    · rcases altSpan_cases hA hx with rfl | rfl | ⟨p, q, rfl⟩ | hx'
      · rw [show top = RE.not .nil from rfl, cutToList_not, if_pos rfl] at hy
        simp at hy
      · rw [cutToList_nil, List.mem_singleton] at hy
        subst hy; exact hnil
      · rw [cutToList_alt, List.mem_singleton] at hy
        subst hy; exact Or.inr hx
      · exact hAP (hA.cut_atom _ hx' y hy)
  · rintro y (hx | hx)
    · exact hnot y hx
    · rcases altSpan_cases hA hx with h | h | ⟨p, q, h⟩ | h
      · rw [show top = RE.not .nil from rfl, RE.not.injEq] at h
        subst h; exact hnil
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · exact hnot y h
  · rintro x (hx | hx) h rest hrest c
    · exact hhd x hx h rest hrest c
    · rcases altSpan_cases hA hx with rfl | rfl | ⟨p, q, rfl⟩ | hx'
      · exact headD_mem_of_notSeq htop trivial hderiv hsuf0 h rest hrest c
      · exact headD_mem_of_notSeq hnil trivial hderiv hsuf0 h rest hrest c
      · exact headD_mem_of_notSeq (x := RE.alt p q) (Or.inr hx) trivial hderiv hsuf0 h rest hrest c
      · exact hhd _ hx' h rest hrest c
  · rintro x (hx | hx) h rest hrest w
    · exact hhw x hx h rest hrest w
    · rcases altSpan_cases hA hx with rfl | rfl | ⟨p, q, rfl⟩ | hx'
      · exact headW_mem_of_notSeq htop trivial hderivW hsuf0 h rest hrest w
      · exact headW_mem_of_notSeq hnil trivial hderivW hsuf0 h rest hrest w
      · exact headW_mem_of_notSeq (x := RE.alt p q) (Or.inr hx) trivial hderivW hsuf0 h rest hrest w
      · exact hhw _ hx' h rest hrest w

theorem sat_cutPool {U : Finset Char} {A : Set RE} (hA : AtomSet U A)
    (hnot : ∀ y : RE, (RE.not y) ∈ A → y ∈ CutPool A)
    (hd : ∀ x ∈ A, ∀ c, deriv c x ∈ CutPool A)
    (hw : ∀ x ∈ A, ∀ w, derivW w x ∈ CutPool A)
    (hsuf : ∀ x ∈ A, ∀ i, seqOfList ((seqToList x).drop i) ∈ CutPool A)
    (hhd : ∀ x ∈ A, ∀ h rest, seqToList x = h :: rest → ∀ c,
        seqOfList (seqToList (deriv c h) ++ rest) ∈ CutPool A)
    (hhw : ∀ x ∈ A, ∀ h rest, seqToList x = h :: rest → ∀ w,
        seqOfList (seqToList (derivW w h) ++ rest) ∈ CutPool A) :
    Sat U (CutPool A) := by
  have hAP : A ⊆ CutPool A := Set.subset_union_left
  have hfin : (CutPool A).Finite := hA.finite.union (cutSpan_finite hA.finite)
  have heps : (RE.eps) ∈ CutPool A := hAP hA.eps_mem
  have hnil : (RE.nil) ∈ CutPool A := hAP hA.nil_mem
  have htop : top ∈ CutPool A := hAP hA.top_mem
  have hderiv := cutPool_deriv hA hd
  have hderivW := cutPool_derivW hA hw
  have hsuffix := cutPool_suffix hA hsuf
  have hsuf0 := cutPool_suffix_zero hA hsuf
  refine ⟨⟨hfin, heps, hnil, htop, fun cl h => hAP (hA.sym_mem cl h), ?_, ?_, ?_⟩,
    ?_, hderiv, hderivW, hsuffix, ?_, ?_⟩
  · rintro cl (hx | hx)
    · exact hA.sym_cls cl hx
    · rcases cutSpan_cases hA hx with h | h | ⟨p, q, h⟩ | h
      · exact absurd h (by simp [top])
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · exact hA.sym_cls cl h
  · rintro x (hx | hx) y hy
    · exact hAP (hA.alt_atom x hx y hy)
    · rcases cutSpan_cases hA hx with rfl | rfl | ⟨p, q, rfl⟩ | hx'
      · rw [show top = RE.not .nil from rfl, altToList_not, List.mem_singleton] at hy
        subst hy; exact htop
      · rw [altToList_nil] at hy
        simp at hy
      · rw [altToList_cut, List.mem_singleton] at hy
        subst hy; exact Or.inr hx
      · exact hAP (hA.alt_atom _ hx' y hy)
  · rintro x (hx | ⟨L, hL, rfl⟩) y hy
    · exact hAP (hA.cut_atom x hx y hy)
    · exact hAP (cutL_mem_atoms hA hL y hy)
  · rintro y (hx | hx)
    · exact hnot y hx
    · rcases cutSpan_cases hA hx with h | h | ⟨p, q, h⟩ | h
      · rw [show top = RE.not .nil from rfl, RE.not.injEq] at h
        subst h; exact hnil
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · exact hnot y h
  · rintro x (hx | hx) h rest hrest c
    · exact hhd x hx h rest hrest c
    · rcases cutSpan_cases hA hx with rfl | rfl | ⟨p, q, rfl⟩ | hx'
      · exact headD_mem_of_notSeq htop trivial hderiv hsuf0 h rest hrest c
      · exact headD_mem_of_notSeq hnil trivial hderiv hsuf0 h rest hrest c
      · exact headD_mem_of_notSeq (x := RE.cut p q) (Or.inr hx) trivial hderiv hsuf0 h rest hrest c
      · exact hhd _ hx' h rest hrest c
  · rintro x (hx | hx) h rest hrest w
    · exact hhw x hx h rest hrest w
    · rcases cutSpan_cases hA hx with rfl | rfl | ⟨p, q, rfl⟩ | hx'
      · exact headW_mem_of_notSeq htop trivial hderivW hsuf0 h rest hrest w
      · exact headW_mem_of_notSeq hnil trivial hderivW hsuf0 h rest hrest w
      · exact headW_mem_of_notSeq (x := RE.cut p q) (Or.inr hx) trivial hderivW hsuf0 h rest hrest w
      · exact hhw _ hx' h rest hrest w


end Redgrep

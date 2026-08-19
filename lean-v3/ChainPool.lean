import SatCases

/-!
# Saturated pools for concatenation chains

A derivative of a concatenation `a · b` is a *chain*: a (right-nested)
product whose tail is a suffix of the factor list of `b` and whose head part
is the factor list of a state of `a`.  This file makes that precise —
`chainStates Pa b` is the set of such chains — and proves that the smart
unions of those chains form a saturated pool (`sat_chainPool`), which is what
the `seq` and `rep` cases of the finiteness proof need.

The head part is kept as an explicit *list* (`Frags Pa`, the suffixes of the
factor lists of states of `a`) rather than as a regex: the smart constructor
`seq2` re-associates its arguments, so only the flattened factor list is
stable under the derivative recursion.
-/

namespace Redgrep

open Smart

/-! ### Fragments -/

/-- The suffixes of the factor lists of the states in `Pa`. -/
def Frags (Pa : Set RE) : Set (List RE) := {L | ∃ x ∈ Pa, ∃ i, L = (seqToList x).drop i}

theorem frags_shape {Pa : Set RE} {L : List RE} (hL : L ∈ Frags Pa) :
    ∀ z ∈ L, z ≠ .eps ∧ NotSeq z := by
  obtain ⟨x, -, i, rfl⟩ := hL
  intro z hz
  exact ⟨(mem_seqToList_notSeq z (List.mem_of_mem_drop hz)).2,
    (mem_seqToList_notSeq z (List.mem_of_mem_drop hz)).1⟩

theorem frags_seqToList {Pa : Set RE} {L : List RE} (hL : L ∈ Frags Pa) :
    seqToList (seqOfList L) = L :=
  seqToList_seqOfList (frags_shape hL)

theorem frags_drop {Pa : Set RE} {L : List RE} (hL : L ∈ Frags Pa) (n : Nat) :
    L.drop n ∈ Frags Pa := by
  obtain ⟨x, hx, i, rfl⟩ := hL
  exact ⟨x, hx, i + n, by rw [List.drop_drop]⟩

theorem frags_of_mem {Pa : Set RE} {x : RE} (hx : x ∈ Pa) : seqToList x ∈ Frags Pa :=
  ⟨x, hx, 0, by rw [List.drop_zero]⟩

theorem frags_nil {U : Finset Char} {Pa : Set RE} (hPa : Sat U Pa) : ([] : List RE) ∈ Frags Pa :=
  ⟨RE.eps, hPa.eps_mem, 0, rfl⟩

theorem frags_mem {U : Finset Char} {Pa : Set RE} (hPa : Sat U Pa) {L : List RE}
    (hL : L ∈ Frags Pa) : seqOfList L ∈ Pa := by
  obtain ⟨x, hx, i, rfl⟩ := hL
  exact hPa.suffix_mem x hx i

/-- One head-derivative step on a fragment stays a fragment. -/
theorem frags_head_step {U : Finset Char} {Pa : Set RE} (hPa : Sat U Pa) {h : RE} {L : List RE}
    (hK : h :: L ∈ Frags Pa) (c : Char) : seqToList (deriv c h) ++ L ∈ Frags Pa := by
  have hy : seqOfList (seqToList (deriv c h) ++ L) ∈ Pa :=
    hPa.headD_mem _ (frags_mem hPa hK) h L (frags_seqToList hK) c
  have := frags_of_mem hy
  rwa [seqToList_seqOfList ?_] at this
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact ⟨(mem_seqToList_notSeq z hz).2, (mem_seqToList_notSeq z hz).1⟩
  · exact frags_shape hK z (List.mem_cons_of_mem h hz)

theorem frags_head_stepW {U : Finset Char} {Pa : Set RE} (hPa : Sat U Pa) {h : RE} {L : List RE}
    (hK : h :: L ∈ Frags Pa) (w : List Char) : seqToList (derivW w h) ++ L ∈ Frags Pa := by
  have hy : seqOfList (seqToList (derivW w h) ++ L) ∈ Pa :=
    hPa.headW_mem _ (frags_mem hPa hK) h L (frags_seqToList hK) w
  have := frags_of_mem hy
  rwa [seqToList_seqOfList ?_] at this
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact ⟨(mem_seqToList_notSeq z hz).2, (mem_seqToList_notSeq z hz).1⟩
  · exact frags_shape hK z (List.mem_cons_of_mem h hz)

theorem frags_finite {Pa : Set RE} (hPa : Pa.Finite) : (Frags Pa).Finite := by
  refine Set.Finite.subset (hPa.biUnion (fun x _ => (seqToList x).tails.finite_toSet)) ?_
  rintro L ⟨x, hx, i, rfl⟩
  exact Set.mem_biUnion hx ((List.mem_tails _ _).mpr (List.drop_suffix i _))

/-! ### Chain states -/

/-- A state of the concatenation chain: a fragment of a state of `a`
followed by a suffix of the factor list of `b`. -/
def chainStates (Pa : Set RE) (b : RE) : Set RE :=
  {y | ∃ K ∈ Frags Pa, ∃ j, y = seqOfList (K ++ (seqToList b).drop j)}

theorem chainStates_finite {Pa : Set RE} (hPa : Pa.Finite) (b : RE) :
    (chainStates Pa b).Finite := by
  refine Set.Finite.subset (Set.Finite.image (fun p : List RE × List RE => seqOfList (p.1 ++ p.2))
    ((frags_finite hPa).prod (seqToList b).tails.finite_toSet)) ?_
  rintro y ⟨K, hK, j, rfl⟩
  exact ⟨(K, (seqToList b).drop j), ⟨hK, (List.mem_tails _ _).mpr (List.drop_suffix j _)⟩, rfl⟩

theorem mem_chainStates {Pa : Set RE} {b : RE} {K : List RE} (hK : K ∈ Frags Pa) (j : Nat) :
    seqOfList (K ++ (seqToList b).drop j) ∈ chainStates Pa b := ⟨K, hK, j, rfl⟩

theorem mem_chainStates_zero {Pa : Set RE} {b : RE} {K : List RE} (hK : K ∈ Frags Pa) :
    seqOfList (K ++ seqToList b) ∈ chainStates Pa b := ⟨K, hK, 0, by rw [List.drop_zero]⟩

/-- The elements of a chain list are proper factors. -/
theorem chain_list_shape {Pa : Set RE} {b : RE} {K : List RE} (hK : K ∈ Frags Pa) (j : Nat) :
    ∀ z ∈ K ++ (seqToList b).drop j, z ≠ .eps ∧ NotSeq z := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact frags_shape hK z hz
  · have := mem_seqToList_notSeq z (List.mem_of_mem_drop hz)
    exact ⟨this.2, this.1⟩

theorem chain_seqToList {Pa : Set RE} {b : RE} {K : List RE} (hK : K ∈ Frags Pa) (j : Nat) :
    seqToList (seqOfList (K ++ (seqToList b).drop j)) = K ++ (seqToList b).drop j :=
  seqToList_seqOfList (chain_list_shape hK j)

theorem seqOfList_ne_eps {L : List RE} (hne : L ≠ []) (h : ∀ x ∈ L, x ≠ .eps) :
    seqOfList L ≠ .eps := by
  cases L with
  | nil => exact absurd rfl hne
  | cons x xs =>
    rw [Smart.seqOfList_cons]
    split
    · exact h x (by simp)
    · simp

theorem seqToList_bsuffix (b : RE) (j : Nat) :
    seqToList (seqOfList ((seqToList b).drop j)) = (seqToList b).drop j :=
  seqToList_seqOfList fun z hz =>
    ⟨(mem_seqToList_notSeq z (List.mem_of_mem_drop hz)).2,
      (mem_seqToList_notSeq z (List.mem_of_mem_drop hz)).1⟩

/-! ### The pool -/

/-- The atoms of the chain pool: the chain states, the states of the head
regex, and the extra states `E` supplied for the tail regex. -/
def chainAtoms (Pa E : Set RE) (b : RE) : Set RE := chainStates Pa b ∪ Pa ∪ E

/-- The chain pool: smart unions of chain atoms. -/
def chainPool (Pa E : Set RE) (b : RE) : Set RE := AltPool (chainAtoms Pa E b)

theorem mem_chainAtoms {Pa E : Set RE} {b : RE} (x : RE) :
    x ∈ chainAtoms Pa E b ↔ (x ∈ chainStates Pa b ∨ x ∈ Pa ∨ x ∈ E) := by
  simp only [chainAtoms, Set.mem_union]
  tauto

/-- The four shapes a chain state can have. -/
theorem chain_cases {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hbE : ∀ j, seqOfList ((seqToList b).drop j) ∈ E) {K : List RE} (hK : K ∈ Frags Pa)
    (j : Nat) :
    seqOfList (K ++ (seqToList b).drop j) = .eps ∨
      seqOfList (K ++ (seqToList b).drop j) ∈ Pa ∨
      seqOfList (K ++ (seqToList b).drop j) ∈ E ∨
      ∃ p q, seqOfList (K ++ (seqToList b).drop j) = .seq p q := by
  cases K with
  | nil => exact Or.inr (Or.inr (Or.inl (by rw [List.nil_append]; exact hbE j)))
  | cons h K' =>
    rw [List.cons_append, Smart.seqOfList_cons]
    by_cases hL : K' ++ (seqToList b).drop j = []
    · rw [if_pos hL]
      refine Or.inr (Or.inl ?_)
      have := frags_mem hPa hK
      rw [Smart.seqOfList_cons] at this
      rw [if_pos (List.append_eq_nil_iff.mp hL).1] at this
      exact this
    · exact Or.inr (Or.inr (Or.inr ⟨h, _, by rw [if_neg hL]⟩))

theorem chainStates_cases {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hbE : ∀ j, seqOfList ((seqToList b).drop j) ∈ E) {x : RE} (hx : x ∈ chainStates Pa b) :
    x = .eps ∨ x ∈ Pa ∨ x ∈ E ∨ ∃ p q, x = .seq p q := by
  obtain ⟨K, hK, j, rfl⟩ := hx
  exact chain_cases hPa hbE hK j

theorem chainAtoms_atomSet {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hEfin : E.Finite) (hbE : ∀ j, seqOfList ((seqToList b).drop j) ∈ E)
    (hEalt : ∀ x ∈ E, ∀ y ∈ altToList x, y ∈ chainAtoms Pa E b)
    (hEcut : ∀ x ∈ E, ∀ y ∈ cutToList x, y ∈ chainAtoms Pa E b)
    (hEsym : ∀ cl, (RE.sym cl) ∈ E → ClsOK U cl) :
    AtomSet U (chainAtoms Pa E b) := by
  have hPaA : Pa ⊆ chainAtoms Pa E b := fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inl hx))
  have hEA : E ⊆ chainAtoms Pa E b := fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inr hx))
  refine ⟨((chainStates_finite hPa.finite b).union hPa.finite).union hEfin,
    hPaA hPa.eps_mem, hPaA hPa.nil_mem, hPaA hPa.top_mem,
    fun cl h => hPaA (hPa.sym_mem cl h), ?_, ?_, ?_⟩
  · intro cl hcl
    rcases (mem_chainAtoms _).mp hcl with hx | hx | hx
    · rcases chainStates_cases hPa hbE hx with h | h | h | ⟨p, q, h⟩
      · exact absurd h (by simp)
      · exact hPa.sym_cls cl h
      · exact hEsym cl h
      · exact absurd h (by simp)
    · exact hPa.sym_cls cl hx
    · exact hEsym cl hx
  · intro x hx y hy
    rcases (mem_chainAtoms x).mp hx with hx' | hx' | hx'
    · rcases chainStates_cases hPa hbE hx' with h | h | h | ⟨p, q, h⟩
      · subst h
        rw [altToList_eps, List.mem_singleton] at hy
        subst hy; exact hPaA hPa.eps_mem
      · exact hPaA (hPa.alt_atom x h y hy)
      · exact hEalt x h y hy
      · rw [h, altToList_seq, List.mem_singleton] at hy
        subst hy; rw [← h]; exact hx
    · exact hPaA (hPa.alt_atom x hx' y hy)
    · exact hEalt x hx' y hy
  · intro x hx y hy
    rcases (mem_chainAtoms x).mp hx with hx' | hx' | hx'
    · rcases chainStates_cases hPa hbE hx' with h | h | h | ⟨p, q, h⟩
      · subst h
        rw [cutToList_eps, List.mem_singleton] at hy
        subst hy; exact hPaA hPa.eps_mem
      · exact hPaA (hPa.cut_atom x h y hy)
      · exact hEcut x h y hy
      · rw [h, cutToList_seq, List.mem_singleton] at hy
        subst hy; rw [← h]; exact hx
    · exact hPaA (hPa.cut_atom x hx' y hy)
    · exact hEcut x hx' y hy

/-- Prefixing a chain by the factors of `z` stays a chain. -/
theorem chain_seq2_mem {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    {z : RE} {K : List RE} {j : Nat}
    (hzK : seqToList z ++ K ∈ Frags Pa) (hK : K ∈ Frags Pa)
    (hLne : K ++ (seqToList b).drop j ≠ []) :
    seq2 z (seqOfList (K ++ (seqToList b).drop j)) ∈ chainAtoms Pa E b := by
  have hPaA : Pa ⊆ chainAtoms Pa E b := fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inl hx))
  have hchain : ∀ K' ∈ Frags Pa, ∀ j', seqOfList (K' ++ (seqToList b).drop j') ∈ chainAtoms Pa E b :=
    fun K' hK' j' => (mem_chainAtoms _).mpr (Or.inl (mem_chainStates hK' j'))
  rw [seq2_eq]
  split
  · exact hPaA hPa.nil_mem
  · split
    · exact hchain K hK j
    · split
      · rename_i hne
        exact absurd hne (seqOfList_ne_eps hLne fun x hx => (chain_list_shape hK j x hx).1)
      · rw [chain_seqToList hK j, ← List.append_assoc]
        exact hchain _ hzK j

/-! ### Derivatives of chain states -/

theorem chain_deriv_mem {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hAtom : AtomSet U (chainAtoms Pa E b))
    (hbE : ∀ j, seqOfList ((seqToList b).drop j) ∈ E)
    (hEd : ∀ x ∈ E, ∀ c, deriv c x ∈ chainPool Pa E b) :
    ∀ K ∈ Frags Pa, ∀ (j : Nat) (c : Char),
      deriv c (seqOfList (K ++ (seqToList b).drop j)) ∈ chainPool Pa E b := by
  have hPaA : Pa ⊆ chainAtoms Pa E b := fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inl hx))
  have hAP : chainAtoms Pa E b ⊆ chainPool Pa E b := Set.subset_union_left
  have halt2 : ∀ x y : RE, x ∈ chainPool Pa E b → y ∈ chainPool Pa E b →
      alt2 x y ∈ chainPool Pa E b := by
    intro x y hx hy
    refine Or.inr (altL_mem_altSpan hAtom ?_)
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hy
      · simp at hz
  intro K
  induction K with
  | nil =>
    intro _ j c
    rw [List.nil_append]
    exact hEd _ (hbE j) c
  | cons h K' ih =>
    intro hK j c
    have hK' : K' ∈ Frags Pa := by
      have := frags_drop hK 1
      rwa [List.drop_one, List.tail_cons] at this
    by_cases hL : K' ++ (seqToList b).drop j = []
    · have hh : h ∈ Pa := by
        have := frags_mem hPa hK
        rw [Smart.seqOfList_cons, if_pos (List.append_eq_nil_iff.mp hL).1] at this
        exact this
      rw [List.cons_append, hL]
      exact hAP (hPaA (hPa.deriv_mem h hh c))
    · rw [List.cons_append, Smart.seqOfList_cons, if_neg hL, deriv_seq]
      have hseq := chain_seq2_mem (E := E) hPa (frags_head_step hPa hK c) hK' hL
      split
      · exact halt2 _ _ (hAP hseq) (ih hK' j c)
      · exact hAP hseq

theorem chain_derivW_mem {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hAtom : AtomSet U (chainAtoms Pa E b))
    (hbE : ∀ j, seqOfList ((seqToList b).drop j) ∈ E)
    (hEw : ∀ x ∈ E, ∀ w, derivW w x ∈ chainPool Pa E b) :
    ∀ K ∈ Frags Pa, ∀ (j : Nat) (w : List Char),
      derivW w (seqOfList (K ++ (seqToList b).drop j)) ∈ chainPool Pa E b := by
  have hPaA : Pa ⊆ chainAtoms Pa E b := fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inl hx))
  have hAP : chainAtoms Pa E b ⊆ chainPool Pa E b := Set.subset_union_left
  have haltL : ∀ L : List RE, (∀ y ∈ L, y ∈ chainPool Pa E b) → altL L ∈ chainPool Pa E b :=
    fun L hL => Or.inr (altL_mem_altSpan hAtom hL)
  have halt2 : ∀ x y : RE, x ∈ chainPool Pa E b → y ∈ chainPool Pa E b →
      alt2 x y ∈ chainPool Pa E b := by
    intro x y hx hy
    refine haltL [x, y] ?_
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hy
      · simp at hz
  intro K
  induction K with
  | nil =>
    intro _ j w
    rw [List.nil_append]
    exact hEw _ (hbE j) w
  | cons h K' ih =>
    intro hK j w
    have hK' : K' ∈ Frags Pa := by
      have := frags_drop hK 1
      rwa [List.drop_one, List.tail_cons] at this
    by_cases hL : K' ++ (seqToList b).drop j = []
    · have hh : h ∈ Pa := by
        have := frags_mem hPa hK
        rw [Smart.seqOfList_cons, if_pos (List.append_eq_nil_iff.mp hL).1] at this
        exact this
      rw [List.cons_append, hL]
      exact hAP (hPaA (hPa.derivW_mem h hh w))
    · rw [List.cons_append, Smart.seqOfList_cons, if_neg hL, derivW_seq]
      refine halt2 _ _ (hAP (chain_seq2_mem (E := E) hPa (frags_head_stepW hPa hK w) hK' hL))
        (haltL _ ?_)
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨i, -, rfl⟩ := hy
      split
      · exact ih hK' j (w.drop i)
      · exact hAP (hPaA hPa.nil_mem)

/-! ### The chain pool is saturated -/

theorem chainAtoms_deriv {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hAtom : AtomSet U (chainAtoms Pa E b))
    (hbE : ∀ j, seqOfList ((seqToList b).drop j) ∈ E)
    (hEd : ∀ x ∈ E, ∀ c, deriv c x ∈ chainPool Pa E b) :
    ∀ x ∈ chainAtoms Pa E b, ∀ c, deriv c x ∈ chainPool Pa E b := by
  intro x hx c
  rcases (mem_chainAtoms x).mp hx with ⟨K, hK, j, rfl⟩ | hx' | hx'
  · exact chain_deriv_mem hPa hAtom hbE hEd K hK j c
  · exact Set.subset_union_left
      ((mem_chainAtoms (deriv c x)).mpr (Or.inr (Or.inl (hPa.deriv_mem x hx' c))))
  · exact hEd x hx' c

theorem chainAtoms_derivW {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hAtom : AtomSet U (chainAtoms Pa E b))
    (hbE : ∀ j, seqOfList ((seqToList b).drop j) ∈ E)
    (hEw : ∀ x ∈ E, ∀ w, derivW w x ∈ chainPool Pa E b) :
    ∀ x ∈ chainAtoms Pa E b, ∀ w, derivW w x ∈ chainPool Pa E b := by
  intro x hx w
  rcases (mem_chainAtoms x).mp hx with ⟨K, hK, j, rfl⟩ | hx' | hx'
  · exact chain_derivW_mem hPa hAtom hbE hEw K hK j w
  · exact Set.subset_union_left
      ((mem_chainAtoms (derivW w x)).mpr (Or.inr (Or.inl (hPa.derivW_mem x hx' w))))
  · exact hEw x hx' w

theorem chainAtoms_suffix {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hEsuf : ∀ x ∈ E, ∀ i, seqOfList ((seqToList x).drop i) ∈ chainPool Pa E b) :
    ∀ x ∈ chainAtoms Pa E b, ∀ i, seqOfList ((seqToList x).drop i) ∈ chainPool Pa E b := by
  have hAP : chainAtoms Pa E b ⊆ chainPool Pa E b := Set.subset_union_left
  intro x hx i
  rcases (mem_chainAtoms x).mp hx with ⟨K, hK, j, rfl⟩ | hx' | hx'
  · rw [chain_seqToList hK j, List.drop_append, List.drop_drop]
    exact hAP ((mem_chainAtoms _).mpr (Or.inl (mem_chainStates (frags_drop hK i) _)))
  · exact hAP ((mem_chainAtoms _).mpr (Or.inr (Or.inl (hPa.suffix_mem x hx' i))))
  · exact hEsuf x hx' i

/-- Pool-level closure under one-character derivatives. -/
theorem chainPool_deriv {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hAtom : AtomSet U (chainAtoms Pa E b))
    (hbE : ∀ j, seqOfList ((seqToList b).drop j) ∈ E)
    (hEd : ∀ x ∈ E, ∀ c, deriv c x ∈ chainPool Pa E b) :
    ∀ x ∈ chainPool Pa E b, ∀ c, deriv c x ∈ chainPool Pa E b :=
  altPool_deriv hAtom (chainAtoms_deriv hPa hAtom hbE hEd)

/-- Pool-level closure under word derivatives. -/
theorem chainPool_derivW {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hAtom : AtomSet U (chainAtoms Pa E b))
    (hbE : ∀ j, seqOfList ((seqToList b).drop j) ∈ E)
    (hEw : ∀ x ∈ E, ∀ w, derivW w x ∈ chainPool Pa E b) :
    ∀ x ∈ chainPool Pa E b, ∀ w, derivW w x ∈ chainPool Pa E b :=
  altPool_derivW hAtom (chainAtoms_derivW hPa hAtom hbE hEw)

/-- Pool-level closure under re-associating a state's factor list. -/
theorem chainPool_suffix_zero {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hAtom : AtomSet U (chainAtoms Pa E b))
    (hEsuf : ∀ x ∈ E, ∀ i, seqOfList ((seqToList x).drop i) ∈ chainPool Pa E b) :
    ∀ z ∈ chainPool Pa E b, seqOfList (seqToList z) ∈ chainPool Pa E b :=
  altPool_suffix_zero hAtom (chainAtoms_suffix hPa hEsuf)

theorem sat_chainPool {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hEfin : E.Finite) (hbE : ∀ j, seqOfList ((seqToList b).drop j) ∈ E)
    (hEalt : ∀ x ∈ E, ∀ y ∈ altToList x, y ∈ chainAtoms Pa E b)
    (hEcut : ∀ x ∈ E, ∀ y ∈ cutToList x, y ∈ chainAtoms Pa E b)
    (hEsym : ∀ cl, (RE.sym cl) ∈ E → ClsOK U cl)
    (hEnot : ∀ y : RE, (RE.not y) ∈ E → y ∈ chainPool Pa E b)
    (hEd : ∀ x ∈ E, ∀ c, deriv c x ∈ chainPool Pa E b)
    (hEw : ∀ x ∈ E, ∀ w, derivW w x ∈ chainPool Pa E b)
    (hEsuf : ∀ x ∈ E, ∀ i, seqOfList ((seqToList x).drop i) ∈ chainPool Pa E b)
    (hEhd : ∀ x ∈ E, ∀ h rest, seqToList x = h :: rest → ∀ c,
        seqOfList (seqToList (deriv c h) ++ rest) ∈ chainPool Pa E b)
    (hEhw : ∀ x ∈ E, ∀ h rest, seqToList x = h :: rest → ∀ w,
        seqOfList (seqToList (derivW w h) ++ rest) ∈ chainPool Pa E b) :
    Sat U (chainPool Pa E b) := by
  have hAtom := chainAtoms_atomSet hPa hEfin hbE hEalt hEcut hEsym
  have hPaA : Pa ⊆ chainAtoms Pa E b := fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inl hx))
  have hAP : chainAtoms Pa E b ⊆ chainPool Pa E b := Set.subset_union_left
  have hchain : ∀ K ∈ Frags Pa, ∀ j,
      seqOfList (K ++ (seqToList b).drop j) ∈ chainAtoms Pa E b :=
    fun K hK j => (mem_chainAtoms _).mpr (Or.inl (mem_chainStates hK j))
  have hd := chainAtoms_deriv hPa hAtom hbE hEd
  have hw := chainAtoms_derivW hPa hAtom hbE hEw
  have hsuf := chainAtoms_suffix hPa hEsuf
  show Sat U (AltPool (chainAtoms Pa E b))
  refine sat_altPool hAtom ?_ hd hw hsuf ?_ ?_
  · intro y hy
    rcases (mem_chainAtoms _).mp hy with hx' | hx' | hx'
    · rcases chainStates_cases hPa hbE hx' with h | h | h | ⟨p, q, h⟩
      · exact absurd h (by simp)
      · exact hAP (hPaA (hPa.not_body y h))
      · exact hEnot y h
      · exact absurd h (by simp)
    · exact hAP (hPaA (hPa.not_body y hx'))
    · exact hEnot y hx'
  · intro x hx h rest hrest c
    rcases (mem_chainAtoms x).mp hx with ⟨K, hK, j, rfl⟩ | hx' | hx'
    · rw [chain_seqToList hK j] at hrest
      cases K with
      | nil =>
        rw [List.nil_append] at hrest
        exact hEhd _ (hbE j) h rest (by rw [seqToList_bsuffix]; exact hrest) c
      | cons h' K'' =>
        rw [List.cons_append, List.cons.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        rw [← List.append_assoc]
        exact hAP (hchain _ (frags_head_step hPa hK c) j)
    · exact hAP (hPaA (hPa.headD_mem x hx' h rest hrest c))
    · exact hEhd x hx' h rest hrest c
  · intro x hx h rest hrest w
    rcases (mem_chainAtoms x).mp hx with ⟨K, hK, j, rfl⟩ | hx' | hx'
    · rw [chain_seqToList hK j] at hrest
      cases K with
      | nil =>
        rw [List.nil_append] at hrest
        exact hEhw _ (hbE j) h rest (by rw [seqToList_bsuffix]; exact hrest) w
      | cons h' K'' =>
        rw [List.cons_append, List.cons.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        rw [← List.append_assoc]
        exact hAP (hchain _ (frags_head_stepW hPa hK w) j)
    · exact hAP (hPaA (hPa.headW_mem x hx' h rest hrest w))
    · exact hEhw x hx' h rest hrest w


/-! ### Prefixing the bare tail regex -/

theorem chainPool_altL {U : Finset Char} {Pa E : Set RE} {b : RE}
    (hAtom : AtomSet U (chainAtoms Pa E b)) (L : List RE)
    (hL : ∀ y ∈ L, y ∈ chainPool Pa E b) : altL L ∈ chainPool Pa E b :=
  Or.inr (altL_mem_altSpan hAtom hL)

theorem chainPool_alt2 {U : Finset Char} {Pa E : Set RE} {b : RE}
    (hAtom : AtomSet U (chainAtoms Pa E b)) {x y : RE}
    (hx : x ∈ chainPool Pa E b) (hy : y ∈ chainPool Pa E b) : alt2 x y ∈ chainPool Pa E b := by
  refine chainPool_altL hAtom [x, y] ?_
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hx
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact hy
    · simp at hz

/-- `seq2 z b` for a state `z` of the head regex and the *raw* tail regex. -/
theorem chain_seq2_tail {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    (hbE : b ∈ E) {z : RE} (hz : z ∈ Pa) : seq2 z b ∈ chainAtoms Pa E b := by
  have hPaA : Pa ⊆ chainAtoms Pa E b := fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inl hx))
  rw [seq2_eq]
  split
  · exact hPaA hPa.nil_mem
  · split
    · exact (mem_chainAtoms _).mpr (Or.inr (Or.inr hbE))
    · split
      · exact hPaA hz
      · rw [show seqToList z ++ seqToList b = seqToList z ++ (seqToList b).drop 0 by
          rw [List.drop_zero]]
        exact (mem_chainAtoms _).mpr (Or.inl (mem_chainStates (frags_of_mem hz) 0))

/-- The re-associated form of `seq2 z b` is a chain atom as well. -/
theorem chain_seq2_tail_reassoc {U : Finset Char} {Pa E : Set RE} {b : RE} (hPa : Sat U Pa)
    {z : RE} (hz : z ∈ Pa) :
    seqOfList (seqToList (seq2 z b)) ∈ chainAtoms Pa E b := by
  have hPaA : Pa ⊆ chainAtoms Pa E b := fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inl hx))
  rw [seq2_eq]
  split
  · exact hPaA hPa.nil_mem
  · split
    · rw [show seqToList b = (seqToList b).drop 0 by rw [List.drop_zero],
        show ((seqToList b).drop 0) = [] ++ (seqToList b).drop 0 by rw [List.nil_append]]
      exact (mem_chainAtoms _).mpr (Or.inl (mem_chainStates (frags_nil hPa) 0))
    · split
      · have := hPa.suffix_mem z hz 0
        rw [List.drop_zero] at this
        exact hPaA this
      · rw [seqToList_seqOfList (L := seqToList z ++ seqToList b) ?_]
        · rw [show seqToList z ++ seqToList b = seqToList z ++ (seqToList b).drop 0 by
            rw [List.drop_zero]]
          exact (mem_chainAtoms _).mpr (Or.inl (mem_chainStates (frags_of_mem hz) 0))
        · intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact ⟨(mem_seqToList_notSeq y hy).2, (mem_seqToList_notSeq y hy).1⟩
          · exact ⟨(mem_seqToList_notSeq y hy).2, (mem_seqToList_notSeq y hy).1⟩

end Redgrep

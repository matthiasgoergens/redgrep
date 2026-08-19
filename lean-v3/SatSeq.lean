import ChainPool

/-!
# Saturated pools for `seq` and `rep`

The two remaining constructors, both instances of the chain machinery of
`ChainPool.lean`:

* for `a · b` the tail regex is `b` itself and the extra atoms are the states
  of `b` (plus the raw term `a · b`, whose factor list is the concatenation of
  the two factor lists but which is not itself right-nested);
* for `a∗` the tail regex is `rep_ a` and the only extra atom is `a∗`: a
  derivative of `a∗` is `(d a) · a∗`, again a chain over the states of `a`.
-/

namespace Redgrep

open Smart

/-! ### The smart star -/

theorem rep_mem_cases (a : RE) :
    rep_ a = .eps ∨ rep_ a = top ∨ rep_ a = a ∨ rep_ a = .rep a := by
  cases a with
  | nil => exact Or.inl rfl
  | eps => exact Or.inl rfl
  | rep r => exact Or.inr (Or.inr (Or.inl rfl))
  | _ =>
    all_goals
      (unfold rep_
       simp only []
       split
       · exact Or.inr (Or.inl rfl)
       · exact Or.inr (Or.inr (Or.inr rfl)))

theorem rep_notSeq (a : RE) : NotSeq (rep_ a) := by
  cases a with
  | nil => trivial
  | eps => trivial
  | rep r => trivial
  | _ =>
    all_goals
      (unfold rep_
       simp only []
       split
       · trivial
       · trivial)

/-! ### Concatenation -/

theorem exists_sat_seq {U : Finset Char} {Pa Pb : Set RE} {a b : RE}
    (hPa : Sat U Pa) (hPb : Sat U Pb) (ha : a ∈ Pa) (hb : b ∈ Pb) :
    ∃ P, Sat U P ∧ (RE.seq a b) ∈ P := by
  classical
  set E : Set RE := Pb ∪ {RE.seq a b} with hEdef
  have hmemE : ∀ x : RE, x ∈ E ↔ (x ∈ Pb ∨ x = .seq a b) := by
    intro x; simp [hEdef, or_comm]
  have hrE : (RE.seq a b) ∈ E := (hmemE _).mpr (Or.inr rfl)
  have hPbE : Pb ⊆ E := fun x hx => (hmemE x).mpr (Or.inl hx)
  have hEA : E ⊆ chainAtoms Pa E b := fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inr hx))
  have hPaA : Pa ⊆ chainAtoms Pa E b := fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inl hx))
  have hCA : chainStates Pa b ⊆ chainAtoms Pa E b :=
    fun x hx => (mem_chainAtoms x).mpr (Or.inl hx)
  have hAP : chainAtoms Pa E b ⊆ chainPool Pa E b := Set.subset_union_left
  have hEfin : E.Finite := hPb.finite.union (Set.finite_singleton _)
  have hbE : ∀ j, seqOfList ((seqToList b).drop j) ∈ E := fun j => hPbE (hPb.suffix_mem b hb j)
  have hEalt : ∀ x ∈ E, ∀ y ∈ altToList x, y ∈ chainAtoms Pa E b := by
    intro x hx y hy
    rcases (hmemE x).mp hx with h | rfl
    · exact hEA (hPbE (hPb.alt_atom x h y hy))
    · rw [altToList_seq, List.mem_singleton] at hy
      subst hy; exact hEA hrE
  have hEcut : ∀ x ∈ E, ∀ y ∈ cutToList x, y ∈ chainAtoms Pa E b := by
    intro x hx y hy
    rcases (hmemE x).mp hx with h | rfl
    · exact hEA (hPbE (hPb.cut_atom x h y hy))
    · rw [cutToList_seq, List.mem_singleton] at hy
      subst hy; exact hEA hrE
  have hEsym : ∀ cl, (RE.sym cl) ∈ E → ClsOK U cl := by
    intro cl hcl
    rcases (hmemE _).mp hcl with h | h
    · exact hPb.sym_cls cl h
    · exact absurd h (by simp)
  have hAtom := chainAtoms_atomSet hPa hEfin hbE hEalt hEcut hEsym
  have hEnot : ∀ y : RE, (RE.not y) ∈ E → y ∈ chainPool Pa E b := by
    intro y hy
    rcases (hmemE _).mp hy with h | h
    · exact hAP (hEA (hPbE (hPb.not_body y h)))
    · exact absurd h (by simp)
  have hEd : ∀ x ∈ E, ∀ c, deriv c x ∈ chainPool Pa E b := by
    intro x hx c
    rcases (hmemE x).mp hx with h | rfl
    · exact hAP (hEA (hPbE (hPb.deriv_mem x h c)))
    · rw [deriv_seq]
      have h1 : seq2 (deriv c a) b ∈ chainAtoms Pa E b :=
        chain_seq2_tail hPa (hPbE hb) (hPa.deriv_mem a ha c)
      split
      · exact chainPool_alt2 hAtom (hAP h1) (hAP (hEA (hPbE (hPb.deriv_mem b hb c))))
      · exact hAP h1
  have hEw : ∀ x ∈ E, ∀ w, derivW w x ∈ chainPool Pa E b := by
    intro x hx w
    rcases (hmemE x).mp hx with h | rfl
    · exact hAP (hEA (hPbE (hPb.derivW_mem x h w)))
    · rw [derivW_seq]
      refine chainPool_alt2 hAtom (hAP (chain_seq2_tail hPa (hPbE hb) (hPa.derivW_mem a ha w)))
        (chainPool_altL hAtom _ ?_)
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨i, -, rfl⟩ := hy
      split
      · exact hAP (hEA (hPbE (hPb.derivW_mem b hb _)))
      · exact hAP (hPaA hPa.nil_mem)
  have hEsuf : ∀ x ∈ E, ∀ i, seqOfList ((seqToList x).drop i) ∈ chainPool Pa E b := by
    intro x hx i
    rcases (hmemE x).mp hx with h | rfl
    · exact hAP (hEA (hPbE (hPb.suffix_mem x h i)))
    · rw [Smart.seqToList_seq, List.drop_append]
      exact hAP (hCA (mem_chainStates (frags_drop (frags_of_mem ha) i) _))
  have hEhd : ∀ x ∈ E, ∀ h rest, seqToList x = h :: rest → ∀ c,
      seqOfList (seqToList (deriv c h) ++ rest) ∈ chainPool Pa E b := by
    intro x hx h rest hrest c
    rcases (hmemE x).mp hx with hx' | rfl
    · exact hAP (hEA (hPbE (hPb.headD_mem x hx' h rest hrest c)))
    · rw [Smart.seqToList_seq] at hrest
      cases hla : seqToList a with
      | nil =>
        rw [hla, List.nil_append] at hrest
        exact hAP (hEA (hPbE (hPb.headD_mem b hb h rest hrest c)))
      | cons h' A' =>
        rw [hla, List.cons_append, List.cons.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        have hK : h' :: A' ∈ Frags Pa := by rw [← hla]; exact frags_of_mem ha
        rw [← List.append_assoc]
        exact hAP (hCA (mem_chainStates_zero (frags_head_step hPa hK c)))
  have hEhw : ∀ x ∈ E, ∀ h rest, seqToList x = h :: rest → ∀ w,
      seqOfList (seqToList (derivW w h) ++ rest) ∈ chainPool Pa E b := by
    intro x hx h rest hrest w
    rcases (hmemE x).mp hx with hx' | rfl
    · exact hAP (hEA (hPbE (hPb.headW_mem x hx' h rest hrest w)))
    · rw [Smart.seqToList_seq] at hrest
      cases hla : seqToList a with
      | nil =>
        rw [hla, List.nil_append] at hrest
        exact hAP (hEA (hPbE (hPb.headW_mem b hb h rest hrest w)))
      | cons h' A' =>
        rw [hla, List.cons_append, List.cons.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        have hK : h' :: A' ∈ Frags Pa := by rw [← hla]; exact frags_of_mem ha
        rw [← List.append_assoc]
        exact hAP (hCA (mem_chainStates_zero (frags_head_stepW hPa hK w)))
  exact ⟨chainPool Pa E b,
    sat_chainPool hPa hEfin hbE hEalt hEcut hEsym hEnot hEd hEw hEsuf hEhd hEhw,
    hAP (hEA hrE)⟩

/-! ### Star -/

theorem exists_sat_rep {U : Finset Char} {Pa : Set RE} {a : RE}
    (hPa : Sat U Pa) (ha : a ∈ Pa) : ∃ P, Sat U P ∧ (RE.rep a) ∈ P := by
  classical
  set E : Set RE := Pa ∪ {RE.rep a} with hEdef
  have hmemE : ∀ x : RE, x ∈ E ↔ (x ∈ Pa ∨ x = .rep a) := by
    intro x; simp [hEdef, or_comm]
  have hrE : (RE.rep a) ∈ E := (hmemE _).mpr (Or.inr rfl)
  have hPaE : Pa ⊆ E := fun x hx => (hmemE x).mpr (Or.inl hx)
  have hEA : E ⊆ chainAtoms Pa E (rep_ a) :=
    fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inr hx))
  have hPaA : Pa ⊆ chainAtoms Pa E (rep_ a) :=
    fun x hx => (mem_chainAtoms x).mpr (Or.inr (Or.inl hx))
  have hAP : chainAtoms Pa E (rep_ a) ⊆ chainPool Pa E (rep_ a) := Set.subset_union_left
  have hbmem : rep_ a ∈ E := by
    rcases rep_mem_cases a with h | h | h | h
    · rw [h]; exact hPaE hPa.eps_mem
    · rw [h]; exact hPaE hPa.top_mem
    · rw [h]; exact hPaE ha
    · rw [h]; exact hrE
  have hEfin : E.Finite := hPa.finite.union (Set.finite_singleton _)
  have hbE : ∀ j, seqOfList ((seqToList (rep_ a)).drop j) ∈ E := by
    intro j
    rcases suffix_of_notSeq (rep_notSeq a) j with h | h
    · rw [h]; exact hbmem
    · rw [h]; exact hPaE hPa.eps_mem
  have hEalt : ∀ x ∈ E, ∀ y ∈ altToList x, y ∈ chainAtoms Pa E (rep_ a) := by
    intro x hx y hy
    rcases (hmemE x).mp hx with h | rfl
    · exact hPaA (hPa.alt_atom x h y hy)
    · rw [altToList_rep, List.mem_singleton] at hy
      subst hy; exact hEA hrE
  have hEcut : ∀ x ∈ E, ∀ y ∈ cutToList x, y ∈ chainAtoms Pa E (rep_ a) := by
    intro x hx y hy
    rcases (hmemE x).mp hx with h | rfl
    · exact hPaA (hPa.cut_atom x h y hy)
    · rw [cutToList_rep, List.mem_singleton] at hy
      subst hy; exact hEA hrE
  have hEsym : ∀ cl, (RE.sym cl) ∈ E → ClsOK U cl := by
    intro cl hcl
    rcases (hmemE _).mp hcl with h | h
    · exact hPa.sym_cls cl h
    · exact absurd h (by simp)
  have hAtom := chainAtoms_atomSet hPa hEfin hbE hEalt hEcut hEsym
  have hEnot : ∀ y : RE, (RE.not y) ∈ E → y ∈ chainPool Pa E (rep_ a) := by
    intro y hy
    rcases (hmemE _).mp hy with h | h
    · exact hAP (hPaA (hPa.not_body y h))
    · exact absurd h (by simp)
  have hEd : ∀ x ∈ E, ∀ c, deriv c x ∈ chainPool Pa E (rep_ a) := by
    intro x hx c
    rcases (hmemE x).mp hx with h | rfl
    · exact hAP (hPaA (hPa.deriv_mem x h c))
    · rw [deriv_rep]
      exact hAP (chain_seq2_tail hPa hbmem (hPa.deriv_mem a ha c))
  have hEw : ∀ x ∈ E, ∀ w, derivW w x ∈ chainPool Pa E (rep_ a) := by
    intro x hx w
    rcases (hmemE x).mp hx with h | rfl
    · exact hAP (hPaA (hPa.derivW_mem x h w))
    · rw [derivW_rep]
      refine chainPool_altL hAtom _ ?_
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · split at hy
        · rw [List.mem_singleton] at hy
          subst hy; exact hAP (hEA hbmem)
        · simp at hy
      · rw [List.mem_map] at hy
        obtain ⟨i, -, rfl⟩ := hy
        split
        · exact hAP (chain_seq2_tail hPa hbmem (hPa.derivW_mem a ha _))
        · exact hAP (hPaA hPa.nil_mem)
  have hEsuf : ∀ x ∈ E, ∀ i, seqOfList ((seqToList x).drop i) ∈ chainPool Pa E (rep_ a) := by
    intro x hx i
    rcases (hmemE x).mp hx with h | rfl
    · exact hAP (hPaA (hPa.suffix_mem x h i))
    · exact suffix_mem_of_notSeq (hAP (hPaA hPa.eps_mem)) (hAP (hEA hrE)) trivial i
  have hEhd : ∀ x ∈ E, ∀ h rest, seqToList x = h :: rest → ∀ c,
      seqOfList (seqToList (deriv c h) ++ rest) ∈ chainPool Pa E (rep_ a) := by
    intro x hx
    rcases (hmemE x).mp hx with h | rfl
    · exact fun hh rest hrest c => hAP (hPaA (hPa.headD_mem x h hh rest hrest c))
    · exact headD_mem_of_notSeq (hAP (hEA hrE)) trivial
        (chainPool_deriv hPa hAtom hbE hEd) (chainPool_suffix_zero hPa hAtom hEsuf)
  have hEhw : ∀ x ∈ E, ∀ h rest, seqToList x = h :: rest → ∀ w,
      seqOfList (seqToList (derivW w h) ++ rest) ∈ chainPool Pa E (rep_ a) := by
    intro x hx
    rcases (hmemE x).mp hx with h | rfl
    · exact fun hh rest hrest w => hAP (hPaA (hPa.headW_mem x h hh rest hrest w))
    · exact headW_mem_of_notSeq (hAP (hEA hrE)) trivial
        (chainPool_derivW hPa hAtom hbE hEw) (chainPool_suffix_zero hPa hAtom hEsuf)
  exact ⟨chainPool Pa E (rep_ a),
    sat_chainPool hPa hEfin hbE hEalt hEcut hEsym hEnot hEd hEw hEsuf hEhd hEhw,
    hAP (hEA hrE)⟩

end Redgrep

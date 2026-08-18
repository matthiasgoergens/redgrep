import Semantics
import Statements

/-!
Correctness of the v2 engine (invHom added).  The statements below are
the contract: do not weaken them, do not change Semantics.lean, and
change Core.lean only where its comment explicitly says YOUR TASK
(implementing the invHom case of deriv, restructuring deriv only if
every other case still satisfies its existing equation).  The laws in
Statements.lean (notably deriv1_invHom, derivW) are available as lemmas.
-/

open Language Computability

namespace Redgrep

/-! ### Membership in `lang`, constructor by constructor

`Language α` is a `def` for `Set (List α)`, so the generic `Set` simp lemmas
do not fire on it; these `rfl`-lemmas give us a usable simp set. -/

@[local simp] theorem mem_lang_sym (cls : Char → Bool) (w : List Char) :
    w ∈ lang (.sym cls) ↔ ∃ c, cls c = true ∧ w = [c] := Iff.rfl

@[local simp] theorem mem_lang_alt (r₁ r₂ : RE) (w : List Char) :
    w ∈ lang (.alt r₁ r₂) ↔ w ∈ lang r₁ ∨ w ∈ lang r₂ := Iff.rfl

@[local simp] theorem mem_lang_cut (r₁ r₂ : RE) (w : List Char) :
    w ∈ lang (.cut r₁ r₂) ↔ w ∈ lang r₁ ∧ w ∈ lang r₂ := Iff.rfl

@[local simp] theorem mem_lang_seq (r₁ r₂ : RE) (w : List Char) :
    w ∈ lang (.seq r₁ r₂) ↔ ∃ a ∈ lang r₁, ∃ b ∈ lang r₂, a ++ b = w :=
  Language.mem_mul

@[local simp] theorem mem_lang_rep (r : RE) (w : List Char) :
    w ∈ lang (.rep r) ↔ w ∈ (lang r)∗ := Iff.rfl

@[local simp] theorem mem_lang_not (r : RE) (w : List Char) :
    w ∈ lang (.not r) ↔ ¬ w ∈ lang r := Iff.rfl

@[local simp] theorem mem_lang_invHom (h : Char → List Char) (r : RE) (w : List Char) :
    w ∈ lang (.invHom h r) ↔ w.flatMap h ∈ lang r := Iff.rfl

@[local simp] theorem mem_lang_eps (w : List Char) : w ∈ lang .eps ↔ w = [] := Iff.rfl

@[local simp] theorem mem_lang_nil (w : List Char) : w ∈ lang .nil ↔ False := Iff.rfl

@[local simp] theorem mem_derivW_iff (u w : List Char) (L : Language Char) :
    w ∈ _root_.derivW u L ↔ u ++ w ∈ L := Iff.rfl

/-! ### Auxiliary lemmas -/

/-- `altFold` denotes the union of the languages of its arguments. -/
theorem mem_lang_altFold (l : List RE) (w : List Char) :
    w ∈ lang (altFold l) ↔ ∃ r ∈ l, w ∈ lang r := by
  induction l with
  | nil => simp [altFold]
  | cons r rs ih => simp [altFold, ih]

theorem nullable_correct (r : RE) : nullable r = true ↔ ([] : List Char) ∈ lang r := by
  induction r with
  | sym cls => simp [nullable]
  | alt r₁ r₂ ih₁ ih₂ => simp [nullable, ih₁, ih₂]
  | cut r₁ r₂ ih₁ ih₂ => simp [nullable, ih₁, ih₂]
  | seq r₁ r₂ ih₁ ih₂ =>
    simp only [nullable, Bool.and_eq_true, ih₁, ih₂, mem_lang_seq]
    constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨[], h₁, [], h₂, rfl⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hab
      exact ⟨ha, hb⟩
  | rep r ih => simp [nullable, Language.nil_mem_kstar]
  | not r ih =>
    simp only [nullable, Bool.not_eq_true', mem_lang_not, ← ih, Bool.not_eq_true]
  | invHom h r ih => simp [nullable, ih]
  | eps => simp [nullable]
  | nil => simp [nullable]

/-- Gluing: `L∗ * L * L∗ ⊆ L∗`, in element form. -/
theorem kstar_append_kstar (L : Language Char) {p q s : List Char}
    (hp : p ∈ L∗) (hq : q ∈ L) (hs : s ∈ L∗) : p ++ (q ++ s) ∈ L∗ := by
  obtain ⟨P, rfl, hP⟩ := hp
  obtain ⟨S, rfl, hS⟩ := hs
  have hflat : (P ++ (q :: S)).flatten = P.flatten ++ (q ++ S.flatten) := by simp
  rw [← hflat]
  refine Language.join_mem_kstar ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hP y hy
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact hq
    · exact hS y hy

/-- Chunkwise form of `kstar_split` below, by induction on the chunk list. -/
theorem kstar_split_aux (L : Language Char) :
    ∀ (S : List (List Char)) (u w : List Char),
      (∀ y ∈ S, y ∈ L ∧ y ≠ []) → u ++ w = S.flatten → u ≠ [] →
      ∃ i, i < u.length ∧ u.take i ∈ L∗ ∧ w ∈ (_root_.derivW (u.drop i) L) * L∗ := by
  intro S
  induction S with
  | nil =>
    intro u w _ heq hu
    simp only [List.flatten_nil] at heq
    exact absurd (List.append_eq_nil_iff.mp heq).1 hu
  | cons x T ih =>
    intro u w hmem heq hu
    obtain ⟨hxL, hxne⟩ := hmem x (by simp)
    have hT : ∀ y ∈ T, y ∈ L ∧ y ≠ [] := fun y hy => hmem y (by simp [hy])
    have hTflat : T.flatten ∈ L∗ :=
      Language.join_mem_kstar fun y hy => (hT y hy).1
    have hupos : 0 < u.length := List.length_pos_iff.mpr hu
    rw [List.flatten_cons] at heq
    rcases List.append_eq_append_iff.mp heq with ⟨a, ha1, ha2⟩ | ⟨c, hc1, hc2⟩
    · -- `u` is a prefix of the first chunk `x`
      refine ⟨0, hupos, ?_, ?_⟩
      · simpa using Language.nil_mem_kstar L
      · simp only [List.drop_zero]
        exact Language.mem_mul.mpr ⟨a, by simpa [← ha1] using hxL, T.flatten, hTflat, ha2.symm⟩
    · -- the first chunk `x` is a prefix of `u`
      rcases eq_or_ne c [] with rfl | hcne
      · refine ⟨0, hupos, ?_, ?_⟩
        · simpa using Language.nil_mem_kstar L
        · simp only [List.drop_zero]
          refine Language.mem_mul.mpr ⟨[], ?_, w, ?_, by simp⟩
          · show u ++ [] ∈ L
            simpa [hc1] using hxL
          · rw [List.nil_append] at hc2
            simpa [← hc2] using hTflat
      · obtain ⟨j, hj, hjtake, hjdrop⟩ := ih c w hT hc2.symm hcne
        refine ⟨x.length + j, ?_, ?_, ?_⟩
        · rw [hc1]
          simp only [List.length_append]
          omega
        · rw [hc1, List.take_length_add_append]
          simpa using kstar_append_kstar L (Language.nil_mem_kstar L) hxL hjtake
        · rw [hc1, List.drop_length_add_append]
          exact hjdrop

/-- If `u ++ w` lies in `L∗` with `u` nonempty, then some proper prefix of `u`
is a whole number of iterations of `L`, and the chunk straddling the split
point begins with the remaining suffix of `u`. -/
theorem kstar_split (L : Language Char) (u w : List Char) (hu : u ≠ [])
    (h : u ++ w ∈ L∗) :
    ∃ i, i < u.length ∧ u.take i ∈ L∗ ∧ w ∈ (_root_.derivW (u.drop i) L) * L∗ := by
  obtain ⟨S, hS, hmem⟩ := Language.mem_kstar_iff_exists_nonempty.mp h
  exact kstar_split_aux L S u w hmem hS hu

/-- The word derivative of the engine denotes the left quotient. -/
theorem lang_derivW (u : List Char) (r : RE) :
    lang (derivW u r) = _root_.derivW u (lang r) := by
  induction u, r using Redgrep.derivW.induct with
  | case1 cls =>
    rw [derivW]
    rfl
  | case2 cls c hc =>
    rw [derivW, if_pos hc]
    ext w
    simp only [mem_lang_eps, mem_derivW_iff, mem_lang_sym, List.singleton_append]
    constructor
    · rintro rfl; exact ⟨c, hc, rfl⟩
    · rintro ⟨c', _, hw⟩
      simp only [List.cons.injEq] at hw
      exact hw.2
  | case3 cls c hc =>
    rw [derivW, if_neg hc]
    ext w
    simp only [mem_lang_nil, mem_derivW_iff, mem_lang_sym, List.singleton_append, false_iff,
      not_exists]
    rintro c' ⟨hc', hw⟩
    simp only [List.cons.injEq] at hw
    exact hc (hw.1 ▸ hc')
  | case4 u cls h1 h2 =>
    rw [derivW]
    · ext w
      simp only [mem_lang_nil, mem_derivW_iff, mem_lang_sym, false_iff, not_exists]
      rintro c' ⟨_, hw⟩
      cases u with
      | nil => exact h1 rfl
      | cons d u' =>
        simp only [List.cons_append, List.cons.injEq] at hw
        obtain ⟨rfl, hnil⟩ := hw
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hnil
        exact h2 d rfl
    · exact h1
    · exact h2
  | case5 u r₁ r₂ ih₁ ih₂ =>
    rw [derivW]
    ext w
    simp only [mem_lang_alt, ih₁, ih₂, mem_derivW_iff, mem_lang_alt]
  | case6 u r₁ r₂ ih₁ ih₂ =>
    rw [derivW]
    ext w
    simp only [mem_lang_cut, ih₁, ih₂, mem_derivW_iff, mem_lang_cut]
  | case7 u r₁ r₂ ih ihtake ihdrop =>
    rw [derivW]
    ext w
    simp only [mem_lang_alt, mem_lang_seq, mem_lang_altFold, mem_derivW_iff, mem_lang_seq]
    constructor
    · rintro (⟨a, ha, b, hb, rfl⟩ | ⟨rr, hrr, hw⟩)
      · rw [ih] at ha
        exact ⟨u ++ a, ha, b, hb, List.append_assoc u a b⟩
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrr
        by_cases hn : nullable (derivW (u.take i) r₁) = true
        · rw [if_pos hn] at hw
          rw [ihdrop i] at hw
          have h1 : u.take i ∈ lang r₁ := by
            have hnil := (nullable_correct _).mp hn
            rw [ihtake i] at hnil
            simpa using hnil
          refine ⟨u.take i, h1, u.drop i ++ w, hw, ?_⟩
          rw [← List.append_assoc, List.take_append_drop]
        · rw [if_neg hn] at hw
          exact absurd hw (by simp)
    · rintro ⟨a, ha, b, hb, hab⟩
      rcases List.append_eq_append_iff.mp hab with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
      · -- `a` is a prefix of `u`
        right
        have htake : u.take a.length = a := by rw [hc1]; simp
        have hdrop : u.drop a.length = c := by rw [hc1]; simp
        refine ⟨_, List.mem_map.mpr ⟨a.length, ?_, rfl⟩, ?_⟩
        · refine List.mem_range.mpr ?_
          rw [hc1]
          simp only [List.length_append]
          omega
        · rw [htake, hdrop]
          have hn : nullable (derivW a r₁) = true := by
            refine (nullable_correct _).mpr ?_
            have hlang := ihtake a.length
            rw [htake] at hlang
            rw [hlang]
            simpa using ha
          rw [if_pos hn]
          have hlang := ihdrop a.length
          rw [hdrop] at hlang
          rw [hlang]
          simpa [← hc2] using hb
      · -- `u` is a prefix of `a`
        left
        refine ⟨c, ?_, b, hb, hc2.symm⟩
        rw [ih]
        simpa [← hc1] using ha
  | case8 u r ihrep ihr =>
    rw [derivW]
    rcases eq_or_ne u [] with rfl | hu
    · ext w
      simp [mem_lang_altFold]
    · have hemp : (if u.isEmpty = true then [RE.rep r] else []) = ([] : List RE) := by
        cases u with
        | nil => exact absurd rfl hu
        | cons _ _ => rfl
      rw [hemp, List.nil_append]
      ext w
      simp only [mem_lang_altFold, List.mem_map, mem_derivW_iff, mem_lang_rep]
      constructor
      · rintro ⟨rr, ⟨x, _, rfl⟩, hw⟩
        by_cases hn : nullable (derivW (u.take x.1) (.rep r)) = true
        · rw [if_pos hn] at hw
          have htake : u.take x.1 ∈ (lang r)∗ := by
            have hnil := (nullable_correct _).mp hn
            rw [ihrep x] at hnil
            simpa using hnil
          obtain ⟨a, ha, b, hb, rfl⟩ := (mem_lang_seq _ _ _).mp hw
          rw [ihr x] at ha
          have hrew : u ++ (a ++ b) = u.take x.1 ++ ((u.drop x.1 ++ a) ++ b) := by
            rw [List.append_assoc (u.drop x.1), ← List.append_assoc (u.take x.1),
              List.take_append_drop]
          rw [hrew]
          exact kstar_append_kstar (lang r) htake ha hb
        · rw [if_neg hn] at hw
          exact absurd hw (by simp)
      · intro hmem
        obtain ⟨i, hi, htake, hdrop⟩ := kstar_split (lang r) u w hu hmem
        have hix : i ∈ List.range u.length := List.mem_range.mpr hi
        refine ⟨_, ⟨⟨i, hix⟩, List.mem_attach _ _, rfl⟩, ?_⟩
        have hn : nullable (derivW (u.take i) (.rep r)) = true := by
          refine (nullable_correct _).mpr ?_
          rw [ihrep ⟨i, hix⟩]
          simpa using htake
        simp only [hn, if_true]
        refine (mem_lang_seq _ _ _).mpr ?_
        obtain ⟨a, ha, b, hb, hab⟩ := Language.mem_mul.mp hdrop
        refine ⟨a, ?_, b, hb, hab⟩
        rw [ihr ⟨i, hix⟩]
        exact ha
  | case9 u r ih =>
    rw [derivW]
    ext w
    simp only [mem_lang_not, ih, mem_derivW_iff, mem_lang_not]
  | case10 u h r ih =>
    have hattach : (List.flatMap (fun x : {x // x ∈ u} => h x.1) u.attach) = u.flatMap h := by
      simp
    rw [hattach] at ih
    rw [derivW]
    ext w
    simp only [mem_lang_invHom, ih, mem_derivW_iff, mem_lang_invHom, List.flatMap_append]
  | case11 =>
    rw [derivW]
    rfl
  | case12 u hu =>
    rw [derivW]
    · ext w
      simp only [mem_lang_nil, mem_derivW_iff, mem_lang_eps, false_iff]
      intro hcon
      cases u with
      | nil => exact hu rfl
      | cons d u' => exact List.cons_ne_nil d (u' ++ w) hcon
    · exact hu
  | case13 u =>
    rw [derivW]
    ext w
    simp only [mem_lang_nil, mem_derivW_iff, mem_lang_nil]

theorem lang_deriv (c : Char) (r : RE) : lang (deriv c r) = deriv1 c (lang r) := by
  induction r with
  | sym cls =>
    ext w
    show w ∈ lang (if cls c then RE.eps else RE.nil) ↔ c :: w ∈ lang (RE.sym cls)
    by_cases hc : cls c = true
    · rw [if_pos hc]
      simp only [mem_lang_eps, mem_lang_sym]
      constructor
      · rintro rfl; exact ⟨c, hc, rfl⟩
      · rintro ⟨c', _, hw⟩
        simp only [List.cons.injEq] at hw
        exact hw.2
    · rw [if_neg hc]
      simp only [mem_lang_nil, mem_lang_sym, false_iff, not_exists]
      rintro c' ⟨hc', hw⟩
      simp only [List.cons.injEq] at hw
      exact hc (hw.1 ▸ hc')
  | alt r₁ r₂ ih₁ ih₂ =>
    ext w
    show w ∈ lang (deriv c r₁) ∨ w ∈ lang (deriv c r₂) ↔ _
    rw [ih₁, ih₂]
    exact Iff.rfl
  | cut r₁ r₂ ih₁ ih₂ =>
    ext w
    show w ∈ lang (deriv c r₁) ∧ w ∈ lang (deriv c r₂) ↔ _
    rw [ih₁, ih₂]
    exact Iff.rfl
  | seq r₁ r₂ ih₁ ih₂ =>
    show lang (deriv c (RE.seq r₁ r₂)) = deriv1 c (lang r₁ * lang r₂)
    rw [deriv1_mul]
    by_cases hn : nullable r₁ = true
    · rw [if_pos ((nullable_correct r₁).mp hn)]
      show lang (if nullable r₁ then _ else _) = _
      rw [if_pos hn]
      show lang (deriv c r₁) * lang r₂ ⊔ lang (deriv c r₂) = _
      rw [ih₁, ih₂]
    · rw [if_neg (fun hmem => hn ((nullable_correct r₁).mpr hmem))]
      show lang (if nullable r₁ then _ else _) = _
      rw [if_neg hn]
      show lang (deriv c r₁) * lang r₂ = _
      rw [ih₁, sup_bot_eq]
  | rep r ih =>
    show lang (deriv c r) * (lang r)∗ = deriv1 c ((lang r)∗)
    rw [deriv1_kstar, ih]
  | not r ih =>
    show (lang (deriv c r))ᶜ = deriv1 c ((lang r)ᶜ)
    rw [deriv1_compl, ih]
  | invHom h r ih =>
    show _root_.invHom h (lang (derivW (h c) r)) = deriv1 c (_root_.invHom h (lang r))
    rw [deriv1_invHom, lang_derivW]
  | eps =>
    ext w
    show w ∈ lang RE.nil ↔ c :: w ∈ lang RE.eps
    simp
  | nil =>
    ext w
    show w ∈ lang RE.nil ↔ c :: w ∈ lang RE.nil
    simp

theorem deriv_correct (c : Char) (r : RE) (w : List Char) :
    w ∈ lang (deriv c r) ↔ (c :: w) ∈ lang r := by
  rw [lang_deriv]
  exact Iff.rfl

theorem matchRE_correct (r : RE) (s : List Char) : matchRE r s = true ↔ s ∈ lang r := by
  induction s generalizing r with
  | nil => simpa [matchRE] using nullable_correct r
  | cons c s ih =>
    have hstep : matchRE r (c :: s) = matchRE (deriv c r) s := by simp [matchRE]
    rw [hstep, ih, deriv_correct]

end Redgrep

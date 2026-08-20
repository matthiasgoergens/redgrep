import SmartLang

/-!
# The engine contract

`Core.lean`'s smart constructor `invHom_` replaces its association list `h` by
the normal form `homNorm h`.  Normalisation deduplicates the list **by key**,
keeping the first binding of each key — the one `applyHom` resolves to — and
only then drops identity entries, sorts and dedups.  It therefore preserves
the denoted homomorphism pointwise (`homNorm_applyHom`, `REOrder.lean`), which
is what makes the engine contract below hold unconditionally.

Historical note: an earlier version of `homNorm` filtered identity entries
*before* restoring the unique-key invariant, and was unsound on association
lists with duplicate keys, e.g.

```
h = [('a', ['a']), ('a', ['b'])] ,  applyHom h 'a' = ['a'] ,
oldHomNorm h = [('a', ['b'])]    ,  applyHom (oldHomNorm h) 'a' = ['b'] .
```

That counterexample is what motivated the dedup-by-key step; with it in place,
no side condition on the association lists is needed anywhere.
-/

open Language Computability

namespace Redgrep

/-! ### Nullability -/

theorem nullable_iff (r : RE) : nullable r = true ↔ ([] : List Char) ∈ lang r := by
  induction r with
  | sym cl => simp [nullable]
  | alt a b iha ihb => simp [nullable, iha, ihb]
  | cut a b iha ihb => simp [nullable, iha, ihb]
  | seq a b iha ihb =>
    simp only [nullable, Bool.and_eq_true, iha, ihb, Smart.mem_lang_seq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨[], h1, [], h2, rfl⟩
    · rintro ⟨x, hx, y, hy, hxy⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hxy
      exact ⟨hx, hy⟩
  | rep a _ =>
    simp only [nullable, Smart.lang_rep, true_iff]
    exact Language.nil_mem_kstar _
  | not a iha => simp [nullable, ← iha]
  | invHom h a iha => simpa [nullable] using iha
  | eps => simp [nullable]
  | nil => simp [nullable]

theorem flatMap_singleton_self (w : List Char) : w.flatMap (fun c => [c]) = w := by
  induction w with
  | nil => rfl
  | cons c t ih => simp [List.flatMap_cons, ih]

/-- Language contract of the smart inverse homomorphism. -/
theorem lang_invHom_smart (h : List (Char × List Char)) (r : RE) :
    lang (invHom_ h r) = _root_.invHom (applyHom h) (lang r) := by
  rw [invHom_eq_ite]
  split
  · rename_i hr
    subst hr
    ext w
    show w ∈ lang RE.nil ↔ (w.flatMap (applyHom h)) ∈ lang RE.nil
    exact iff_of_false Smart.mem_lang_nil.mp Smart.mem_lang_nil.mp
  · split
    · rename_i hemp
      ext w
      show w ∈ lang r ↔ (w.flatMap (applyHom h)) ∈ lang r
      rw [← homNorm_applyHom_eq h, hemp]
      rw [show applyHom [] = fun c => [c] from rfl, flatMap_singleton_self]
    · show _root_.invHom (applyHom (homNorm h)) (lang r) = _root_.invHom (applyHom h) (lang r)
      rw [homNorm_applyHom_eq]

/-! ### A decomposition lemma for the Kleene star -/

@[simp] theorem mem_derivW {u w : List Char} {L : Language Char} :
    w ∈ _root_.derivW u L ↔ u ++ w ∈ L := Iff.rfl

theorem nil_mem_derivW {u : List Char} {L : Language Char} :
    [] ∈ _root_.derivW u L ↔ u ∈ L := by
  show u ++ [] ∈ L ↔ u ∈ L
  rw [List.append_nil]

theorem kstar_head {L : Language Char} {x : List Char} (hx : x ∈ L∗) (hne : x ≠ []) :
    ∃ c t, c ≠ [] ∧ c ∈ L ∧ t ∈ L∗ ∧ x = c ++ t := by
  obtain ⟨S, rfl, hS⟩ := Language.mem_kstar_iff_exists_nonempty.mp hx
  cases S with
  | nil => simp at hne
  | cons c T =>
    obtain ⟨hc, hcne⟩ := hS c (by simp)
    exact ⟨c, T.flatten, hcne, hc,
      Language.join_mem_kstar (fun y hy => (hS y (by simp [hy])).1), by simp⟩

theorem append_mem_kstar {L : Language Char} {c t : List Char} (hc : c ∈ L) (ht : t ∈ L∗) :
    c ++ t ∈ L∗ :=
  Set.mem_of_mem_of_subset (Language.append_mem_mul hc ht) (mul_kstar_le_kstar (a := L))

theorem append_mem_kstar_left {L : Language Char} {c t : List Char} (hc : c ∈ L∗)
    (ht : t ∈ L∗) : c ++ t ∈ L∗ :=
  Set.mem_of_mem_of_subset (Language.append_mem_mul hc ht) (kstar_mul_kstar L).le

/-- If a nonempty prefix `u` is consumed inside `L∗`, then some *proper* prefix of `u` is a
whole number of iterations and the straddling chunk starts with the rest of `u`. -/
theorem kstar_append_decomp {L : Language Char} (n : ℕ) :
    ∀ (u : List Char), u.length ≤ n → u ≠ [] → ∀ w, u ++ w ∈ L∗ →
      ∃ i, i < u.length ∧ u.take i ∈ L∗ ∧
        ∃ z y, (u.drop i ++ z) ∈ L ∧ y ∈ L∗ ∧ w = z ++ y := by
  induction n with
  | zero =>
    intro u hlen hne
    exact absurd (List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)) hne
  | succ n ih =>
    intro u hlen hne w hw
    obtain ⟨c, t, hcne, hc, ht, heq⟩ := kstar_head hw (by simp [hne])
    rcases List.append_eq_append_iff.mp heq with ⟨a, hca, hwa⟩ | ⟨a, hua, hta⟩
    · refine ⟨0, List.length_pos_of_ne_nil hne, ?_, a, t, ?_, ht, hwa⟩
      · simpa using Language.nil_mem_kstar L
      · simpa using hca ▸ hc
    · by_cases ha : a = []
      · subst ha
        simp only [List.append_nil] at hua
        subst hua
        rw [List.nil_append] at hta
        subst hta
        exact ⟨0, List.length_pos_of_ne_nil hne, by simpa using Language.nil_mem_kstar L,
          [], t, by simpa using hc, ht, rfl⟩
      · subst hua
        have hlen' : a.length ≤ n := by
          simp only [List.length_append] at hlen
          have : 0 < c.length := List.length_pos_of_ne_nil hcne
          omega
        obtain ⟨i, hi, hti, z, y, hz, hy, hwzy⟩ := ih a hlen' ha w (hta ▸ ht)
        refine ⟨c.length + i, ?_, ?_, z, y, ?_, hy, hwzy⟩
        · simp only [List.length_append]; omega
        · rw [List.take_append]
          simp only [Nat.add_sub_cancel_left]
          rw [List.take_of_length_le (by omega)]
          exact append_mem_kstar hc hti
        · rw [List.drop_append]
          simp only [Nat.add_sub_cancel_left]
          rw [List.drop_eq_nil_of_le (by omega)]
          simpa using hz

/-! ### The word derivative -/

theorem lang_derivW_eq : ∀ (u : List Char) (r : RE),
    lang (derivW u r) = _root_.derivW u (lang r) := by
  intro u r
  induction u, r using derivW.induct with
  | case1 cls =>
    rw [derivW, Smart.lang_smart_sym]
    ext w
    exact Iff.rfl
  | case2 cls c hc =>
    rw [derivW, if_pos hc]
    ext w
    show w ∈ lang RE.eps ↔ [c] ++ w ∈ lang (RE.sym cls)
    simp only [Smart.mem_lang_eps, Smart.mem_lang_sym]
    constructor
    · rintro rfl
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c', -, he⟩
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      exact he.2
  | case3 cls c hc =>
    rw [derivW, if_neg hc]
    ext w
    show w ∈ lang RE.nil ↔ [c] ++ w ∈ lang (RE.sym cls)
    simp only [Smart.mem_lang_nil, Smart.mem_lang_sym, false_iff, not_exists]
    rintro c' ⟨hc', he⟩
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
    exact hc (by rw [he.1]; exact hc')
  | case4 u cls h1 h2 =>
    rw [derivW]
    · ext w
      show w ∈ lang RE.nil ↔ u ++ w ∈ lang (RE.sym cls)
      simp only [Smart.mem_lang_nil, Smart.mem_lang_sym, false_iff, not_exists]
      rintro c' ⟨-, he⟩
      cases u with
      | nil => exact h1 rfl
      | cons d t =>
        simp only [List.cons_append, List.cons.injEq] at he
        have ht : t = [] := (List.append_eq_nil_iff.mp he.2).1
        exact h2 d (by rw [ht])
    · exact h1
    · exact h2
  | case5 u a b iha ihb =>
    rw [derivW, Smart.lang_alt2, iha, ihb]
    rfl
  | case6 u a b iha ihb =>
    rw [derivW, Smart.lang_cut2, iha, ihb]
    rfl
  | case7 u a b iha ihtake ihdrop =>
    rw [derivW]
    ext w
    rw [mem_derivW, Smart.mem_lang_alt2, Smart.mem_lang_seq2, Smart.mem_lang_altL]
    show (_ ∨ _) ↔ u ++ w ∈ lang a * lang b
    constructor
    · rintro (⟨p, hp, q, hq, rfl⟩ | ⟨s, hs, hws⟩)
      · rw [iha, mem_derivW] at hp
        rw [← List.append_assoc]
        exact Language.append_mem_mul hp hq
      · rw [List.mem_map] at hs
        obtain ⟨i, -, rfl⟩ := hs
        split at hws
        · rename_i hnull
          rw [nullable_iff, ihtake i, nil_mem_derivW] at hnull
          rw [ihdrop i, mem_derivW] at hws
          have heq : u ++ w = u.take i ++ (u.drop i ++ w) := by
            rw [← List.append_assoc, List.take_append_drop]
          rw [heq]
          exact Language.append_mem_mul hnull hws
        · exact absurd hws (by simp)
    · intro hw'
      obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw'
      rcases List.append_eq_append_iff.mp hxy with ⟨z, huz, hyz⟩ | ⟨z, hxz, hwz⟩
      · right
        have htake : u.take x.length = x := by
          rw [huz, List.take_append]; simp
        have hdrop : u.drop x.length = z := by
          rw [huz, List.drop_append]; simp
        have hnull : nullable (derivW (u.take x.length) a) = true := by
          rw [nullable_iff, ihtake x.length, nil_mem_derivW, htake]
          exact hx
        refine ⟨_, List.mem_map.mpr ⟨x.length, ?_, rfl⟩, ?_⟩
        · rw [List.mem_range, huz]
          simp only [List.length_append]
          omega
        · rw [if_pos hnull, ihdrop x.length, mem_derivW, hdrop, ← hyz]
          exact hy
      · left
        refine ⟨z, ?_, y, hy, hwz.symm⟩
        rw [iha, mem_derivW, ← hxz]
        exact hx
  | case8 u a ihtake ihdrop =>
    rw [derivW]
    ext w
    rw [mem_derivW, Smart.mem_lang_altL]
    show (∃ s ∈ _, w ∈ lang s) ↔ u ++ w ∈ (lang a)∗
    constructor
    · rintro ⟨s, hs, hws⟩
      rcases List.mem_append.mp hs with hs | hs
      · split at hs
        · rename_i hu
          rw [List.mem_singleton] at hs
          subst hs
          have hu' : u = [] := List.isEmpty_iff.mp hu
          subst hu'
          rw [Smart.mem_lang_rep_] at hws
          simpa using hws
        · simp at hs
      · rw [List.mem_map] at hs
        obtain ⟨i, -, rfl⟩ := hs
        split at hws
        · rename_i hnull
          rw [nullable_iff, ihtake i, nil_mem_derivW] at hnull
          obtain ⟨p, hp, q, hq, rfl⟩ := Smart.mem_lang_seq2.mp hws
          rw [ihdrop i, mem_derivW] at hp
          rw [Smart.mem_lang_rep_] at hq
          have heq : u ++ (p ++ q) = u.take i.1 ++ ((u.drop i.1 ++ p) ++ q) := by
            rw [List.append_assoc (u.drop i.1), ← List.append_assoc (u.take i.1),
              List.take_append_drop]
          rw [heq]
          exact append_mem_kstar_left hnull (append_mem_kstar hp hq)
        · exact absurd hws (by simp)
    · intro hw'
      by_cases hu : u = []
      · subst hu
        refine ⟨rep_ a, List.mem_append_left _ (by simp), ?_⟩
        rw [Smart.mem_lang_rep_]
        simpa using hw'
      · obtain ⟨i, hi, hti, z, y, hz, hy, rfl⟩ :=
          kstar_append_decomp u.length u le_rfl hu w hw'
        refine ⟨_, List.mem_append_right _ (List.mem_map.mpr
          ⟨⟨i, List.mem_range.mpr hi⟩, List.mem_attach _ _, rfl⟩), ?_⟩
        have hnull : nullable (derivW (u.take i) (RE.rep a)) = true := by
          rw [nullable_iff, ihtake ⟨i, List.mem_range.mpr hi⟩, nil_mem_derivW]
          exact hti
        rw [if_pos hnull]
        refine Smart.mem_lang_seq2.mpr ⟨z, ?_, y, Smart.mem_lang_rep_.mpr hy, rfl⟩
        rw [ihdrop ⟨i, List.mem_range.mpr hi⟩, mem_derivW]
        exact hz
  | case9 u a ih =>
    rw [derivW, Smart.lang_not_, ih]
    rfl
  | case10 u hh a ih =>
    rw [derivW, lang_invHom_smart]
    have hih : lang (derivW (u.flatMap (applyHom hh)) a)
        = _root_.derivW (u.flatMap (applyHom hh)) (lang a) := by
      simpa using ih
    rw [hih]
    ext w
    show (u.flatMap (applyHom hh)) ++ (w.flatMap (applyHom hh)) ∈ lang a ↔
      ((u ++ w).flatMap (applyHom hh)) ∈ lang a
    rw [List.flatMap_append]
  | case11 =>
    rw [derivW]
    ext w
    exact Iff.rfl
  | case12 u h1 =>
    rw [derivW]
    · ext w
      show w ∈ lang RE.nil ↔ u ++ w ∈ lang RE.eps
      simp only [Smart.mem_lang_nil, Smart.mem_lang_eps, false_iff]
      intro he
      exact h1 (List.append_eq_nil_iff.mp he).1
    · exact h1
  | case13 u =>
    rw [derivW]
    ext w
    show w ∈ lang RE.nil ↔ u ++ w ∈ lang RE.nil
    simp

theorem lang_deriv_eq (c : Char) (r : RE) :
    lang (deriv c r) = deriv1 c (lang r) := by
  induction r with
  | sym cl =>
    rw [deriv_sym]
    ext w
    by_cases hc : inCls c cl
    · simp only [hc, if_pos]
      show w ∈ lang RE.eps ↔ c :: w ∈ lang (RE.sym cl)
      simp only [Smart.mem_lang_eps, Smart.mem_lang_sym]
      constructor
      · rintro rfl; exact ⟨c, hc, rfl⟩
      · rintro ⟨d, _, hd⟩; simpa using (List.cons.injEq c w d []).mp hd |>.2
    · simp only [hc, if_neg, Bool.false_eq_true, not_false_iff]
      show w ∈ lang RE.nil ↔ c :: w ∈ lang (RE.sym cl)
      simp only [Smart.mem_lang_nil, Smart.mem_lang_sym, false_iff]
      rintro ⟨d, hd, he⟩
      obtain ⟨rfl, -⟩ := (List.cons.injEq c w d []).mp he
      exact hc hd
  | alt a b iha ihb =>
    rw [deriv_alt, Smart.lang_alt2, iha, ihb]
    rfl
  | cut a b iha ihb =>
    rw [deriv_cut, Smart.lang_cut2, iha, ihb]
    rfl
  | seq a b iha ihb =>
    show lang (if nullable a then alt2 (seq2 (deriv c a) b) (deriv c b)
      else seq2 (deriv c a) b) = deriv1 c (lang a * lang b)
    rw [deriv1_mul]
    by_cases hn : nullable a
    · rw [if_pos hn, Smart.lang_alt2, Smart.lang_seq2, iha, ihb,
        if_pos ((nullable_iff a).mp hn)]
    · rw [if_neg hn, Smart.lang_seq2, iha,
        if_neg (fun hx => hn ((nullable_iff a).mpr hx))]
      simp
  | rep a iha =>
    show lang (seq2 (deriv c a) (rep_ a)) = deriv1 c ((lang a)∗)
    rw [Smart.lang_seq2, Smart.lang_rep_, iha, deriv1_kstar]
  | not a iha =>
    show lang (not_ (deriv c a)) = deriv1 c ((lang a)ᶜ)
    rw [Smart.lang_not_, iha, deriv1_compl]
  | invHom hh a _ =>
    show lang (invHom_ hh (derivW (applyHom hh c) a)) =
      deriv1 c (_root_.invHom (applyHom hh) (lang a))
    rw [lang_invHom_smart, lang_derivW_eq _ _, deriv1_invHom]
  | eps =>
    show lang RE.nil = deriv1 c (1 : Language Char)
    ext w
    show w ∈ lang RE.nil ↔ c :: w ∈ (1 : Language Char)
    simp only [Smart.mem_lang_nil, false_iff, Language.mem_one]
    exact List.cons_ne_nil _ _
  | nil =>
    show lang RE.nil = deriv1 c (0 : Language Char)
    ext w
    show w ∈ lang RE.nil ↔ c :: w ∈ (0 : Language Char)
    simp only [Smart.mem_lang_nil, false_iff]
    exact Set.notMem_empty _

theorem matchRE_iff (r : RE) (s : List Char) :
    matchRE r s = true ↔ s ∈ lang r := by
  induction s generalizing r with
  | nil => exact nullable_iff r
  | cons c t ih =>
    show nullable (t.foldl (fun r c => deriv c r) (deriv c r)) = true ↔ _
    rw [show (nullable (t.foldl (fun r c => deriv c r) (deriv c r)) = true)
      = (matchRE (deriv c r) t = true) from rfl, ih (deriv c r),
      lang_deriv_eq c r]
    rfl

end Redgrep

import ACI
import AltAlg
import CutAlg

/-!
# Equations for the engine, and canonicity of derivatives

Two things the finiteness proof (`ClosureSat.lean`) needs before anything
else can be said about the reachable state set:

* the defining equations of `derivW` as rewrite rules (`derivW` is defined by
  well-founded recursion, so they are not definitional), together with the
  smart-`sym` forms of both derivative operators;
* the fact that **derivatives of canonical terms are canonical**
  (`isCanon_deriv`, `isCanon_derivW`).  The engine routes everything through
  the smart constructors, so this is really the statement that the smart
  constructors are closed under the derivative recursion.
-/

namespace Redgrep

open Smart

/-! ### Equations for the word derivative -/

@[simp] theorem derivW_nilRE (w : List Char) : derivW w .nil = .nil := by rw [derivW]

@[simp] theorem derivW_eps_nil : derivW [] .eps = .eps := by rw [derivW]

@[simp] theorem derivW_eps_cons (c : Char) (w : List Char) : derivW (c :: w) .eps = .nil := by
  rw [derivW]
  all_goals simp

theorem derivW_sym_nil (cls : Cls) : derivW [] (.sym cls) = sym cls := by rw [derivW]

theorem derivW_sym_one (c : Char) (cls : Cls) :
    derivW [c] (.sym cls) = if inCls c cls then .eps else .nil := by rw [derivW]

theorem derivW_sym_two (c d : Char) (w : List Char) (cls : Cls) :
    derivW (c :: d :: w) (.sym cls) = .nil := by
  rw [derivW]
  all_goals simp

theorem derivW_alt (w : List Char) (a b : RE) :
    derivW w (.alt a b) = alt2 (derivW w a) (derivW w b) := by rw [derivW]

theorem derivW_cut (w : List Char) (a b : RE) :
    derivW w (.cut a b) = cut2 (derivW w a) (derivW w b) := by rw [derivW]

theorem derivW_not (w : List Char) (r : RE) : derivW w (.not r) = not_ (derivW w r) := by
  rw [derivW]

theorem derivW_invHom (w : List Char) (h : List (Char × List Char)) (a : RE) :
    derivW w (.invHom h a) = invHom_ h (derivW (w.flatMap (applyHom h)) a) := by rw [derivW]

theorem derivW_seq (w : List Char) (a b : RE) :
    derivW w (.seq a b) =
      alt2 (seq2 (derivW w a) b)
        (altL ((List.range (w.length + 1)).map fun i =>
          if nullable (derivW (w.take i) a) then derivW (w.drop i) b else .nil)) := by
  rw [derivW]

theorem derivW_rep (w : List Char) (a : RE) :
    derivW w (.rep a) =
      altL ((if w.isEmpty then [rep_ a] else []) ++
        (List.range w.length).attach.map fun x =>
          if nullable (derivW (w.take x.1) (.rep a)) then
            seq2 (derivW (w.drop x.1) a) (rep_ a)
          else .nil) := by
  rw [derivW]

@[simp] theorem deriv_top (c : Char) : deriv c top = top := rfl

@[simp] theorem derivW_top (w : List Char) : derivW w top = top := by
  rw [show top = RE.not .nil from rfl, derivW_not, derivW_nilRE]; rfl

/-! ### Derivatives of a smart `sym` -/

theorem deriv_sym_smart (c : Char) (cl : Cls) :
    deriv c (sym cl) = if inCls c cl then .eps else .nil := by
  rw [Smart.sym_def]
  split
  · rename_i hemp
    rw [deriv_nil, if_neg (by simp [(Cls.isEmpty_iff cl).mp hemp c])]
  · rw [deriv_sym, inCls_norm]

theorem derivW_sym_smart_nil (cl : Cls) : derivW [] (sym cl) = sym cl := by
  rw [Smart.sym_def]
  split
  · rw [derivW_nilRE]
  · rename_i hemp
    rw [derivW_sym_nil, Smart.sym_def, if_neg (by rw [Cls.isEmpty_norm_eq]; exact hemp),
      Cls.norm_idem]

theorem derivW_sym_smart_one (c : Char) (cl : Cls) :
    derivW [c] (sym cl) = if inCls c cl then .eps else .nil := by
  rw [Smart.sym_def]
  split
  · rename_i hemp
    rw [derivW_nilRE, if_neg (by simp [(Cls.isEmpty_iff cl).mp hemp c])]
  · rw [derivW_sym_one, inCls_norm]

theorem derivW_sym_smart_two (c d : Char) (w : List Char) (cl : Cls) :
    derivW (c :: d :: w) (sym cl) = .nil := by
  rw [Smart.sym_def]
  split
  · rw [derivW_nilRE]
  · rw [derivW_sym_two]

/-! ### Canonicity of derivatives -/

theorem isCanon_derivW : ∀ (w : List Char) (x : RE), IsCanon x → IsCanon (derivW w x) := by
  intro w x
  induction w, x using derivW.induct with
  | case1 cls => intro _; rw [derivW_sym_nil]; exact isCanon_sym cls
  | case2 cls c hc => intro _; rw [derivW_sym_one, if_pos hc]; exact isCanon_eps
  | case3 cls c hc => intro _; rw [derivW_sym_one, if_neg hc]; exact isCanon_nil
  | case4 u cls h1 h2 =>
    intro _
    rw [derivW]
    · exact isCanon_nil
    · exact h1
    · exact h2
  | case5 u a b iha ihb => intro h; rw [derivW_alt]; exact isCanon_alt2 (iha h.1) (ihb h.2.1)
  | case6 u a b iha ihb => intro h; rw [derivW_cut]; exact isCanon_cut2 (iha h.1) (ihb h.2.1)
  | case7 u a b iha _ ihdrop =>
    intro h
    rw [derivW_seq]
    refine isCanon_alt2 (isCanon_seq2 (iha h.1) h.2.1) (isCanon_altL fun x hx => ?_)
    rw [List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    split
    · exact ihdrop i h.2.1
    · exact isCanon_nil
  | case8 u a _ ihdrop =>
    intro h
    rw [derivW_rep]
    refine isCanon_altL fun x hx => ?_
    rcases List.mem_append.mp hx with hx | hx
    · split at hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact isCanon_rep_ h.1
      · simp at hx
    · rw [List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      split
      · exact isCanon_seq2 (ihdrop i h.1) (isCanon_rep_ h.1)
      · exact isCanon_nil
  | case9 u a ih => intro h; rw [derivW_not]; exact isCanon_not_ (ih h.1)
  | case10 u hh a ih =>
    intro h
    rw [derivW_invHom]
    exact isCanon_invHom_ _ (by simpa using ih h.1)
  | case11 => intro _; rw [derivW_eps_nil]; exact isCanon_eps
  | case12 u hu =>
    intro _
    rw [derivW]
    · exact isCanon_nil
    · exact hu
  | case13 u => intro _; rw [derivW_nilRE]; exact isCanon_nil

theorem isCanon_deriv (c : Char) : ∀ {x : RE}, IsCanon x → IsCanon (deriv c x) := by
  intro x
  induction x with
  | sym cl => intro _; rw [deriv_sym]; split <;> [exact isCanon_eps; exact isCanon_nil]
  | alt a b iha ihb => intro h; rw [deriv_alt]; exact isCanon_alt2 (iha h.1) (ihb h.2.1)
  | cut a b iha ihb => intro h; rw [deriv_cut]; exact isCanon_cut2 (iha h.1) (ihb h.2.1)
  | seq a b iha ihb =>
    intro h
    rw [deriv_seq]
    split
    · exact isCanon_alt2 (isCanon_seq2 (iha h.1) h.2.1) (ihb h.2.1)
    · exact isCanon_seq2 (iha h.1) h.2.1
  | rep a iha =>
    intro h
    rw [deriv_rep]
    exact isCanon_seq2 (iha h.1) (isCanon_rep_ h.1)
  | not a iha => intro h; rw [deriv_not]; exact isCanon_not_ (iha h.1)
  | invHom hh a iha =>
    intro h
    rw [deriv_invHom]
    exact isCanon_invHom_ _ (isCanon_derivW _ _ h.1)
  | eps => intro _; rw [deriv_eps]; exact isCanon_nil
  | nil => intro _; rw [deriv_nil]; exact isCanon_nil

end Redgrep

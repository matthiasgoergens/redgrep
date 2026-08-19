import SatMain

/-!
# Saturated state sets: the finiteness engine for `Bounds.closure_finite`

Brzozowski finiteness for the v3 engine.  The proof is organised around a
*saturation* predicate `Sat U P` on sets of regexes (`ClosureSpan.lean`): `P`
is closed under one-character derivatives, word derivatives, immediate
subterms, the suffixes of its concatenation chains, and the "head step" that a
derivative of a concatenation performs; its `sym` states are bounded by a
fixed alphabet `U`, which makes `P` finite.  A saturated set containing `r`
contains every state the engine can reach from `r` (`Sat.derivs_mem`), and
`SatMain.exists_sat_set` builds one for every `r` by structural induction, so
the reachable-state set of any regex is finite.

Nothing here needs the ACI canonicity layer: the arguments are purely
structural, which is what makes them applicable to *arbitrary* (possibly
non-canonical) input terms.
-/

namespace Redgrep

/-- Every regex sits inside a saturated (hence finite) set of states. -/
theorem exists_sat (r : RE) : ∃ P : Set RE, P.Finite ∧ r ∈ P ∧
    ∀ x ∈ P, ∀ c, deriv c x ∈ P := by
  obtain ⟨P, hP, hr⟩ := exists_sat_set r
  exact ⟨P, hP.finite, hr, hP.deriv_mem⟩

/-- **Finiteness of the reachable-state set** (the engine-level statement of
`Bounds.closure_finite`). -/
theorem derivs_range_finite (r : RE) :
    (Set.range (fun u : List Char => u.foldl (fun t c => deriv c t) r)).Finite := by
  obtain ⟨P, hP, hr⟩ := exists_sat_set r
  refine Set.Finite.subset hP.finite ?_
  rintro x ⟨u, rfl⟩
  exact hP.derivs_mem hr u

end Redgrep

import Correctness
import ClosureSat
import Mathlib.Data.Set.Card

/-!
# The quantitative programme: closure bounds for the v3 engine (skeleton)

Brzozowski (1964): a regex has finitely many derivatives *up to ACI*.  The v3
engine implements the ACI quotient computationally (smart constructors keep
every derivative in canonical form), so its reachable-state set should be
finite outright, with per-constructor bounds.  This file states that
programme; everything is `sorry`, and the statements are the deliverable.

`B` below is the bounding function, with the classical recurrences:

* `B (not r) = B r` — complement toggles `nullable` only, states are shared;
* `B (alt r s)`, `B (cut r s)` `≤ B r * B s` — pair construction;
* `B (seq r s) ≤ B r * 2 ^ B s` — a derivative of `r·s` is `(d r)·s + Σ` over
  a *subset* of derivatives of `s`;
* `B (rep r) ≤ 2 ^ B r + 1` — sums of subsets of `(d r)·r∗`, plus `r∗` itself;
* leaves: `sym` has derivative closure `{sym, eps, nil}`, `eps` has
  `{eps, nil}`, `nil` has `{nil}`.

The `invHom` bound recorded here (`B r + 1`) is provisional: derivatives of
`invHom h r` are `invHom_ h` applied to word-derivatives of `r`, so its
closure is an image of `closure r` (with the possible collapses of
`invHom_`); pinning the exact constant is part of the proof burden.

Planned sharp cases, to be stated once the `Machine` constructor lands in v3
`Core.lean`:

* **machine**: a DFA node with state set `Q` has closure `≤ |Q| + 1` (the
  reachable states plus the dead state `nil`) — the whole point of embedding
  automata as primitives;
* **div7** (`divisibleBy 7`, base 10): closure exactly `9` (start state,
  7 residues counting the accepting one, dead state — measured on the Haskell
  side, to be re-derived here);
* **tightness**: the kth-from-last-is-`a` family `kthFromLast` below is the
  classical witness that the exponential in the `seq`/`rep` bounds is real:
  its closure has exactly `2 ^ (k + 1)` states (`≥` is the classical DFA
  lower bound; `≤` instantiates `closure_ncard_le`), so the bounds above are
  tight up to constants.
-/

open Language Computability

namespace Redgrep

/-- Iterated one-character derivative: the engine state after reading `u`
(Haskell `quotient`). -/
def derivs (r : RE) (u : List Char) : RE := u.foldl (fun t c => deriv c t) r

/-- The reachable derivative closure of `r`: every state the engine can be in
after reading some word, `r` itself included (`u = []`).  A `Set`, not a
`Finset`: finiteness is the theorem `closure_finite`, not a definition. -/
def closure (r : RE) : Set RE := Set.range (derivs r)

/-- The bounding function of the quantitative programme (see the module
docstring for the provenance of each recurrence). -/
def B : RE → Nat
  | .sym _ => 3
  | .alt r s => B r * B s
  | .cut r s => B r * B s
  | .seq r s => B r * 2 ^ B s
  | .rep r => 2 ^ B r + 1
  | .not r => B r
  | .invHom _ r => B r + 1
  | .eps => 2
  | .nil => 1

/-- Finiteness: the ACI-canonicalising engine reaches only finitely many
states.  (For the v2 engine without smart constructors this is *false* in
general — associativity alone regenerates unboundedly many terms — which is
exactly why v3 exists.)  Stated for arbitrary `r`: the raw initial term
adds at most one state, so finiteness is unconditional. -/
theorem closure_finite (r : RE) : (closure r).Finite :=
  derivs_range_finite r

/-- The quantitative bound, for canonical terms.  The `Canonical r`
hypothesis is NOT decorative: DeepSeek review 2026-08-18 refuted the
unguarded statement with `¬¬∅` and `∅|∅`, whose raw initial terms are
extra states the recurrences do not count (closure = 2, B = 1; confirmed
by six decide-measurements).  (`Set.ncard` is 0 on infinite sets, so this
is consumed together with `closure_finite`.) -/
theorem closure_ncard_le (r : RE) (h : Canonical r) :
    (closure r).ncard ≤ B r := by
  sorry

/-- Unguarded corollary form: canonicalise first, then the bound holds for
any input term. -/
theorem closure_canon_ncard_le (r : RE) :
    (closure (canon r)).ncard ≤ B (canon r) := by
  sorry

/-- The tightness witness: `Σ* a Σ^k` — "the (k+1)-th character from the end
is `a`".  Planned: its closure has exactly `2 ^ (k + 1)` states (each state
remembers which of the last `k + 1` positions carried an `a`). -/
def kthFromLast (k : Nat) : RE :=
  seqL (rep_ dot :: chr 'a' :: List.replicate k dot)

end Redgrep

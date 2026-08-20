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

/-- **The headline quantitative statement** (reformulated 2026-08-20 on
Aristotle's design review, aristotle/design-answers.md §2.2): a *spanning
set* — an explicitly finite set containing `r` and closed under one-step
derivatives, of size at most `B r`.

Why this shape rather than `(closure r).ncard ≤ B r`: `Set.ncard` is `0`
on infinite sets, so the inequality form is *implied by* infiniteness and
is only meaningful alongside `closure_finite`. The spanning form cannot be
satisfied vacuously, is strictly stronger, and is also the natural proof:
each constructor becomes a construction plus a closedness check, with the
exponentials falling out of `Finset.card_powerset` / `card_product`
(seq: index by `S_r × powerset S_s` via Brzozowski's shape theorem; rep:
`powerset S_r` plus `rep_ r`) instead of an arithmetic induction. It also
does not depend on `canon` being ACI-complete, only on the
smart-constructor derivative laws that everything else needs anyway.

The `Canonical` hypothesis stays: the raw initial term of a non-canonical
input is an extra state the recurrences do not count (the `¬¬∅` / `∅|∅`
refutation of 2026-08-18). The recommended structural fix is for the
engine entry point to canonicalise its input, at which point this
hypothesis disappears from user-facing statements — deferred, since it
changes `matchRE`. -/
theorem closure_spanned (r : RE) (h : Canonical r) :
    ∃ S : Finset RE, r ∈ S ∧ (∀ t ∈ S, ∀ c : Char, deriv c t ∈ S) ∧ S.card ≤ B r := by
  sorry

/-- Bridge: a spanning set contains the whole reachable closure (induction
on the word, using only membership and closedness). -/
theorem closure_subset_of_spanned (r : RE) (S : Finset RE)
    (hr : r ∈ S) (hclosed : ∀ t ∈ S, ∀ c : Char, deriv c t ∈ S) :
    closure r ⊆ (S : Set RE) := by
  sorry

/-- The cardinality bound, now a corollary of `closure_spanned` +
`closure_subset_of_spanned` rather than a headline. -/
theorem closure_ncard_le (r : RE) (h : Canonical r) :
    (closure r).ncard ≤ B r := by
  sorry

/-- The tightness witness: `Σ* a Σ^k` — "the (k+1)-th character from the end
is `a`".  Planned: its closure has exactly `2 ^ (k + 1)` states (each state
remembers which of the last `k + 1` positions carried an `a`). -/
def kthFromLast (k : Nat) : RE :=
  seqL (rep_ dot :: chr 'a' :: List.replicate k dot)

end Redgrep

import Correctness

/-!
# Proposed alternatives (all equivalences proved)

Nothing here changes the fixed definitions (`RE`, `lang`, `nullable`, the
`deriv` equations) or the four contract theorems in `Correctness.lean`; every
item below is an *addition* accompanied by a proof relating it to the current
definitions.  Each proposal states why it looks preferable for the planned
extensions (a DFA `machine` constructor, evidence-carrying variants).

Summary of the proposals:

1. `derivW` (already in `Core.lean`) as the *primitive* of the engine, with the
   one-character `deriv` recovered from it.  Justification: `lang_derivW`,
   `lang_derivW_singleton`, `derivW_append_lang`.
2. `matchW`, matching by one word derivative instead of a fold of
   one-character derivatives.  Justification: `matchW_correct`,
   `matchW_eq_matchRE`.
3. `nullable_derivW`: `nullable (derivW u r)` *is* the membership test — the
   engine's state after reading `u` characterises the residual language.
4. A `Decidable` instance for `w ∈ lang r`, i.e. the executable engine
   exported as decidability of the specification.  This is the cheapest
   "evidence-carrying" step: any future parser/witness variant can be checked
   against it.

Unproved suggestions are collected in the comment block at the end of the file.
-/

open Language Computability

namespace Redgrep

/-! ### 1. `derivW` as the primitive -/

/-- Deriving by a one-letter word agrees (semantically) with the structural
one-character `deriv`.  So `deriv` need not be a separate recursion at all: it
could be *defined* as `derivW [c]`, and the current per-constructor equations
kept as (semantic) lemmas.  We do not do this in `Core.lean` because the
contract requires the existing equations to hold syntactically. -/
theorem lang_derivW_singleton (c : Char) (r : RE) :
    lang (derivW [c] r) = lang (deriv c r) := by
  rw [lang_derivW, lang_deriv]
  rfl

/-- The word derivative composes, which is what makes a "read a whole word in
one step" engine (and a future DFA `machine` node, whose word derivative is
just running the automaton on the word) coherent. -/
theorem derivW_append_lang (u v : List Char) (r : RE) :
    lang (derivW (u ++ v) r) = lang (derivW v (derivW u r)) := by
  rw [lang_derivW, lang_derivW, lang_derivW]
  ext w
  show (u ++ v) ++ w ∈ lang r ↔ u ++ (v ++ w) ∈ lang r
  rw [List.append_assoc]

/-! ### 2. Matching by a single word derivative -/

/-- Proposed alternative matcher: derive by the whole input word at once.
Compared with `matchRE` it needs no fold, it extends verbatim to constructors
whose *word* derivative is cheaper than iterated character derivatives
(`invHom`, and a future embedded DFA `machine`), and its correctness proof is a
one-liner from `lang_derivW`. -/
def matchW (r : RE) (s : List Char) : Bool := nullable (derivW s r)

/-- The state of the engine after reading `u` is nullable exactly when `u` is
matched: the semantic characterisation of `derivW`. -/
theorem nullable_derivW (u : List Char) (r : RE) :
    nullable (derivW u r) = true ↔ u ∈ lang r := by
  rw [nullable_correct, lang_derivW]
  show u ++ [] ∈ lang r ↔ u ∈ lang r
  rw [List.append_nil]

theorem matchW_correct (r : RE) (s : List Char) : matchW r s = true ↔ s ∈ lang r :=
  nullable_derivW s r

/-- The two matchers agree, so `matchW` is a drop-in replacement for
`matchRE`. -/
theorem matchW_eq_matchRE (r : RE) (s : List Char) : matchW r s = matchRE r s := by
  rw [Bool.eq_iff_iff, matchW_correct, matchRE_correct]

/-! ### 3. The engine as a decision procedure -/

/-- Membership in the *specification* `lang r` is decidable, by running the
engine.  Exporting the engine this way is the first step towards
evidence-carrying variants: a future parser can be validated against
`decide (w ∈ lang r)`. -/
instance decidableMemLang (r : RE) (s : List Char) : Decidable (s ∈ lang r) :=
  decidable_of_iff _ (matchRE_correct r s)

example : (['a', 'b'] : List Char) ∈ lang (.seq (.sym (· == 'a')) (.sym (· == 'b'))) := by
  decide

/-!
### Further suggestions (not formalised here)

* **Generalise the alphabet.**  `RE` is hard-wired to `Char`.  Making it
  `RE α` (with `sym : α → Bool`) costs nothing in the proofs above — every
  argument in `Correctness.lean` is alphabet-agnostic — and it is what makes a
  `machine` constructor pleasant: an embedded DFA is naturally
  `{ σ : Type } × (σ → α → σ) × ...`, and one usually wants to test the engine
  on small alphabets such as `Fin 2`.

* **A `machine` constructor fits the `derivW` shape.**  With `derivW` as the
  primitive, `derivW u (machine M q) = machine M (M.run q u)`, a *word* step,
  which is exactly the case that iterated one-character derivatives make
  quadratic.  This is the main reason for proposal 1.

* **`sym` as `α → Bool` vs. `Pos`/`Neg` sets.**  Keeping the predicate form in
  the twin is right, but a `Decidable`-predicate wrapper
  (`sym (p : α → Prop) [DecidablePred p]`) would let the twin state character
  classes the way the Haskell side normalises them without losing
  executability.

* **Smart constructors.**  `altFold` above builds right-nested `alt`s with
  `nil` leaves; a smart `alt`/`seq` (absorbing `nil`, unit `eps`) would keep
  the residuals small.  Since all the correctness statements are about `lang`,
  such constructors only need `lang (smartAlt a b) = lang (.alt a b)` and slot
  into the existing proofs unchanged.

* **Evidence-carrying matching.**  `matchRE_correct` is a `Bool ↔ Prop`
  statement; a variant returning `Decidable (s ∈ lang r)` (see
  `decidableMemLang`) or a parse witness for `seq`/`rep` would be a strictly
  stronger interface, and the `kstar_split` lemma in `Correctness.lean` already
  produces the split point needed for a `rep` witness.
-/

end Redgrep

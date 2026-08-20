# Design consultation — answers

Reviewed: `Core.lean`, `Semantics.lean`, `Statements.lean`, `Bounds.lean`, and
`lakefile.toml` as they stand in this tree. (Note that `Bounds.lean` imports
`Correctness` and `ClosureSat`, and the lakefile lists 28 libraries, most of
which are not in this snapshot; where a remark might be overtaken by code I
cannot see, I say so.) Nothing below was proved; a handful of small factual
claims about the pinned Mathlib were checked in a scratch buffer and are
flagged as such. No `.lean` file was modified.

Frankness was requested, so this is written as criticism rather than as
appreciation. The overall shape — binary AST, smart-constructor layer,
denotation into `Language Char`, quantitative programme kept separate — is
sound, and most of what follows is about *where the layer boundaries are*
rather than about the layers themselves.

---

## 1. The definitions

### 1.1 The single biggest source of friction: `Canonical` as a fixed point

`Canonical r := canon r = r` is the definition that costs the most, and it
costs it everywhere. Three separate problems:

**It cannot be inverted.** A hypothesis `canon r = r` tells you nothing you can
case on. Every proof that needs "the members of this union are sorted,
duplicate-free, contain no `nil`, contain at most one `sym`, and none of them
is itself an `alt`" has to re-derive those facts by unfolding `canon`, which
unfolds `alt2`, which unfolds `altL`, which is a `partition` followed by a
`foldl` over `Cls.union` followed by `mergeSort` followed by `dedup`. There is
no way to make that pleasant. An *inductive* `Canonical` — a grammar of normal
forms, with a separate clause for the shape of a canonical `alt` chain, a
canonical `cut` chain, a canonical `seq` chain, a canonical hom list — gives
you inversion lemmas for free, and it is the form every downstream proof
actually wants.

**Its two key theorems are hidden.** With the fixed-point definition, the facts
you need are `canon (canon r) = canon r` (idempotence) and
`Canonical r → Canonical (deriv c r)` (preservation). Idempotence is a genuinely
hard combinatorial statement about `altL`: the `sym`-merge changes the member
multiset, and in principle a merge can expose new flattening opportunities, so
you cannot separate "sort/dedup is idempotent" from "merge is stable". With an
inductive `Canonical` you instead prove the two *separate* statements
`Canonical (canon r)` and `Canonical r → canon r = r`, and idempotence is a
one-line corollary. That is a strictly easier decomposition of the same work,
and it is the change I would make first, because it is cheap (it does not touch
the type, the engine, or any statement outside the ACI files).

**Preservation is a hard gate that everything in `Bounds.lean` sits behind.**
`closure_ncard_le` assumes `Canonical r`, but the proof needs
`Canonical (derivs r u)` for every `u`, i.e. preservation under `deriv`, which
in turn needs "every smart constructor returns a canonical term when given
canonical arguments". That is the whole ACI programme. See §2.3: I think the
bounds can and should be restated so that they do not depend on it at all.

### 1.2 Predicate vs subtype vs quotient

My verdict, in order of the layer they belong to:

* **Predicate (inductive, not fixed-point) — yes, at the bottom.** This is the
  right implementation-level notion, for exactly the reason your module
  docstring gives: `deriving DecidableEq`, structural recursion and structural
  induction on `RE` all stay free, and `lake build` works today. Do not give
  that up.

* **Subtype `CRE := {r // Canonical r}` — yes, as the *interface*, but only
  after preservation is proved.** Before preservation, the subtype is pure
  overhead: you cannot even define `deriv : CRE → CRE`. After preservation, it
  pays for itself immediately and repeatedly: `Bounds` loses its `Canonical`
  hypotheses, `closure` lands in a type where the ACI invariant is not
  something a lemma can forget, `DecidableEq` is inherited via `Subtype`, and
  the awkward `closure_canon_ncard_le` corollary disappears because the entry
  point (`matchRE`, and whatever the public API is) takes a `CRE` built by
  smart constructors. The natural staging is: raw `RE` + inductive `Canonical`
  as the implementation, `CRE` with smart constructors as its only introduction
  forms as the exported interface, and `Core.lean`'s raw constructors made
  `private`/unexported outside the ACI files.

* **Quotient — no, not as the primary type; possibly later as a derived view.**
  A quotient by ACI-equivalence is what the *mathematics* of Brzozowski's
  finiteness theorem is about, and it is tempting for that reason. But for an
  executable twin it is the wrong first move: every operation must be defined
  by `Quotient.lift`, and the congruence obligation for `deriv` ("ACI-equal
  regexes have ACI-equal derivatives") must be discharged *at definition time*,
  before you have any lemmas about `deriv` to discharge it with. That is
  inverting the dependency order of the whole project. If you later want the
  quotient — and for the *sharp* constants (`div7 = 9`) you probably do — define
  it downstream and prove that `deriv` descends, once the smart-constructor
  lemmas exist. Treat it as a theorem, not as a datatype.

### 1.3 Binary constructors + `canon` vs sorted-list fields vs `Finset`

I agree with your call, and for the reason you give: a `Finset RE` field is a
nested inductive through a quotient and is genuinely blocking, and a
`List RE` field kills `deriving DecidableEq` and forces manual nested
recursion everywhere. Keep binary constructors.

But I would change *where the n-ary structure lives in the proofs*. Right now
`altToList`/`altOfList`/`sortDedup` are three functions with no theory
connecting them, and every ACI argument is therefore a list-permutation
argument done by hand. The cheap improvement is:

1. Prove `RE.cmp` lawful (§1.4) and register a genuine `LinearOrder RE`.
2. Define the *canonical view* of a union as a `Finset RE` — `altSet : RE →
   Finset RE` (= `(altToList r).toFinset`) — and prove the round-trip
   `Canonical r → altOfList (sortDedup (altSet r).toList) = r`, plus
   `altSet (altL L) = ...` in terms of `Finset` union.
3. Then state every ACI law as a `Finset` fact. Associativity, commutativity
   and idempotence of `alt2` become `Finset.union_assoc`, `union_comm`,
   `union_idem` transported along the view, instead of `List.Perm` reasoning
   plus `mergeSort` stability lemmas.

That is: binary in the *type*, `Finset` in the *view*, sorted lists only as an
implementation detail of the executable normaliser and never mentioned in a
downstream statement. The pain you are feeling is not binary-vs-n-ary; it is
that the two representations meet with no interface between them.

### 1.4 `RE.cmp` has no laws, and everything depends on them

"Its lawfulness … is later proof work, not assumed by the engine" is true of the
engine and false of the *proofs*. `sortDedup` produces a strictly ascending
duplicate-free list only if `cmp` is transitive, antisymmetric, total, and —
crucially — *compatible with equality* (`cmp a b = .eq ↔ a = b`). Without
`IsTotal`/`IsTrans` instances for `RE.le` you cannot even apply Mathlib's
`mergeSort` sortedness and permutation lemmas, so you cannot state, let alone
prove, that `canon` produces a sorted term. This is a load-bearing hole, and it
is upstream of everything in §1.1.

Concretely, `cmp`'s lawfulness bottoms out in `Cls.cmp`, which compares
`Finset.sort` outputs with `compare` on `List Char`; that is fine
(`Finset.sort` is injective, and the list order is lexicographic) but it is
several lemmas, and `cmpHom` on association lists is several more. I would
either (a) prove the three laws once and package them as a `LinearOrder RE`
instance so that the rest of the development uses `≤`/`<` and Mathlib's order
API rather than a bare `Ordering`, or (b) sidestep by defining an injective
encoding `RE → ℕ` (or into a `List ℕ` with a known `LinearOrder`) and getting
the order via `LinearOrder.lift'`. (a) is more work but keeps the comparator
efficient and mirrors Haskell's derived `Ord`; (b) is faster to get right. Either
way, do it *before* the ACI files, not after — right now those files are being
written on top of an unproved order.

### 1.5 `Cls`: the `charCount` fullness test is a real gap

`Cls.isFull (.pos s) := decide (s.card = charCount)` with
`charCount := 1112064` is an unbacked bridge between a numeral and the actual
type `Char`. To use it in any semantic proof you need

```
∀ s : Finset Char, s.card = charCount → ∀ c, c ∈ s
```

which requires `Fintype Char` together with `Fintype.card Char = charCount`.
I checked against the pinned Mathlib: there is no `Fintype Char` instance and
no `Fintype UInt32` either, and `deriving instance Fintype for Char` fails
(it reduces to `Fintype ((val : UInt32) × PLift val.isValidChar)`, which is not
synthesisable). So this must be built by hand — `Fintype UInt32` from
`Fin 2^32`, then `Char` as a decidable subtype — and the cardinality fact must be
proved *arithmetically* (`0x110000 - 0x800`, as two `Finset.Ico` blocks), never
by `decide`: `Finset.univ : Finset UInt32` has four billion elements and any
kernel evaluation over it is fatal. Your lakefile already reserves a `CharCard`
library; I would treat it as a prerequisite of the `Cls` files rather than as
parallel work, because until it exists, `sym`, `Cls.norm` and hence `altL`'s
`sym`-merge have no provable specification.

There is a cheaper escape if you want one: drop the `pos`-side fullness test
(`isFull (.pos _) := false`), so that the only canonical representation of the
full class is `neg ∅`, and accept that a `pos` set literally enumerating all of
Unicode is not canonicalised. Canonicity then remains a theorem, the pathological
input is unreachable in practice, and `charCount` disappears from the trusted
surface entirely. I would take that trade unless the Haskell twin's behaviour on
that input is observable.

Separately, and independently of the above: `Cls` needs a **semantic
membership API before anything else uses it**. Define `Cls.mem : Cls → Set Char`
(or keep `inCls` and use it), then prove `inCls c (union a b) = inCls c a ||
inCls c b`, the same for `inter` and `compl`, `isEmpty_iff`, `isFull_iff`, and
`norm` correctness. Right now `union`/`inter` are four-case pattern matches
whose correctness has to be re-established in situ by every downstream lemma.
With ten lines of API you get, in effect, that `Cls` is a Boolean algebra, and
then `altL`'s `cs.foldl Cls.union c` is a `sup` over a list — at which point its
independence from the order of the flattened member list is `Finset.sup`
commutativity rather than a bespoke argument. As written, that fold's result is
order-dependent unless `Cls.union` is known associative and commutative, and
`partition` gives you the members in an order you have not controlled. That is a
latent bug as much as a proof obligation.

### 1.6 The assoc-list homomorphism: right call, wrong invariant

Carrying the hom as `List (Char × List Char)` rather than a function is
correct — `DecidableEq` is worth more than elegance here, and the whole
closure programme needs it. But the canonical form is not quite right:

`applyHom` is *first hit wins*, i.e. order-sensitive, while `invHom_` sorts the
list by `cmpHomEntry` (key, then image). So for a list with a duplicate key and
two different images, `invHom_ h r` and `.invHom h r` can denote **different
languages**, and `canon` is then not language-preserving. The docstring calls
duplicate keys "the caller's mistake and merely tolerated", but `canon`'s
correctness theorem (`lang (canon r) = lang r`) is stated for all terms, so the
mistake becomes yours. Two clean fixes:

* make `invHom_` deduplicate *by key* (keeping the first occurrence) before
  sorting, so normalisation preserves `applyHom`'s meaning; and
* add key-uniqueness to the inductive `Canonical` (§1.1) so that downstream
  proofs may assume it and `applyHom` becomes order-independent — at which
  point `applyHom` can be specified as a partial function `Char →. List Char`
  extended by identity, which is much easier to reason about than "find? on a
  list".

If you want the invariant enforced rather than assumed, a
`Hom := {l : List (Char × List Char) // sortedKeys l ∧ noIdentityEntries l}`
subtype still derives `DecidableEq`, and costs one `Subtype.ext` per
construction.

One missing normalisation while you are there: `invHom_ g (invHom_ h r)` should
compose to a single node (`invHom_ (h ∘ g)`, suitably tabulated over the finite
domain), otherwise nested inverse homomorphisms stack and the closure of a
nested term is not the image of a single closure — which is exactly what the
`B (invHom _ r) = B r + 1` recurrence in `Bounds.lean` implicitly assumes.

### 1.7 `derivW` as a structural primitive: the honest analysis

This is the definition I would most like to change and am least sure how to.

The problem it solves is real: `deriv c (.invHom h r)` needs
`∂_{h c} r`, i.e. a *word* derivative, and the obvious definition
`derivW u r = u.foldl (flip deriv) r` is not structurally decreasing — the smart
constructors can *grow* a term (`deriv c (rep r) = seq2 (deriv c r) (rep_ r)`),
so no `sizeOf`-based measure works. Your solution — define `derivW` directly by
structural recursion, enumerating all splits in the `seq` and `rep` cases, with
measure `(sizeOf r, u.length)` — does terminate, which is not nothing.

But the price is high and it is paid by every proof downstream:

* No `rfl` equations. `deriv`'s equation lemmas are `rfl` and you record them
  as `simp` lemmas; `derivW`'s come out of well-founded recursion and are
  painful to rewrite with, and the `rep` case with `List.range … |>.attach` is
  worse still.
* `deriv` calls `derivW` at `invHom`, so *every* statement about `deriv`
  inherits the pain at that one constructor.
* Semantically, `derivW u` and `u.foldl (flip deriv)` should agree, but they
  are *syntactically different functions*, and the closure programme needs the
  agreement (see §2.5). So you end up owing the lemma anyway, and the split
  enumeration bought you nothing but a definition that typechecks.

The three principled alternatives, with my ranking:

1. **`Machine` leaves absorb `invHom` (best, and it is already on your
   roadmap).** For a DFA leaf, `invHom h (machine M)` is just `machine (M ∘ h)`:
   compose the transition function with the hom, precomputed. If `invHom` is
   only ever applied to sub-engines that can be compiled to a `Machine`, the AST
   node — and with it the entire word-derivative primitive — disappears. This
   also makes the `invHom` state bound exact instead of provisional. It is a
   bigger change but it removes a whole category of pain.

2. **Fuel indexed by hom-nesting depth (tactical fix, keeps the node).**
   Smart constructors never *create* `invHom` nodes, so the hom-nesting depth of
   any derivative of `r` is at most that of `r`. That is the measure that
   actually decreases, but it is a theorem about the function being defined, so
   it is not available at definition time. The standard workaround: define
   `derivAux : Nat → Char → RE → RE` with fuel bounding the hom depth,
   set `deriv c r := derivAux (homDepth r) c r`, and prove a fuel-irrelevance
   lemma (`homDepth r ≤ n → derivAux n c r = derivAux (homDepth r) c r`) once.
   Then `derivW u r = u.foldl (flip (derivAux n)) r` is a plain fold, all the
   classical Brzozowski equations hold by `rfl` or one `unfold`, and the split
   enumeration becomes a *theorem* you prove only if you want it.

3. **Keep the current definition, but immediately prove the bridge**
   `lang (derivW u r) = Language.leftQuotient (lang r) u`
   and `lang (u.foldl (flip deriv) r) = Language.leftQuotient (lang r) u`,
   and thereafter reason semantically and never unfold `derivW` again.
   This is the cheapest thing to do today and is worth doing regardless of
   whether you also do (1) or (2). Note that syntactic equality of the two
   functions is *not* likely to hold on the nose (the split enumeration builds a
   different `altL` chain); before investing in it, check it by evaluation on a
   dozen small terms, and if it fails, state the bridge as equality of `canon`
   images or as language equality only.

### 1.8 Naming, which is a correctness issue and not a style issue

`Redgrep.sym` (smart) and `RE.sym` (constructor) are different functions with
the same last component; the same holds for `not_`/`RE.not` (less dangerous,
because of the underscore) and, worst of all, `Redgrep.derivW` and the
root-level `derivW` in `Statements.lean`, which `Semantics.lean` imports. Your
own `deriv_sym` simp lemma is stated about `RE.sym` and will silently fail to
fire on terms built by the smart `sym` — which is *all terms the engine
produces*. That class of near-miss is the most expensive kind of bug in a
development like this, because it presents as "the proof is hard" rather than as
an error. Rename the smart constructors (`mkSym`, `mkAlt`, `mkSeq`, `mkRep`,
`mkNot`, `mkInvHom`) or put them in a `Smart` namespace, and rename the
language-level operations in `Statements.lean` into a `Lang` namespace
(`Lang.deriv`, `Lang.derivWord`, `Lang.invHom`, `Lang.reverse`). Ten minutes,
and it removes a permanent hazard.

---

## 2. The bounds programme

### 2.1 Is a per-constructor `B` over the syntactic closure the natural object?

For *this* project, yes — with one large caveat about how it is **stated**, and
one about what it is **proved from**.

It is the natural object because the deliverable is a claim about *your engine*:
how many distinct states the ACI-canonicalising derivative machine can occupy.
That is a property of `deriv` and the smart constructors, not of the language,
and no NFA-based formulation can substitute for it. If you switched to a
Thompson/Glushkov NFA plus subset construction you would be proving a classical
theorem about a construction you do not run — a fine thing to have, but not this
programme, and it would leave the engine's own state count unmeasured.

### 2.2 But the statement should not be an `ncard` inequality

`Set.ncard` is `0` on infinite sets, so

```
theorem closure_ncard_le (r) (h : Canonical r) : (closure r).ncard ≤ B r
```

is *implied by* `(closure r).Infinite`. As a statement it is only meaningful in
conjunction with `closure_finite`, which the docstring acknowledges, but it is
better not to have a headline theorem that is vacuously satisfiable. Restate it
as a spanning-set claim:

```
theorem closure_spanned (r : RE) :
    ∃ S : Finset RE, r ∈ S ∧ (∀ t ∈ S, ∀ c, deriv c t ∈ S) ∧ S.card ≤ B r
```

with `closure r ⊆ ↑S` and both `closure_finite` and the cardinality bound as
one-line corollaries (`closure r ⊆ ↑S` follows by induction on the word, using
only `r ∈ S` and closedness). This is strictly stronger, it cannot be satisfied
vacuously, it eliminates the `Set.ncard` wart, and — the real point — it is
*also the natural proof*.

### 2.3 The spanning-set reformulation is what makes the exponentials painless

Trying to bound `(closure (seq r s)).ncard` directly is hopeless, because
`closure` is defined as a range and there is no handle on it. With spanning
sets, each constructor is a construction plus a closedness check, and the
exponentials fall out of `Finset` cardinality lemmas rather than out of an
induction:

* **`seq r s`.** Brzozowski's shape theorem says every derivative of `r·s` is
  `(∂_u r)·s` plus a union of *some subset* of derivatives of `s`. So take the
  index set `S_r × Finset.powerset S_s` and the map
  `fun (t, T) => alt2 (seq2 t s) (altL T.toList)`. Then
  `card ≤ S_r.card * 2 ^ S_s.card ≤ B r * 2 ^ B s` is
  `Finset.card_image_le` + `Finset.card_product` + `Finset.card_powerset` —
  no arithmetic induction at all. Closedness under `deriv` is the derivative
  identity for `seq`, plus the fact that `deriv` distributes over `altL`.

* **`rep r`.** Index set `Finset.powerset S_r`, map
  `fun T => altL ((T.image (fun t => seq2 t (rep_ r))).toList)`, plus the single
  extra element `rep_ r`; `2 ^ B r + 1` is again a `card_powerset`.

* **`alt`/`cut`.** Index set `S_r × S_s`, giving `B r * B s`.

* **`not`.** Image of `S_r` under `not_`; the bound is `B r` because complement
  toggles nullability only — but note that this needs `not_` injective on the
  relevant set, or you get `≤` for free anyway (which is all you want).

The important structural consequence: **the spanning-set formulation does not
need `canon` to be an ACI-complete normaliser, and it does not need
`Canonical` preservation.** All it needs is that the explicitly-constructed
finite set is literally closed under `deriv`. What it *does* need is a family of
lemmas of the form

```
deriv c (altL L) = altL (L.map (deriv c))
deriv c (seq2 x y) = ...            -- the smart-constructor derivative laws
```

i.e. "`deriv` commutes with the smart constructors". Those are about as much
work as canonicity preservation, but unlike canonicity preservation they are
*directly* what every bound uses, and they are also what the correctness proof
(`lang (altL L) = ⨆ …`) wants. I would make this family — smart-constructor
language laws and smart-constructor derivative laws — the central API of the
project, mark `altL`, `cutL`, `canon` `irreducible` once it is proved, and never
unfold them again.

Doing this also dissolves the `¬¬∅` / `∅|∅` counterexample cleanly. That
counterexample is really telling you that *the engine's entry point should
canonicalise its input*: if `matchRE r` is defined as iterating from `canon r`,
then "the state is always canonical" is true by construction, the raw initial
term is not a state, and `Canonical` never appears in a user-facing statement.
Alternatively state the unconditional bound as `≤ B (canon r) + 1` and be done.
Both are better than a `Canonical` side condition on the headline theorem.

### 2.4 Antimirov, similarity, NFAs — what each is actually good for

* **Antimirov partial derivatives.** Very attractive for the `∪, ·, *`
  fragment: `pd : Char → RE → Finset RE` needs no canonicalisation whatsoever,
  and the closure is bounded *linearly* by the number of symbol occurrences.
  The fatal objection for redgrep: there is no clean partial-derivative theory
  for **complement and intersection** — those are precisely the operators the
  engine exists for, and to complement a set of partial derivatives you must
  determinise, which puts the exponential back and adds a second layer. So: do
  not move the main programme to Antimirov. *Do* borrow its idea for the
  exponential cases — the subsets appearing in the `seq`/`rep` spanning sets in
  §2.3 are exactly "sets of partial derivatives", and thinking of them that way
  is what makes the construction obvious.

* **Closure modulo similarity rather than modulo `canon`.** Modulo `canon` is
  the honest object because it is what the engine computes, and (per §2.3) the
  upper bounds do not need `canon` to be complete for ACI. A coarser
  similarity quotient buys you *smaller* constants and nothing else, at the cost
  of a decidable congruence and quotient machinery. Reserve it for the sharp
  results (`div7 = 9`), where you genuinely need "no two of these states are
  equal", and even there the Myhill–Nerode route below is better.

* **NFA construction.** Not for the upper bounds, for the reason in §2.1. But
  Mathlib's `Mathlib/Computability/MyhillNerode.lean` (checked in the pinned
  version) is directly useful for the *lower* bounds — see §2.6.

### 2.5 Two prerequisites the current `B` quietly assumes

* `B (invHom h r) = B r + 1` assumes that the closure of `invHom h r` is the
  `invHom_ h`-image of the *word*-derivative closure of `r`, and that the word
  closure coincides with the character closure — i.e. `∂_{uv} = ∂_v ∘ ∂_u`
  **syntactically**, which is the bridge lemma of §1.7. Until that exists, the
  `invHom` recurrence is not merely "provisional", it is not yet a statement
  whose proof has a route. Prioritise the bridge.

* `B` is not `canon`-invariant (`B (alt eps eps) = 4` while
  `B (canon (alt eps eps)) = 2`), so `closure_canon_ncard_le` is not obviously
  stronger or weaker than `closure_ncard_le`; it is a different statement. If
  the intended reading is "the user hands us any term and we promise a bound",
  the honest form is `(closure r).ncard ≤ B (canon r) + 1` — with the `+1` for
  the uncanonicalised initial term — or, better, canonicalise at the entry point
  and drop the corollary.

### 2.6 Tightness: state it via distinguishability, not via syntax

For `kthFromLast k`, state

```
theorem closure_kthFromLast (k : Nat) : (closure (kthFromLast k)).ncard = 2 ^ (k + 1)
```

and prove the two directions by completely different means.

`≤` instantiates the spanning-set lemma of §2.3.

`≥` should **never** be attempted by syntactic inspection — that way you are
proving that `2^(k+1)` explicitly-written regexes are pairwise distinct, i.e.
you are back in ACI-completeness territory. Prove it semantically instead. The
reusable lemma to add now is:

```
theorem card_le_closure_of_distinguishable (r : RE) (U : Finset (List Char))
    (h : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ∃ w, matchRE r (u ++ w) ≠ matchRE r (v ++ w)) :
    U.card ≤ (closure r).ncard
```

Its proof is three lines of principle: `u ↦ derivs r u` maps `U` into
`closure r`; if `derivs r u = derivs r v` then `matchRE r (u ++ w) =
matchRE r (v ++ w)` for every `w` (by `matchRE`'s definition as
`nullable ∘ derivs` and the fold-append law); so the map is injective on `U`.
It needs no canonicity, no ACI, and no `lang`. Then:

* **tightness**: take `U = {a,b}^{k+1}` (all words of length `k+1` over two
  letters); two distinct bit patterns differ at some position `i`, and the
  distinguishing word is `b^i`. `U.card = 2^(k+1)` is `card_pow`-style
  bookkeeping.
* **`div7 = 9`**: take the nine words reaching the nine distinct states, with
  explicit distinguishing suffixes. Same lemma, different `U`.

If you would rather route through the language, Mathlib gives you the other
half for free: `Language.leftQuotient`, `Language.toDFA`, and
`isRegular_iff_finite_range_leftQuotient` are all present in the pinned
version. Once you have `lang (derivs r u) = (lang r).leftQuotient u` — which is
the natural corollary of engine correctness — the Myhill–Nerode index
`(Set.range (lang r).leftQuotient).ncard` is the image of `closure r` under
`lang`, hence a lower bound on it. That gives `≥` from a purely
language-theoretic argument, with `closure r` never inspected. I would state
`lang (derivs r u) = (lang r).leftQuotient u` as a named theorem regardless of
which route you take for tightness; it is the single cleanest statement of what
the engine is, and it connects your development to Mathlib's automata theory in
one line.

---

## 3. Evidence: parse witnesses and refutations

### 3.1 One family indexed by polarity, not two mutually-defined families

Two mutually-defined inductive families `Parse`/`Refute` express the duality
correctly, but in Lean they cost you the thing you most need: a usable
induction principle. Mutual inductives do get mutual recursors, but they are
clunky to drive, `induction` needs help, and every lemma about the pair has to
be stated as a conjunction and proved by the mutual eliminator by hand.

I would use **one inductive family indexed by a polarity**:

```
inductive Ev : Bool → RE → List Char → Type
```

with `Ev true r w` = "structured proof that `w` matches `r`" and `Ev false r w`
= "structured refutation". Then:

* `not` is two clauses, `Ev false r w → Ev true (.not r) w` and
  `Ev true r w → Ev false (.not r) w`, and the De Morgan swap you want is
  literally the index flip — the "complement swaps the two" theorem is `rfl`.
* You get **one** derived recursor, so every soundness/completeness proof is a
  single `induction`, with the polarity generalised. This is the decisive
  practical advantage and it is worth quite a lot.
* Duality is visible in the constructor list, which is a documentation win:

  | node | `Ev true` | `Ev false` |
  |---|---|---|
  | `alt` | a choice of disjunct | a **pair** of refutations |
  | `cut` | a pair | a **choice** of conjunct + its refutation |
  | `eps` | `w = []` | a witness `w = c :: v` |
  | `nil` | (none) | trivial |
  | `sym` | `w = [c]`, `inCls c cls` | either `w` is not one char, or it is `[c]` with `¬ inCls c cls` |
  | `invHom` | `Ev true r (w.flatMap (applyHom h))` | ditto at `false` |
  | `seq` | a split + two parses | **all** splits refuted (see below) |
  | `rep` | a list of parses of nonempty chunks | **all** first chunks refuted |

Two things I would *not* do:

* **Do not put `w ∉ lang r` inside the refutation type.** "Membership implies
  `False` plus structure" mixes `Prop` and `Type`, makes the family
  non-inspectable (you cannot case on the `Prop` field to extract blame), and
  makes it impossible to compute with. Keep `Ev` purely structural and prove
  `Ev false r w → w ∉ lang r` (and `Ev true r w → w ∈ lang r`) as *theorems*.
  Those two are one mutual induction with the polarity index — again the payoff
  of the single family.

* **Do not index by the derivative history.** A "run of the derivative
  automaton" (a list of states plus the final nullability check) is trivially
  produced by the engine but is not a typed parse tree, and reconstructing a
  tree from it is where the real work is. See §3.3.

### 3.2 The `seq` and `rep` negative cases, concretely

This is the genuinely hard part, and it is hard for a logical reason:
refuting a concatenation is *universally* quantified over splits, so the
refutation is intrinsically a function, or a table, rather than a single tree.

Two encodings, and I would take the second:

* **Higher-order:** `(∀ u v, w = u ++ v → Ev false r u ⊕ Ev false s v) →
  Ev false (.seq r s) w`. Honest, but the premise is a function type, which
  makes the family's recursor higher-order, destroys any hope of
  `DecidableEq`/finiteness of evidence, and makes evidence non-serialisable —
  a real concern if the point is to hand refutations to a user.

* **Tabulated:** carry one entry per split, over the *finite decidable* index
  set `List.range (w.length + 1)`, as a first-order structure (a length-indexed
  vector, or a `List.Forall`-style heterogeneous list over `splits w`). The
  evidence is then a finite tree, printable, comparable, and the recursor stays
  first-order. Provide `ofFun`/`toFun` bridges to the higher-order view for
  proofs that want it.

Note that the tabulated form is *exactly* the split enumeration your `derivW`
already performs for `seq` — which is a good sign that the engine can produce it,
and is an argument for keeping that enumeration somewhere even if `derivW`
itself is redefined (§1.7).

For `rep` the negative case must be recursive in the word rather than in a
decomposition: `Ev false (.rep r) (c :: w)` should say "for every *nonempty*
prefix `p` of `c :: w`, either `Ev false r p` or `Ev false (.rep r) (suffix)`".
The self-reference is at a strictly shorter word and occurs strictly
positively, so it is a legal inductive family; the essential detail is to
**exclude the empty first chunk explicitly**, otherwise the constructor refers
to itself at the same index and you have a clause that is at best useless and
at worst confusing. (Mirror `kstar_nonempty_chunks` in `Statements.lean`, which
already establishes precisely the nonempty-chunk characterisation you need for
the positive side; the negative side is its De Morgan dual.)

### 3.3 The engine/evidence bridge, which is where the work actually is

The deliverable you presumably want is

```
def decide (r : RE) (w : List Char) : Ev true r w ⊕ Ev false r w
```

agreeing with `matchRE`. Getting it from a derivative engine requires evidence
transport along derivatives, in both polarities:

```
Ev b (deriv c r) w  ≃  Ev b r (c :: w)
```

That pair of functions is the entire difficulty of this phase — it is where
`seq`'s split bookkeeping and `rep`'s chunk bookkeeping are actually done, and
everything else is plumbing. Two consequences for the design:

* Keep `Ev` **semantics-shaped** (indexed by the regex and word, mirroring
  `lang`), not derivative-shaped. A derivative-shaped evidence type makes
  transport trivial and the final artefact worthless.
* Stage it: define a cheap `Run r w` (the list of states the engine passed
  through, plus the terminal nullability decision), have the engine produce
  that, and write `Run → Ev` as a separate reconstruction function. This
  isolates the hard work in one place, lets you test the engine before the
  evidence theory is finished, and keeps the engine's performance
  characteristics unaffected by the evidence machinery.

### 3.4 Where the refutation disambiguation policy should live

**Not in the type.** This is the clearest recommendation in this section.

Baking a policy into the indices — a "POSIX-`Parse`" inductive whose `seq`
constructor carries "and no longer split exists" — means every constructor
acquires a negative, universally-quantified side condition. The derived
induction principle then becomes nearly useless (each case hands you a
hypothesis you cannot case on), and relating the biased family to the engine
becomes a second, harder version of §3.3. Formalisations of POSIX matching that
take this route are notoriously heavy.

The layered alternative is much lighter and is what I would do:

1. `Ev` is **unbiased**: it enumerates all witnesses and all refutations, with
   no canonical choice. Soundness and completeness are proved once, against
   `lang`, with no mention of any policy.
2. The policy is a **relation** on `Ev` at a fixed `(r, w)` — a preorder
   `e ≼ e'` ("`e'` is at least as POSIX as `e`") — together with a
   **normalisation function** `pick : Ev b r w → Ev b r w` and the two theorems
   `pick e` is `≼`-maximal and `pick` is idempotent. Blame extraction is then
   `blame := summarise ∘ pick`.
3. Only if you genuinely need two policies live at once should the policy become
   a parameter or a typeclass — and then it costs you a binder in every lemma
   statement, so postpone it.

On the *content* of the refutation policy: the natural dual of POSIX
longest-match on the success side is, for `r·s`, to blame the **latest** split —
take the largest `i` such that `∂_{w[0..i)} r` is nullable, and report the
refutation of `s` on the remainder; if no such `i` exists, report the refutation
of `r` on the longest prefix it could not extend. For `r*`, iterate: consume
greedily by longest match until no nonempty chunk matches, and blame the
position where consumption stalled. Both of these are exactly "the furthest
point the engine got", which is also the error message a user of a grep-like
tool wants ("failed at column 17"), and — usefully — both are computable
directly from the derivative run without materialising the full tabulated
refutation. That is another argument for keeping the policy in a separate
normalisation layer: the *policy* is cheap and streaming, while the *full
refutation type* is exhaustive and expensive, and you do not want the cheap
thing to depend on the expensive one.

---

## 4. Other things I would restructure now

**Module and namespace layout.** 28 top-level `lean_lib`s with names like
`Statements`, `Core`, `Engine`, `Closure`, `Bounds`, `SatMain`, `ChainPool` is a
flat namespace at the root, and several of those names are generic enough to
collide with future dependencies. Collapse to a single
`lean_lib Redgrep` with a `globs` entry and a directory structure
(`Redgrep/Core.lean`, `Redgrep/Cls/…`, `Redgrep/ACI/…`, `Redgrep/Bounds/…`,
`Redgrep/Evidence/…`). Faster to configure, easier to navigate, and it removes
the root-name hazard. Also split `Statements.lean`: it is a *specification* file
(language-level definitions and laws) that `Semantics.lean` imports for one
definition, so `Redgrep/Lang/Defs.lean` + `Redgrep/Lang/Laws.lean` cuts the
rebuild coupling.

**Dependency order.** The critical path, as I see it, is:
(1) `Fintype Char` / the fullness lemma, or the escape in §1.5 — everything
about `Cls` is blocked on it;
(2) the `Cls` membership API (§1.5);
(3) `RE.cmp` lawfulness and `LinearOrder RE` (§1.4);
(4) smart-constructor **language** laws (`lang (alt2 x y) = lang x ⊔ lang y`, …)
    and hence `lang (canon r) = lang r`;
(5) smart-constructor **derivative** laws (`deriv c (altL L) = altL (map …)`, …);
(6) the spanning-set bounds (§2.3), which need (5) but **not** ACI-completeness;
(7) tightness via distinguishability (§2.6), which needs almost nothing;
(8) evidence.
Note that (7) is nearly independent of everything else and would give you a real
headline result early — I would pull it forward. Note also that the inductive
`Canonical` and its preservation lemma, currently the gate for `Bounds.lean`,
move *off* the critical path under the §2.3 reformulation; they are then needed
only for sharp constants and for the `CRE` subtype interface.

**Seal the normalisers.** Once (4) and (5) exist, mark `altL`, `cutL`, `canon`,
`sortDedup` `irreducible`. Otherwise `simp` and `decide` will unfold them into
terms containing `mergeSort` and `partition`, which is how proofs in this style
turn into twenty-minute elaborations.

**Beware `decide` over `Char`.** `DecidableEq (Finset Char)` goes through
`Multiset`/`Quotient`, and `Char`'s own `Fintype` (once built) has four billion
elements upstream. Keep `decide`-measurements to regexes over two- or
three-element `pos` classes, and never `decide` anything that mentions
`Finset.univ : Finset Char`. Where the Haskell twin's behaviour is the thing
being checked, prefer `#guard` conformance tests over a golden table of
`(regex, word, expected)` triples: they are checked at build time, cost no proof
effort, and catch exactly the divergences that are otherwise found months later.

**The `Machine` constructor.** Three concrete recommendations before it lands:

* **Do not put a Mathlib `DFA Char σ` in the AST.** Its transition is a
  function, so the node loses `DecidableEq`, and the closure programme needs it.
  Use a concrete first-order table (`structure DFAt where n : Nat; step : …;
  accept : Array Bool`) plus a well-formedness predicate, and relate it to
  Mathlib's `DFA` by a separate `toDFA` and an `accepts` theorem — the same
  syntax/semantics split you already use for `RE`/`lang`.
* **The alphabet is 1.1 million letters, so the transition table cannot be
  dense in `Char`.** Key it by *classes*: `step : Array (List (Cls × Nat))` with
  a default target, i.e. a class-partitioned transition list per state, with a
  well-formedness condition that the classes in each row partition `Σ`. This
  reuses the `Cls` API you already need, and it makes `deriv c (machine M q) =
  machine M (M.step q c)` a lookup over a short list.
* **Carry the current state in the node** (`machine (M : DFAt) (q : Nat)`), so
  that the derivative is a pure table transition with no recursion and the state
  bound is immediate: `B (machine M q) ≤ M.n` (or `M.n + 1` if you collapse dead
  states to `nil`). With that in place, `invHom h (machine M q) = machine (M ∘ h)
  q'` gives you the `invHom` escape of §1.7(1) as a bonus, and the `div7`
  measurement becomes a statement about a nine-state table rather than about
  derivative syntax.

**One documentation point.** The module docstrings in `Core.lean` and
`Bounds.lean` are unusually good — they record the design rationale and the
provenance of each recurrence, which is exactly what a reviewer needs. Two of
the claims in them are, however, currently *stated as settled* while being
unproved and load-bearing: "the sort order … its lawfulness is later proof work,
not assumed by the engine" (the engine does not assume it, but every ACI proof
does), and the `charCount`/`Fintype Char` agreement ("a later proof obligation,
not assumed anywhere" — it is assumed by any semantic lemma about `Cls.isFull`).
I would mark both explicitly as *open holes on the critical path* rather than as
future refinements, since that is what they are.

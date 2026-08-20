import Mathlib.Data.Char
import Mathlib.Data.Finset.Sort

/-!
# Redgrep core, v3 — ACI-canonical twin

Executable mirror of the Haskell core (`src/Redgrep/Core.hs`) with the two
features the v2 twin deliberately simplified away:

* **Comparable classes.**  `sym` carries a `Cls` — a finite set of characters
  or the complement of one — instead of an opaque predicate `Char → Bool`, so
  classes (and hence regexes) have decidable equality and a total order.
* **ACI canonicalisation.**  Smart constructors (`altL`, `cutL`, `seq2`,
  `rep_`, `not_`, `sym`, `invHom_`) flatten, sort, deduplicate and apply
  unit/absorbing laws, mirroring the Haskell smart constructors.  The engine
  (`deriv`, `derivW`) is routed through them, which is what makes the set of
  reachable derivatives finite (the quantitative programme in `Bounds.lean`).

## Representation choice (and its tradeoffs)

The Haskell `Alt`/`Cut` carry a canonical `Set RE`.  The direct Lean analogue
(`alt (rs : Finset RE)`) is a nested inductive through a quotient and needs
`DecidableEq`/order instances *while defining* `RE` — painful to the point of
blocking.  A sorted-`List` field (`alt (rs : List RE)`) is the same nested
inductive problem minus the quotient: `deriving DecidableEq` does not handle
it, and every recursion needs manual nested-recursion boilerplate.

We therefore keep the v2 **binary constructors** and put all canonicity into a
separate layer: smart constructors normalise on the way in (canonical terms
are right-nested, sorted, duplicate-free chains), `canon : RE → RE` normalises
an arbitrary term bottom-up, and `Canonical r` (`canon r = r`) is the
well-formedness predicate.  Tradeoffs: `DecidableEq`/recursion/induction stay
trivial and `lake build` works today; the cost is that canonicity is a
*property* rather than baked into the type, so ACI-quotient arguments (e.g.
closure cardinality in `Bounds.lean`) must carry `Canonical` hypotheses or
work with images of `canon`, and the sort order is an explicit `RE.cmp` rather
than an inherited instance.

Deliberate deviations from the task spec / v2, mirroring the Haskell side:

* `invHom` carries its homomorphism as a finite association list
  `List (Char × List Char)` (Haskell: `Map Char String`), **not** a function
  `Char → List Char` — a function field would destroy the derived
  `DecidableEq`, which the closure-cardinality programme needs.  Characters
  absent from the list map to themselves (`applyHom`); `invHom_` normalises
  the list (`homNorm`), mirroring Haskell `invHom`.  Since `applyHom` resolves
  a key by *first hit wins* while the Haskell original works with a `Map`
  whose keys are unique by construction, normalisation first deduplicates by
  key (keeping the first binding) and only then drops identity entries, sorts
  and dedups; that is exactly what makes it meaning-preserving
  (`homNorm_applyHom`).
* `Machine` (embedded DFA nodes) is still TODO in v3; the planned sharp bound
  for it is recorded in `Bounds.lean`.
-/

namespace Redgrep

/-- The number of `Char`s: Unicode scalar values, `0x110000 - 0x800`
surrogates.  Mathlib (as pinned) has no `Fintype Char`, so fullness of a
`Finset Char` is tested against this constant; the agreement with
`Fintype.card Char` is a (later) proof obligation, not assumed anywhere. -/
def charCount : Nat := 1112064

/-- Character classes: a finite set, or the complement of one (`neg ∅` is
`.`).  Kept normalised (`Cls.norm`) so classes compare structurally. -/
inductive Cls where
  | pos (s : Finset Char)
  | neg (s : Finset Char)
  deriving DecidableEq

/-- Class membership. -/
def inCls (c : Char) : Cls → Bool
  | .pos s => decide (c ∈ s)
  | .neg s => decide (c ∉ s)

namespace Cls

/-- Total emptiness test (the `neg` case is why `charCount` exists). -/
def isEmpty : Cls → Bool
  | .pos s => decide (s = ∅)
  | .neg s => decide (s.card = charCount)

/-- Totality test, dual to `isEmpty`. -/
def isFull : Cls → Bool
  | .pos s => decide (s.card = charCount)
  | .neg s => decide (s = ∅)

/-- Canonical representative: the full class is always `neg ∅` (dot). -/
def norm (c : Cls) : Cls := if c.isFull then .neg ∅ else c

def union : Cls → Cls → Cls
  | .pos a, .pos b => .pos (a ∪ b)
  | .neg a, .neg b => .neg (a ∩ b)
  | .pos a, .neg b => .neg (b \ a)
  | .neg a, .pos b => .neg (a \ b)

def inter : Cls → Cls → Cls
  | .pos a, .pos b => .pos (a ∩ b)
  | .neg a, .neg b => .neg (a ∪ b)
  | .pos a, .neg b => .pos (a \ b)
  | .neg a, .pos b => .pos (b \ a)

def compl : Cls → Cls
  | .pos s => .neg s
  | .neg s => .pos s

/-- A total comparator (via the sorted element lists), used only as the sort
key of the ACI canonical form.  Its order-theoretic laws are later work. -/
def cmp : Cls → Cls → Ordering
  | .pos a, .pos b => compare (a.sort (· ≤ ·)) (b.sort (· ≤ ·))
  | .pos _, .neg _ => .lt
  | .neg _, .pos _ => .gt
  | .neg a, .neg b => compare (a.sort (· ≤ ·)) (b.sort (· ≤ ·))

end Cls

/-- The core regex AST, v3: binary `alt`/`cut` with canonicity supplied by
the smart constructors below (see the module docstring). -/
inductive RE where
  /-- A character class. -/
  | sym (cls : Cls)
  /-- Union (Haskell `Alt`; canonical terms are right-nested sorted chains). -/
  | alt (r₁ r₂ : RE)
  /-- Intersection (Haskell `Cut`). -/
  | cut (r₁ r₂ : RE)
  /-- Concatenation (Haskell `Seq`; canonical terms are right-nested). -/
  | seq (r₁ r₂ : RE)
  /-- Kleene star (Haskell `Rep`). -/
  | rep (r : RE)
  /-- Complement (Haskell `Not`). -/
  | not (r : RE)
  /-- Inverse string homomorphism, the hom as a finite association list
  (identity outside its domain; see `applyHom`). -/
  | invHom (h : List (Char × List Char)) (r : RE)
  /-- The empty string. -/
  | eps
  /-- The empty language. -/
  | nil
  deriving DecidableEq

/-- The homomorphism denoted by an association list: first hit wins,
characters absent from the list map to themselves (Haskell `applyHom`). -/
def applyHom (h : List (Char × List Char)) (c : Char) : List Char :=
  match h.find? (fun p => p.1 == c) with
  | some p => p.2
  | none => [c]

namespace RE

/- The constructor tag `RE.ctorIdx` (auto-generated by Lean for every
inductive) is the major key of the total order `RE.cmp` below. -/

/-- Lexicographic comparator for hom entries. -/
def cmpHomEntry (a b : Char × List Char) : Ordering :=
  (compare a.1 b.1).then (compare a.2 b.2)

/-- Lexicographic comparator for hom association lists. -/
def cmpHom : List (Char × List Char) → List (Char × List Char) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (cmpHomEntry a b).then (cmpHom as bs)

/-- A total comparator on `RE`: constructor tag first, then fields
lexicographically.  This is the sort order of the ACI canonical form
(the analogue of the Haskell derived `Ord`); its lawfulness (linearity,
compatibility with `=`) is later proof work, not assumed by the engine. -/
def cmp : RE → RE → Ordering
  | .sym c₁, .sym c₂ => c₁.cmp c₂
  | .alt a₁ b₁, .alt a₂ b₂ => (cmp a₁ a₂).then (cmp b₁ b₂)
  | .cut a₁ b₁, .cut a₂ b₂ => (cmp a₁ a₂).then (cmp b₁ b₂)
  | .seq a₁ b₁, .seq a₂ b₂ => (cmp a₁ a₂).then (cmp b₁ b₂)
  | .rep r₁, .rep r₂ => cmp r₁ r₂
  | .not r₁, .not r₂ => cmp r₁ r₂
  | .invHom h₁ r₁, .invHom h₂ r₂ => (cmpHom h₁ h₂).then (cmp r₁ r₂)
  | r₁, r₂ => compare r₁.ctorIdx r₂.ctorIdx

/-- Boolean `≤` for `List.mergeSort`. -/
def le (a b : RE) : Bool := (cmp a b).isLE

end RE

/-! ### Smart constructors — the only way to build canonical terms -/

/-- `¬∅`: the universal language `Σ*`, the unit of `cutL`. -/
def top : RE := .not .nil

/-- Smart `sym`: an empty class is `nil`, a full class is normalised. -/
def sym (cls : Cls) : RE := if cls.isEmpty then .nil else .sym cls.norm

def chr (c : Char) : RE := sym (.pos {c})

def dot : RE := .sym (.neg ∅)

def isSym : RE → Bool
  | .sym _ => true
  | _ => false

/-- Flatten a (right-nested) union into its member list, dropping `nil`. -/
def altToList : RE → List RE
  | .alt a b => altToList a ++ altToList b
  | .nil => []
  | r => [r]

/-- Flatten an intersection into its member list, dropping `top`. -/
def cutToList : RE → List RE
  | .cut a b => cutToList a ++ cutToList b
  | r => if r = top then [] else [r]

/-- Flatten a concatenation into its factor list, dropping `eps`. -/
def seqToList : RE → List RE
  | .seq a b => seqToList a ++ seqToList b
  | .eps => []
  | r => [r]

/-- Rebuild a right-nested union; the empty union is `nil`. -/
def altOfList : List RE → RE
  | [] => .nil
  | [r] => r
  | r :: rs => .alt r (altOfList rs)

/-- Rebuild a right-nested intersection; the empty intersection is `top`. -/
def cutOfList : List RE → RE
  | [] => top
  | [r] => r
  | r :: rs => .cut r (cutOfList rs)

/-- Rebuild a right-nested concatenation; the empty product is `eps`. -/
def seqOfList : List RE → RE
  | [] => .eps
  | [r] => r
  | r :: rs => .seq r (seqOfList rs)

/-- Sort by the total order and remove duplicates: the ACI normal form of a
member list. -/
def sortDedup (rs : List RE) : List RE := (rs.mergeSort RE.le).dedup

/-- Extract the classes of the `sym` members. -/
def symClasses (rs : List RE) : List Cls :=
  rs.filterMap fun r => match r with | .sym cls => some cls | _ => none

/-- n-ary union, flattened, sorted, deduplicated; `nil` dropped, `top`
absorbing, `sym` members merged into one class (Haskell `altL`). -/
def altL (rs : List RE) : RE :=
  let flat := rs.flatMap altToList
  if top ∈ flat then top
  else
    let (syms, rest) := flat.partition isSym
    let merged : List RE :=
      match symClasses syms with
      | [] => []
      | c :: cs =>
        match sym (cs.foldl Cls.union c) with
        | .nil => []
        | s => [s]
    altOfList (sortDedup (merged ++ rest))

def alt2 (x y : RE) : RE := altL [x, y]

/-- n-ary intersection, dual to `altL`: `top` dropped, `nil` absorbing,
`sym` members merged by intersection; the empty intersection is `top`
(Haskell `cutL`). -/
def cutL (rs : List RE) : RE :=
  let flat := rs.flatMap cutToList
  if .nil ∈ flat then .nil
  else
    let (syms, rest) := flat.partition isSym
    match symClasses syms with
    | [] => cutOfList (sortDedup rest)
    | c :: cs =>
      match sym (cs.foldl Cls.inter c) with
      | .nil => .nil
      | s => cutOfList (sortDedup (s :: rest))

def cut2 (x y : RE) : RE := cutL [x, y]

/-- Smart concatenation: `nil` absorbing, `eps` unit, right-nested
(Haskell `seq2`). -/
def seq2 : RE → RE → RE
  | .nil, _ => .nil
  | _, .nil => .nil
  | .eps, y => y
  | x, .eps => x
  | x, y => seqOfList (seqToList x ++ seqToList y)

def seqL (rs : List RE) : RE := rs.foldr seq2 .eps

def str (s : String) : RE := seqL (s.toList.map chr)

/-- Smart star (Haskell `rep_`): `(∅)* = ()* = ε`, `(r*)* = r*`,
`(Σ*)* = Σ*`. -/
def rep_ : RE → RE
  | .nil => .eps
  | .eps => .eps
  | .rep r => .rep r
  | r => if r = top then top else .rep r

/-- Smart complement (Haskell `not_`): involutive. -/
def not_ : RE → RE
  | .not r => r
  | r => .not r

/-- `r?` -/
def opt (r : RE) : RE := alt2 .eps r

/-- Deduplicate an association list **by key**, keeping the FIRST binding for
each key — exactly the one `applyHom` resolves to.  This restores, on the
association-list representation, the "keys are unique" invariant that the
Haskell original gets for free from `Map Char String`; without it, dropping an
identity entry could expose a shadowed later binding and change the denoted
homomorphism. -/
def homDedupKeys : List (Char × List Char) → List (Char × List Char)
  | [] => []
  | p :: ps => p :: homDedupKeys (ps.filter fun q => q.1 != p.1)
termination_by l => l.length
decreasing_by
  simp only [List.length_cons, List.length_unattach]
  exact Nat.lt_succ_of_le ((List.length_filter_le _ _).trans (by simp))

/-- The canonical form of a hom association list: first deduplicate by key
(so that later, shadowed bindings can never resurface), then drop identity
entries, then sort and remove duplicate pairs.  Normalisation preserves the
denoted homomorphism pointwise (`homNorm_applyHom` in `REOrder.lean`). -/
def homNorm (h : List (Char × List Char)) : List (Char × List Char) :=
  (((homDedupKeys h).filter fun p => p.2 != [p.1]).mergeSort
    fun a b => (RE.cmpHomEntry a b).isLE).dedup

/-- Smart inverse homomorphism (Haskell `invHom`): `nil` collapses, the
association list is replaced by its canonical form `homNorm` (deduplicated by
key, identity entries dropped, sorted and duplicate-free); an emptied map
collapses to the bare regex. -/
def invHom_ (h : List (Char × List Char)) : RE → RE
  | .nil => .nil
  | r => if homNorm h = [] then r else .invHom (homNorm h) r

theorem homDedupKeys_sublist :
    ∀ l : List (Char × List Char), List.Sublist (homDedupKeys l) l
  | [] => by rw [homDedupKeys]
  | p :: ps => by
    rw [homDedupKeys]
    exact List.Sublist.cons₂ p
      ((homDedupKeys_sublist (ps.filter fun q => q.1 != p.1)).trans List.filter_sublist)
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem homNorm_subperm (h : List (Char × List Char)) : (homNorm h).Subperm h :=
  (((List.dedup_sublist _).subperm.trans (List.mergeSort_perm _ _).subperm).trans
    List.filter_sublist.subperm).trans (homDedupKeys_sublist h).subperm

/-! ### The engine -/

/-- Does the language contain the empty string?  Mirrors the Haskell
`nullable` equations constructor by constructor. -/
def nullable : RE → Bool
  | .sym _ => false
  | .alt r₁ r₂ => nullable r₁ || nullable r₂
  | .cut r₁ r₂ => nullable r₁ && nullable r₂
  | .seq r₁ r₂ => nullable r₁ && nullable r₂
  | .rep _ => true
  | .not r => !nullable r
  | .invHom _ r => nullable r
  | .eps => true
  | .nil => false

/-- Derivative by a whole *word* (left quotient), routed through the smart
constructors.  Same recursion (and termination argument) as the v2 twin: the
word shrinks in the `rep` case, the regex shrinks everywhere else, and the
`invHom` case derives the body by the image word — which is what keeps `deriv`
below total and structural. -/
def derivW : List Char → RE → RE
  | u, .sym cls =>
      match u with
      | [] => sym cls
      | [c] => if inCls c cls then .eps else .nil
      | _ => .nil
  | u, .alt r₁ r₂ => alt2 (derivW u r₁) (derivW u r₂)
  | u, .cut r₁ r₂ => cut2 (derivW u r₁) (derivW u r₂)
  | u, .seq r₁ r₂ =>
      -- Either the whole word is consumed inside the first factor, or the
      -- first factor matches some prefix `u.take i` and the remaining suffix
      -- `u.drop i` is consumed inside the second factor.
      alt2 (seq2 (derivW u r₁) r₂)
        (altL ((List.range (u.length + 1)).map fun i =>
          if nullable (derivW (u.take i) r₁) then derivW (u.drop i) r₂ else .nil))
  | u, .rep r =>
      -- Some proper prefix `u.take i` is matched by a whole number of
      -- iterations, and the chunk straddling the split point begins with
      -- the remaining suffix `u.drop i`.
      altL ((if u.isEmpty then [rep_ r] else []) ++
        (List.range u.length).attach.map fun x =>
          if nullable (derivW (u.take x.1) (.rep r)) then
            seq2 (derivW (u.drop x.1) r) (rep_ r)
          else .nil)
  | u, .not r => not_ (derivW u r)
  | u, .invHom h r => invHom_ h (derivW (u.flatMap (applyHom h)) r)
  | u, .eps => match u with | [] => .eps | _ => .nil
  | _, .nil => .nil
termination_by u r => (sizeOf r, u.length)
decreasing_by
  all_goals
    first
      | (apply Prod.Lex.left
         simp +arith
         done)
      | (apply Prod.Lex.right
         have hx := List.mem_range.mp x.2
         simp only [List.length_take]
         omega)

/-- Brzozowski derivative by one character, routed through the smart
constructors (mirrors the Haskell `deriv` equations). -/
def deriv (c : Char) : RE → RE
  | .sym cls => if inCls c cls then .eps else .nil
  | .alt r₁ r₂ => alt2 (deriv c r₁) (deriv c r₂)
  | .cut r₁ r₂ => cut2 (deriv c r₁) (deriv c r₂)
  | .seq r₁ r₂ =>
      if nullable r₁ then alt2 (seq2 (deriv c r₁) r₂) (deriv c r₂)
      else seq2 (deriv c r₁) r₂
  | .rep r => seq2 (deriv c r) (rep_ r)
  | .not r => not_ (deriv c r)
  | .invHom h r => invHom_ h (derivW (applyHom h c) r)
  | .eps => .nil
  | .nil => .nil

/-! `deriv` is plain structural recursion, so each equation holds by `rfl`;
recorded as simp lemmas (the v3 analogue of the v2 block). -/

@[simp] theorem deriv_sym (c : Char) (cls : Cls) :
    deriv c (.sym cls) = if inCls c cls then .eps else .nil := rfl

@[simp] theorem deriv_alt (c : Char) (r₁ r₂ : RE) :
    deriv c (.alt r₁ r₂) = alt2 (deriv c r₁) (deriv c r₂) := rfl

@[simp] theorem deriv_cut (c : Char) (r₁ r₂ : RE) :
    deriv c (.cut r₁ r₂) = cut2 (deriv c r₁) (deriv c r₂) := rfl

@[simp] theorem deriv_seq (c : Char) (r₁ r₂ : RE) :
    deriv c (.seq r₁ r₂) =
      (if nullable r₁ then alt2 (seq2 (deriv c r₁) r₂) (deriv c r₂)
       else seq2 (deriv c r₁) r₂) := rfl

@[simp] theorem deriv_rep (c : Char) (r : RE) :
    deriv c (.rep r) = seq2 (deriv c r) (rep_ r) := rfl

@[simp] theorem deriv_not (c : Char) (r : RE) :
    deriv c (.not r) = not_ (deriv c r) := rfl

@[simp] theorem deriv_invHom (c : Char) (h : List (Char × List Char)) (r : RE) :
    deriv c (.invHom h r) = invHom_ h (derivW (applyHom h c) r) := rfl

@[simp] theorem deriv_eps (c : Char) : deriv c .eps = .nil := rfl

@[simp] theorem deriv_nil (c : Char) : deriv c .nil = .nil := rfl

/-- Match by iterated derivative (Haskell `match`). -/
def matchRE : RE → List Char → Bool := fun r s =>
  nullable (s.foldl (fun r c => deriv c r) r)

/-! ### Canonicalisation as a function and a predicate -/

/-- Bottom-up normalisation: rebuild every node through its smart
constructor.  On terms built exclusively by smart constructors this is the
identity (`canon_canonical` in `Correctness.lean`). -/
def canon : RE → RE
  | .sym cls => sym cls
  | .alt a b => alt2 (canon a) (canon b)
  | .cut a b => cut2 (canon a) (canon b)
  | .seq a b => seq2 (canon a) (canon b)
  | .rep r => rep_ (canon r)
  | .not r => not_ (canon r)
  | .invHom h r => invHom_ h (canon r)
  | .eps => .eps
  | .nil => .nil

/-- The well-formedness predicate of the v3 representation: a term is
canonical iff normalisation fixes it.  Decidable, since `RE` has decidable
equality. -/
def Canonical (r : RE) : Prop := canon r = r

instance (r : RE) : Decidable (Canonical r) := by unfold Canonical; infer_instance

end Redgrep

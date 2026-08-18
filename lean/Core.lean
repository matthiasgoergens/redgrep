/-!
# Redgrep core — executable twin

Executable mirror of the Haskell core (`src/Redgrep/Core.hs`): the regex AST
and the Brzozowski-derivative engine, as plain structural recursion.

Deliberate differences from the Haskell side (v1):

* `alt`/`cut` are **binary** here. The Haskell `Alt`/`Cut` carry a canonical
  `Set RE` — but canonicity (ACI normal form, smart constructors) is a
  Haskell-side performance concern, not a semantic one; the twin states and
  proves laws about the plain operations.
* `sym` carries its class as a predicate `Char → Bool` for executability,
  rather than the normalised `Pos`/`Neg` set representation.
* `Machine` (embedded DFA nodes) is still omitted; `InvHom` (inverse string
  homomorphism) is part of v2, see `derivW` below.
-/

namespace Redgrep

/-- The core regex AST: symbols, union, intersection, concatenation,
Kleene star, complement, the empty string, and the empty language. -/
inductive RE where
  /-- A character class, as a decidable predicate. -/
  | sym (cls : Char → Bool)
  /-- Union (Haskell `Alt`, binary in the twin). -/
  | alt (r₁ r₂ : RE)
  /-- Intersection (Haskell `Cut`, binary in the twin). -/
  | cut (r₁ r₂ : RE)
  /-- Concatenation (Haskell `Seq`, binary in the twin). -/
  | seq (r₁ r₂ : RE)
  /-- Kleene star (Haskell `Rep`). -/
  | rep (r : RE)
  /-- Complement (Haskell `Not`). -/
  | not (r : RE)
  /-- Inverse string homomorphism: matches w iff r matches h(w)
  (see invHom in Statements.lean).  v2 addition. -/
  | invHom (h : Char → List Char) (r : RE)
  /-- The empty string. -/
  | eps
  /-- The empty language. -/
  | nil

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

/-- `altFold rs` is the (right-nested) union of the regexes in `rs`. -/
def altFold : List RE → RE
  | [] => .nil
  | r :: rs => .alt r (altFold rs)

/-- Derivative by a whole *word* (left quotient), defined by recursion on the
regex, the word shrinking in the `rep` case.  `derivW` never calls `deriv`;
it is what makes the `invHom` case of `deriv` below total and computable:
deriving `invHom h r` by a character `c` means deriving `r` by the image
word `h c`.

The language law is `lang (derivW u r) = derivW u (lang r)`, proved as
`lang_derivW` in `Correctness.lean`. -/
def derivW : List Char → RE → RE
  | u, .sym cls =>
      match u with
      | [] => .sym cls
      | [c] => if cls c then .eps else .nil
      | _ => .nil
  | u, .alt r₁ r₂ => .alt (derivW u r₁) (derivW u r₂)
  | u, .cut r₁ r₂ => .cut (derivW u r₁) (derivW u r₂)
  | u, .seq r₁ r₂ =>
      -- Either the whole word is consumed inside the first factor, or the
      -- first factor matches some prefix `u.take i` and the remaining suffix
      -- `u.drop i` is consumed inside the second factor.
      .alt (.seq (derivW u r₁) r₂)
        (altFold ((List.range (u.length + 1)).map fun i =>
          if nullable (derivW (u.take i) r₁) then derivW (u.drop i) r₂ else .nil))
  | u, .rep r =>
      -- Some proper prefix `u.take i` is matched by a whole number of
      -- iterations, and the chunk straddling the split point begins with
      -- the remaining suffix `u.drop i`.  (For `u = []` the list of splits is
      -- empty and the answer is `rep r` itself.)
      altFold ((if u.isEmpty then [RE.rep r] else []) ++
        (List.range u.length).attach.map fun x =>
          if nullable (derivW (u.take x.1) (.rep r)) then
            .seq (derivW (u.drop x.1) r) (.rep r)
          else .nil)
  | u, .not r => .not (derivW u r)
  | u, .invHom h r => .invHom h (derivW (u.flatMap h) r)
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

/-- Brzozowski derivative by one character.  Mirrors the Haskell `deriv`
equations: it commutes with every constructor, including complement. -/
def deriv (c : Char) : RE → RE
  | .sym cls => if cls c then .eps else .nil
  | .alt r₁ r₂ => .alt (deriv c r₁) (deriv c r₂)
  | .cut r₁ r₂ => .cut (deriv c r₁) (deriv c r₂)
  | .seq r₁ r₂ =>
      if nullable r₁ then .alt (.seq (deriv c r₁) r₂) (deriv c r₂)
      else .seq (deriv c r₁) r₂
  | .rep r => .seq (deriv c r) (.rep r)
  | .not r => .not (deriv c r)
  -- Derive by the image string: the language law is `deriv1_invHom` in
  -- `Statements.lean`.  The word derivative `derivW` above does the work,
  -- so this case is not recursive in `deriv` and `deriv` stays structural.
  | .invHom h r => .invHom h (derivW (h c) r)
  | .eps => .nil
  | .nil => .nil

/-! `deriv` is still plain structural recursion, so each of its equations holds
by `rfl`; they are recorded here as simp lemmas. -/

@[simp] theorem deriv_sym (c : Char) (cls : Char → Bool) :
    deriv c (.sym cls) = if cls c then .eps else .nil := rfl

@[simp] theorem deriv_alt (c : Char) (r₁ r₂ : RE) :
    deriv c (.alt r₁ r₂) = .alt (deriv c r₁) (deriv c r₂) := rfl

@[simp] theorem deriv_cut (c : Char) (r₁ r₂ : RE) :
    deriv c (.cut r₁ r₂) = .cut (deriv c r₁) (deriv c r₂) := rfl

@[simp] theorem deriv_seq (c : Char) (r₁ r₂ : RE) :
    deriv c (.seq r₁ r₂) =
      (if nullable r₁ then .alt (.seq (deriv c r₁) r₂) (deriv c r₂)
       else .seq (deriv c r₁) r₂) := rfl

@[simp] theorem deriv_rep (c : Char) (r : RE) :
    deriv c (.rep r) = .seq (deriv c r) (.rep r) := rfl

@[simp] theorem deriv_not (c : Char) (r : RE) :
    deriv c (.not r) = .not (deriv c r) := rfl

@[simp] theorem deriv_invHom (c : Char) (h : Char → List Char) (r : RE) :
    deriv c (.invHom h r) = .invHom h (derivW (h c) r) := rfl

@[simp] theorem deriv_eps (c : Char) : deriv c .eps = .nil := rfl

@[simp] theorem deriv_nil (c : Char) : deriv c .nil = .nil := rfl

/-- Match by iterated derivative: derive by each character in turn, then ask
whether the residual is nullable (Haskell `match`). -/
def matchRE : RE → List Char → Bool := fun r s =>
  nullable (s.foldl (fun r c => deriv c r) r)

end Redgrep

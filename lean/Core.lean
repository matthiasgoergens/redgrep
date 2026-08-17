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
* TODO (v2): `InvHom` (inverse string homomorphism; needs the
  derive-by-image-string rule, see `deriv1_invHom` in `Statements.lean`) and
  `Machine` (embedded DFA nodes) are omitted.
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
  | .eps => true
  | .nil => false

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
  | .eps => .nil
  | .nil => .nil

/-- Match by iterated derivative: derive by each character in turn, then ask
whether the residual is nullable (Haskell `match`). -/
def matchRE : RE → List Char → Bool := fun r s =>
  nullable (s.foldl (fun r c => deriv c r) r)

end Redgrep

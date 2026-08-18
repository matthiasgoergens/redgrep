import Mathlib.Computability.Language
import Core
-- `_root_.invHom` (used in `lang` below) is defined in `Statements.lean`;
-- this import is the only change made to this file.
import Statements

/-!
# Redgrep semantics

The denotation of the core AST as a Mathlib `Language Char`
(`Set (List Char)` with `*` = concatenation, `∗` = Kleene star,
`⊔`/`⊓`/`ᶜ` the set-lattice operations, `1` = `{[]}`, `0` = `⊥`).
This is the specification the executable engine in `Core.lean` is
measured against (see `Correctness.lean`).
-/

open Language Computability

namespace Redgrep

/-- The language denoted by a regex, by structural recursion. -/
def lang : RE → Language Char
  | .sym cls => {w | ∃ c, cls c = true ∧ w = [c]}
  | .alt r₁ r₂ => lang r₁ ⊔ lang r₂
  | .cut r₁ r₂ => lang r₁ ⊓ lang r₂
  | .seq r₁ r₂ => lang r₁ * lang r₂
  | .rep r => (lang r)∗
  | .not r => (lang r)ᶜ
  | .invHom h r => _root_.invHom h (lang r)
  | .eps => 1
  | .nil => 0

end Redgrep

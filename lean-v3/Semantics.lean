import Mathlib.Computability.Language
import Core
-- `_root_.invHom` (used in `lang` below) is defined in `Statements.lean`.
import Statements

/-!
# Redgrep semantics, v3

The denotation of the v3 core AST as a Mathlib `Language Char`
(`Set (List Char)` with `*` = concatenation, `∗` = Kleene star,
`⊔`/`⊓`/`ᶜ` the set-lattice operations, `1` = `{[]}`, `0` = `⊥`).
Identical in shape to the v2 `Semantics.lean`; the only changes are the
`sym` case (a `Cls` interpreted through `inCls` instead of a raw
predicate) and the `invHom` case (the association list interpreted
through `applyHom`).  This is the specification the executable engine in
`Core.lean` — and every smart constructor — is measured against
(see `Correctness.lean`).
-/

open Language Computability

namespace Redgrep

/-- The language denoted by a regex, by structural recursion. -/
def lang : RE → Language Char
  | .sym cls => {w | ∃ c, inCls c cls = true ∧ w = [c]}
  | .alt r₁ r₂ => lang r₁ ⊔ lang r₂
  | .cut r₁ r₂ => lang r₁ ⊓ lang r₂
  | .seq r₁ r₂ => lang r₁ * lang r₂
  | .rep r => (lang r)∗
  | .not r => (lang r)ᶜ
  | .invHom h r => _root_.invHom (applyHom h) (lang r)
  | .eps => 1
  | .nil => 0

end Redgrep

import ACIAlt
import ACICut
import ACISeq

/-!
# The ACI layer: `canon` is idempotent

Assembly of the per-constructor files: structurally canonical terms
(`IsCanon`, `ACIDefs.lean`) are exactly the fixed points of `canon`.

* `isCanon_canon_eq` : `IsCanon r → canon r = r`;
* `canon_isCanon`    : `IsCanon (canon r)` (each smart constructor lands in
  `IsCanon`);
* `canon_idem`, `canonical_iff_isCanon`.

`Correctness.canon_canonical` is `canon_idem` read through the definition of
`Canonical`.
-/

namespace Redgrep

/-- Structurally canonical terms are fixed points of `canon`. -/
theorem isCanon_canon_eq {r : RE} (h : IsCanon r) : canon r = r := by
  induction r with
  | sym cl => exact h
  | alt a b iha ihb =>
    obtain ⟨ha, hb, -, -, -, -⟩ := isCanon_alt_iff.mp h
    show alt2 (canon a) (canon b) = _
    rw [iha ha, ihb hb]
    exact alt2_eq_self h
  | cut a b iha ihb =>
    obtain ⟨ha, hb, -, -, -, -⟩ := isCanon_cut_iff.mp h
    show cut2 (canon a) (canon b) = _
    rw [iha ha, ihb hb]
    exact cut2_eq_self h
  | seq a b iha ihb =>
    obtain ⟨ha, hb, -, -, -, -, -⟩ := isCanon_seq_iff.mp h
    show seq2 (canon a) (canon b) = _
    rw [iha ha, ihb hb]
    exact seq2_eq_self h
  | rep a ih =>
    obtain ⟨ha, -, -, -, -⟩ := isCanon_rep_iff.mp h
    show rep_ (canon a) = _
    rw [ih ha]
    exact rep_eq_self h
  | not a ih =>
    obtain ⟨ha, -⟩ := isCanon_not_iff.mp h
    show not_ (canon a) = _
    rw [ih ha]
    exact not_eq_self h
  | invHom hh a ih =>
    obtain ⟨ha, -, -, -⟩ := isCanon_invHom_iff.mp h
    show invHom_ hh (canon a) = _
    rw [ih ha]
    exact invHom_eq_self h
  | eps => rfl
  | nil => rfl

/-- Every rebuilt term is structurally canonical. -/
theorem canon_isCanon (r : RE) : IsCanon (canon r) := by
  induction r with
  | sym cl => exact isCanon_sym cl
  | alt a b iha ihb => exact isCanon_alt2 iha ihb
  | cut a b iha ihb => exact isCanon_cut2 iha ihb
  | seq a b iha ihb => exact isCanon_seq2 iha ihb
  | rep a ih => exact isCanon_rep_ ih
  | not a ih => exact isCanon_not_ ih
  | invHom h a ih => exact isCanon_invHom_ h ih
  | eps => exact isCanon_eps
  | nil => exact isCanon_nil

theorem canon_idem (r : RE) : canon (canon r) = canon r :=
  isCanon_canon_eq (canon_isCanon r)

/-- The two notions of canonicity agree. -/
theorem canonical_iff_isCanon (r : RE) : Canonical r ↔ IsCanon r := by
  constructor
  · intro h
    have := canon_isCanon r
    rwa [h] at this
  · exact fun h => isCanon_canon_eq h

end Redgrep

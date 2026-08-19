import SatSeq
import SatCases

/-!
# Assembling a saturated pool for an arbitrary regex

Every constructor of `RE` has its own pool construction (`SatCases.lean` for
the atoms and the boolean/homomorphic connectives, `SatSeq.lean` for
concatenation and star).  All of them are stated relative to a fixed bound `U`
on the character classes involved, so to run the structural induction we need
one `U` that bounds *all* the classes of the term: `reUniv r`.
-/

namespace Redgrep

/-- All characters mentioned by the classes occurring in a regex. -/
def reUniv : RE → Finset Char
  | .sym cl => cl.carrier
  | .alt a b => reUniv a ∪ reUniv b
  | .cut a b => reUniv a ∪ reUniv b
  | .seq a b => reUniv a ∪ reUniv b
  | .rep a => reUniv a
  | .not a => reUniv a
  | .invHom _ a => reUniv a
  | .eps => ∅
  | .nil => ∅

/-- Every class occurring in the regex is bounded by `U`. -/
def REOK (U : Finset Char) : RE → Prop
  | .sym cl => ClsOK U cl
  | .alt a b => REOK U a ∧ REOK U b
  | .cut a b => REOK U a ∧ REOK U b
  | .seq a b => REOK U a ∧ REOK U b
  | .rep a => REOK U a
  | .not a => REOK U a
  | .invHom _ a => REOK U a
  | .eps => True
  | .nil => True

theorem reOK_mono {U V : Finset Char} (h : U ⊆ V) : ∀ {r : RE}, REOK U r → REOK V r := by
  intro r
  induction r with
  | sym cl => exact fun hr => clsOK_mono h hr
  | alt a b iha ihb => exact fun hr => ⟨iha hr.1, ihb hr.2⟩
  | cut a b iha ihb => exact fun hr => ⟨iha hr.1, ihb hr.2⟩
  | seq a b iha ihb => exact fun hr => ⟨iha hr.1, ihb hr.2⟩
  | rep a iha => exact iha
  | not a iha => exact iha
  | invHom _ a iha => exact iha
  | eps => exact fun _ => trivial
  | nil => exact fun _ => trivial

theorem reOK_reUniv (r : RE) : REOK (reUniv r) r := by
  induction r with
  | sym cl => exact clsOK_self cl
  | alt a b iha ihb =>
    exact ⟨reOK_mono Finset.subset_union_left iha, reOK_mono Finset.subset_union_right ihb⟩
  | cut a b iha ihb =>
    exact ⟨reOK_mono Finset.subset_union_left iha, reOK_mono Finset.subset_union_right ihb⟩
  | seq a b iha ihb =>
    exact ⟨reOK_mono Finset.subset_union_left iha, reOK_mono Finset.subset_union_right ihb⟩
  | rep a iha => exact iha
  | not a iha => exact iha
  | invHom _ a iha => exact iha
  | eps => trivial
  | nil => trivial

/-- Structural induction: a regex whose classes are bounded by `U` lies in a
saturated set of states over `U`. -/
theorem exists_sat_of {U : Finset Char} : ∀ {r : RE}, REOK U r → ∃ P, Sat U P ∧ r ∈ P := by
  intro r
  induction r with
  | sym cl => exact fun hr => exists_sat_sym hr
  | alt a b iha ihb =>
    intro hr
    obtain ⟨Pa, hPa, ha⟩ := iha hr.1
    obtain ⟨Pb, hPb, hb⟩ := ihb hr.2
    exact exists_sat_alt hPa hPb ha hb
  | cut a b iha ihb =>
    intro hr
    obtain ⟨Pa, hPa, ha⟩ := iha hr.1
    obtain ⟨Pb, hPb, hb⟩ := ihb hr.2
    exact exists_sat_cut hPa hPb ha hb
  | seq a b iha ihb =>
    intro hr
    obtain ⟨Pa, hPa, ha⟩ := iha hr.1
    obtain ⟨Pb, hPb, hb⟩ := ihb hr.2
    exact exists_sat_seq hPa hPb ha hb
  | rep a iha =>
    intro hr
    obtain ⟨Pa, hPa, ha⟩ := iha hr
    exact exists_sat_rep hPa ha
  | not a iha =>
    intro hr
    obtain ⟨Pa, hPa, ha⟩ := iha hr
    exact exists_sat_not hPa ha
  | invHom hm a iha =>
    intro hr
    obtain ⟨Pa, hPa, ha⟩ := iha hr
    exact exists_sat_invHom hPa ha
  | eps => exact fun _ => exists_sat_eps U
  | nil => exact fun _ => exists_sat_nilRE U

/-- **Every regex sits inside a saturated (hence finite) set of states.** -/
theorem exists_sat_set (r : RE) : ∃ P : Set RE, Sat (reUniv r) P ∧ r ∈ P :=
  exists_sat_of (reOK_reUniv r)

end Redgrep

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.ResidueCard
import InverseGalois.CFT.Local.AdicResidue

/-!
# The number of residues of a completion of a number field

The Frobenius automorphism of a completion raises a root of unity to the power given by the number
of residues, so a description of the Frobenius as a cyclotomic operation needs that number for an
arbitrary place, not only for a place whose residue field is the prime field.

The residue ring of the completion is the residue field of the place itself.  Reducing an integer
of the number field gives a ring homomorphism to the residue ring of the completion, and it is
surjective because the number field is dense in its completion: every element of the valuation ring
of the completion differs from an integer of the number field by something of valuation less than
one.  Its kernel is the place, because the valuation of an integer in the completion is its
valuation in the number field.  So the residue ring of the completion is the quotient of the ring of
integers by the place, whose cardinality is the absolute norm of the place: the residue
characteristic raised to the residue degree.

## Main results

* `InverseGalois.CFT.adicResidueHom`: the reduction of an integer of a number field in the residue
  ring of a completion.
* `InverseGalois.CFT.natCard_divisionResidue_adicCompletion_eq_natCard_quotient`: **the residue ring
  of a completion has as many elements as the residue field of the place.**
* `InverseGalois.CFT.natCard_divisionResidue_adicCompletion_eq_pow_inertiaDeg`: **the completion of
  a number field at a place over `p` has `p` raised to the residue degree many residues.**

## Tags

local field, residue field, residue degree, adic completion, absolute norm, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section ResidueCardDegree

variable {K : Type} [Field K] [NumberField K]

/-! ### Reducing an integer in the residue ring of a completion -/

/-- An integer of a number field is an integer of the completion at a finite place. -/
theorem algebraMap_mem_divisionIntegers_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    algebraMap (𝓞 K) (v.adicCompletion K) x
      ∈ divisionIntegers (v.adicCompletion K) (v.adicCompletion K) := by
  rw [mem_divisionIntegers, divisionNorm_base, Valued.toNormedField.norm_le_one_iff]
  simpa using algebraMap_mem_valAddSubgroup_zero K v x

/-- The valuation of an integer of a number field in the completion at a finite place is its
valuation in the number field. -/
theorem valued_algebraMap_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) x) = v.intValuation x := by
  have hmap : algebraMap (𝓞 K) (v.adicCompletion K) x
      = ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) := rfl
  rw [hmap, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v),
    v.valuation_of_algebraMap]

/-- **The reduction of an integer of a number field in the residue ring of a completion.** -/
noncomputable def adicResidueHom (v : HeightOneSpectrum (𝓞 K)) :
    𝓞 K →+* DivisionResidue (v.adicCompletion K) (v.adicCompletion K) :=
  ((divisionResidueCon (v.adicCompletion K) (v.adicCompletion K)).mk').comp
    ((algebraMap (𝓞 K) (v.adicCompletion K)).codRestrict _
      (algebraMap_mem_divisionIntegers_adicCompletion v))

/-- The reduction of an integer vanishes exactly when the integer lies in the place. -/
theorem adicResidueHom_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    adicResidueHom v x = 0 ↔ x ∈ v.asIdeal := by
  rw [adicResidueHom, RingHom.comp_apply, RingCon.coe_mk', divisionResidue_eq_zero_iff]
  show divisionNorm (v.adicCompletion K) (v.adicCompletion K)
    (algebraMap (𝓞 K) (v.adicCompletion K) x) < 1 ↔ _
  rw [divisionNorm_base, Valued.toNormedField.norm_lt_one_iff, valued_algebraMap_adicCompletion]
  exact v.intValuation_lt_one_iff_mem x

/-- **The reduction of the integers of a number field fills the residue ring of a completion.**
The number field is dense in the completion, so every integer of the completion differs from an
integer of the number field by something of valuation less than one. -/
theorem adicResidueHom_surjective (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (adicResidueHom v) := by
  intro q
  obtain ⟨y, rfl⟩ := (divisionResidueCon (v.adicCompletion K) (v.adicCompletion K)).mk'_surjective q
  have hy : Valued.v (y : v.adicCompletion K) ≤ 1 := by
    have h := mem_divisionIntegers.1 y.2
    rw [divisionNorm_base] at h
    exact Valued.toNormedField.norm_le_one_iff.1 h
  obtain ⟨b, hb⟩ := exists_algebraMap_sub_le_exp_neg_one K v hy
  refine ⟨b, ?_⟩
  rw [adicResidueHom, RingHom.comp_apply, RingCon.coe_mk', divisionResidue_eq_iff]
  show divisionNorm (v.adicCompletion K) (v.adicCompletion K)
    (algebraMap (𝓞 K) (v.adicCompletion K) b - (y : v.adicCompletion K)) < 1
  rw [divisionNorm_base, Valued.toNormedField.norm_lt_one_iff,
    Valuation.map_sub_swap Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) b)
      (y : v.adicCompletion K)]
  refine lt_of_le_of_lt hb ?_
  simpa using WithZero.exp_lt_exp.mpr (show (-1 : ℤ) < 0 by norm_num)

/-! ### Counting the residues -/

/-- **The residue ring of a completion has as many elements as the residue field of the place.** -/
theorem natCard_divisionResidue_adicCompletion_eq_natCard_quotient
    (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (DivisionResidue (v.adicCompletion K) (v.adicCompletion K))
      = Nat.card (𝓞 K ⧸ v.asIdeal) := by
  have hker : RingHom.ker (adicResidueHom v) = v.asIdeal := by
    ext x
    simpa only [RingHom.mem_ker] using adicResidueHom_eq_zero_iff v x
  rw [← hker]
  exact (Nat.card_congr
    (RingHom.quotientKerEquivOfSurjective (adicResidueHom_surjective v)).toEquiv).symm

/-- **The completion of a number field at a place over `p` has `p` raised to the residue degree
many residues.** -/
theorem natCard_divisionResidue_adicCompletion_eq_pow_inertiaDeg {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K)) [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (DivisionResidue (v.adicCompletion K) (v.adicCompletion K))
      = p ^ (Ideal.span {(p : ℤ)}).inertiaDeg v.asIdeal := by
  rw [natCard_divisionResidue_adicCompletion_eq_natCard_quotient, ← Submodule.cardQuot_apply,
    ← Ideal.absNorm_apply]
  exact Ideal.absNorm_eq_pow_inertiaDeg' _ hp

end ResidueCardDegree

end InverseGalois.CFT

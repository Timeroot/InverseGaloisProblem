/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.NilpotentQuotient
import InverseGalois.CFT.Scholz.RadicalTower

/-!
# Radicals of rational numbers in a nilpotent extension

Adjoining an `ℓ`-th root of a rational number which is not already an `ℓ`-th power produces, for an
odd prime `ℓ`, a field whose Galois closure has no quotient of order `ℓ`.  A finite nilpotent group
whose order is divisible by `ℓ` does have such a quotient.  Consequently a Galois extension of the
rationals with nilpotent Galois group contains no new `ℓ`-th roots of rational numbers, provided it
contains the `ℓ`-th roots of unity: adjoining a root of unity and a single radical builds the whole
radical field inside it, whose Galois group would then be a nilpotent group of order divisible by
`ℓ`.

This is the source of the auxiliary primes of the Scholz–Reichardt construction: the field cut out
by a solution of the embedding problem together with the cyclotomic field of `ℓ`-power conductor is
such a nilpotent extension, so the products of the ramified primes stay non-radical there, and the
Chebotarev density theorem then produces primes with prescribed power residue behaviour.

## Main results

* `InverseGalois.CFT.radicalField_singleton_le`: the radical field of a single rational number sits
  inside any subfield of the algebraic closure containing a primitive `ℓ`-th root of unity and one
  `ℓ`-th root of that number.
* `InverseGalois.CFT.pow_ne_of_isNilpotent`: **a rational number which is not an `ℓ`-th power in the
  rationals is not an `ℓ`-th power in a Galois extension with nilpotent Galois group containing the
  `ℓ`-th roots of unity**, for `ℓ` an odd prime.

## Tags

radical extension, nilpotent group, Scholz–Reichardt, root of unity
-/

open Module Polynomial IntermediateField

namespace InverseGalois.CFT

variable {ℓ : ℕ} {B : IntermediateField ℚ (AlgebraicClosure ℚ)}

/-- **The radical field of a single rational number sits inside any subfield containing a primitive
`ℓ`-th root of unity and one `ℓ`-th root of that number.**  Every root of `X ^ ℓ - 1` is a power of
the given root of unity, and every root of `X ^ ℓ - m` is such a power times the given root. -/
theorem radicalField_singleton_le (hℓ : ℓ ≠ 0) {ζ u : AlgebraicClosure ℚ} {m : ℚ}
    (hζ : IsPrimitiveRoot ζ ℓ) (hζB : ζ ∈ B) (huB : u ∈ B)
    (hu : u ^ ℓ = algebraMap ℚ (AlgebraicClosure ℚ) m) (hm : m ≠ 0) :
    radicalField ℓ {m} ≤ B := by
  haveI : NeZero ℓ := ⟨hℓ⟩
  have hu0 : u ≠ 0 := by
    intro h
    exact hm (by simpa [h, zero_pow hℓ] using hu.symm)
  refine adjoin_le_iff.mpr fun α hα => ?_
  rw [Polynomial.mem_rootSet] at hα
  obtain ⟨-, h⟩ := hα
  rw [radicalPoly, map_prod] at h
  obtain ⟨c, hc, hzero⟩ := Finset.prod_eq_zero_iff.mp h
  simp only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at hzero
  rcases Finset.mem_insert.mp hc with rfl | hcm
  · obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (by simpa using hzero)
    exact hi ▸ pow_mem hζB i
  · rw [Finset.mem_singleton] at hcm
    subst hcm
    obtain ⟨i, -, hi⟩ : ∃ i < ℓ, ζ ^ i = α * u⁻¹ := by
      refine hζ.eq_pow_of_pow_eq_one ?_
      rw [mul_pow, inv_pow, hzero, hu, mul_inv_cancel₀]
      exact fun h => hm ((map_eq_zero (algebraMap ℚ (AlgebraicClosure ℚ))).mp h)
    have : α = ζ ^ i * u := by
      rw [hi, inv_mul_cancel_right₀ hu0]
    exact this ▸ mul_mem (pow_mem hζB i) huB

set_option synthInstance.maxHeartbeats 1000000 in
/-- **A rational number which is not an `ℓ`-th power in the rationals is not an `ℓ`-th power in a
Galois extension with nilpotent Galois group containing the `ℓ`-th roots of unity**, for `ℓ` an odd
prime.  An `ℓ`-th root would place the whole radical field inside the extension, making the Galois
group of that radical field a nilpotent group of order divisible by `ℓ`, hence one with a quotient
of order `ℓ`; radical fields have no such quotient. -/
theorem pow_ne_of_isNilpotent [Fact ℓ.Prime] (hodd : Odd ℓ) [FiniteDimensional ℚ ↥B]
    [IsGalois ℚ ↥B] (hnil : Group.IsNilpotent Gal(↥B/ℚ)) {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ ℓ) (hζB : ζ ∈ B) {m : ℚ} (hm : ∀ y : ℚ, y ^ ℓ ≠ m)
    {u : AlgebraicClosure ℚ} (huB : u ∈ B) : u ^ ℓ ≠ algebraMap ℚ (AlgebraicClosure ℚ) m := by
  intro hu
  haveI := hnil
  have hℓ : ℓ.Prime := Fact.out
  have hm0 : m ≠ 0 := fun h => hm 0 (by rw [h]; exact zero_pow hℓ.ne_zero)
  have hle : radicalField ℓ {m} ≤ B :=
    radicalField_singleton_le hℓ.ne_zero hζ hζB huB hu hm0
  haveI : IsGalois ℚ ↥(IntermediateField.restrict hle) :=
    IsGalois.of_algEquiv (IntermediateField.restrict_algEquiv hle)
  haveI : Group.IsNilpotent Gal(↥(IntermediateField.restrict hle)/ℚ) :=
    nilpotent_of_surjective _ (AlgEquiv.restrictNormalHom_surjective (F := ℚ) ↥B)
  haveI : Group.IsNilpotent Gal(↥(radicalField ℓ {m})/ℚ) :=
    nilpotent_of_mulEquiv (AlgEquiv.autCongr (IntermediateField.restrict_algEquiv hle).symm)
  have hdvd : ℓ ∣ Nat.card Gal(↥(radicalField ℓ {m})/ℚ) := by
    rw [IsGalois.card_aut_eq_finrank]
    obtain ⟨α, hα⟩ := exists_pow_eq_radicalField (S := {m}) hℓ.ne_zero (Finset.mem_singleton_self m)
    have haeval : (aeval α) (X ^ ℓ - C m) = 0 := by simp [hα]
    have hmin : minpoly ℚ α = X ^ ℓ - C m :=
      (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hℓ hm) haeval
        (monic_X_pow_sub_C m hℓ.ne_zero)).symm
    have hfr : finrank ℚ ↥ℚ⟮α⟯ = ℓ := by
      rw [adjoin.finrank (Algebra.IsIntegral.isIntegral α), hmin, natDegree_X_pow_sub_C]
    have htower := Module.finrank_mul_finrank ℚ ↥ℚ⟮α⟯ ↥(radicalField ℓ {m})
    rw [hfr] at htower
    exact ⟨_, htower.symm⟩
  exact not_exists_normal_quotient_card_radicalField hodd
    (exists_normal_quotient_card_eq_of_isNilpotent hℓ hdvd)

end InverseGalois.CFT

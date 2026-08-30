/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.FrobeniusTower

/-!
# The Frobenius automorphism over an intermediate local field

Let `K ⊆ M ⊆ L` be a tower of nonarchimedean local fields with `L / K` unramified, and suppose the
absolute value of `M` extends the absolute value of `K`.  The absolute value of a finite extension
of a complete field is the spectral norm, and the spectral norm is computed from the algebra norm,
which is transitive in a tower; so the absolute value of `L` is the same whether it is computed over
`K` or over `M`.

The Frobenius automorphism of `L / M` raises every residue to the power given by the number of
residues of `M`, which for an unramified `M / K` is the number of residues of `K` raised to the
degree.  Iterating the Frobenius automorphism of `L / K` that many times has exactly the same effect
on residues, and the Frobenius automorphism is unique; hence **the Frobenius automorphism of `L / M`
induces the `[M : K]`-th power of the Frobenius automorphism of `L / K`.**

## Main results

* `InverseGalois.CFT.isDivisionFrobenius_iff`: the Frobenius condition, spelled out with the
  absolute value.
* `InverseGalois.CFT.divisionNorm_eq_of_base`: **the absolute value of a finite extension does not
  depend on which of two compatibly normed base fields it is computed over.**
* `InverseGalois.CFT.unramified_base`: an unramified extension stays unramified over a compatibly
  normed intermediate field.
* `InverseGalois.CFT.eq_divisionFrobenius_of_restrictScalars`: **an automorphism inducing the
  `[M : K]`-th power of the Frobenius automorphism of `L / K` is the Frobenius automorphism of
  `L / M`.**

## Tags

local field, unramified extension, Frobenius, spectral norm, base change
-/

set_option synthInstance.maxHeartbeats 800000

universe u

namespace InverseGalois.CFT

open Module

/-! ### The Frobenius condition in terms of the absolute value -/

section Concrete

variable {K L : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]

/-- A power of a residue is the residue of the power. -/
theorem divisionResidue_pow (x : divisionIntegers K L) (n : ℕ) :
    ((x : divisionIntegers K L) : DivisionResidue K L) ^ n
      = ((x ^ n : divisionIntegers K L) : DivisionResidue K L) :=
  (map_pow ((divisionResidueCon K L).mk') x n).symm

/-- **The Frobenius condition, spelled out with the absolute value**: the automorphism moves every
integer to within distance one of its power. -/
theorem isDivisionFrobenius_iff (σ : L ≃ₐ[K] L) :
    IsDivisionFrobenius σ ↔ ∀ x : divisionIntegers K L,
      divisionNorm K L (σ (x : L) - (x : L) ^ Nat.card (DivisionResidue K K)) < 1 := by
  simp only [IsDivisionFrobenius]
  refine forall_congr' fun x => ?_
  rw [divisionResidue_pow, divisionResidue_eq_iff, coe_divisionIntegersAlgEquiv,
    SubmonoidClass.coe_pow]

/-- **A power of the Frobenius automorphism raises every residue to the corresponding power of the
number of residues of the base field.** -/
theorem divisionResidueHom_pow_eq {σ : L ≃ₐ[K] L} (hσ : IsDivisionFrobenius σ) (d : ℕ) :
    ∀ r : DivisionResidue K L,
      divisionResidueHom (σ ^ d) r = r ^ Nat.card (DivisionResidue K K) ^ d := by
  have hbase : ∀ r : DivisionResidue K L,
      divisionResidueHom σ r = r ^ Nat.card (DivisionResidue K K) := by
    intro r
    obtain ⟨x, rfl⟩ := (divisionResidueCon K L).mk'_surjective r
    rw [RingCon.coe_mk', divisionResidueHom_coe]
    exact hσ x
  induction d with
  | zero =>
    intro r
    rw [pow_zero, divisionResidueHom_one, RingHom.id_apply, pow_zero, pow_one]
  | succ d ih =>
    intro r
    rw [pow_succ, ← divisionResidueHom_comp, RingHom.comp_apply, hbase, ih, ← pow_mul, ← pow_succ']

/-- **A power of the Frobenius automorphism moves every integer to within distance one of the
corresponding power.** -/
theorem divisionNorm_pow_sub_lt_one {σ : L ≃ₐ[K] L} (hσ : IsDivisionFrobenius σ) (d : ℕ)
    (y : divisionIntegers K L) :
    divisionNorm K L ((σ ^ d) (y : L) - (y : L) ^ Nat.card (DivisionResidue K K) ^ d) < 1 := by
  have h := divisionResidueHom_pow_eq hσ d ((y : divisionIntegers K L) : DivisionResidue K L)
  rw [divisionResidueHom_coe, divisionResidue_pow, divisionResidue_eq_iff,
    coe_divisionIntegersAlgEquiv, SubmonoidClass.coe_pow] at h
  exact h

end Concrete

/-! ### The absolute value over a compatibly normed intermediate field -/

section Base

variable {K M L : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [NontriviallyNormedField M] [IsUltrametricDist M] [ProperSpace M]
variable [Algebra K M] [FiniteDimensional K M]
variable [Field L] [Algebra M L] [FiniteDimensional M L] [Algebra K L] [IsScalarTower K M L]

omit [IsUltrametricDist M] [ProperSpace M] in
/-- **A norm extending the norm of a complete nonarchimedean base field is the absolute value of the
extension**, because the spectral norm is the unique such norm. -/
theorem norm_eq_divisionNorm (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖) (y : M) :
    ‖y‖ = divisionNorm K M y := by
  rw [divisionNorm_eq_spectralNorm]
  exact spectralNorm_unique_field_norm_ext (K := K) (L := M)
    (f := NormedField.toAbsoluteValue M) hnorm y

omit [IsUltrametricDist M] [ProperSpace M] in
/-- **The absolute value of a finite extension does not depend on which of two compatibly normed
base fields it is computed over**, because the algebra norm is transitive in a tower. -/
theorem divisionNorm_eq_of_base (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖) (z : L) :
    divisionNorm M L z = divisionNorm K L z := by
  have hKM : ((finrank K M : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hML : ((finrank M L : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hfin : finrank K M * finrank M L = finrank K L := Module.finrank_mul_finrank K M L
  rw [divisionNorm, divisionNorm, norm_eq_divisionNorm hnorm, divisionNorm, Algebra.norm_norm,
    ← Real.rpow_mul (norm_nonneg _), ← hfin]
  refine congrArg _ ?_
  push_cast
  field_simp

omit [IsUltrametricDist M] [ProperSpace M] in
/-- **An unramified extension stays unramified over a compatibly normed intermediate field.** -/
theorem unramified_base (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (hurK : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖) :
    ∀ z : L, z ≠ 0 → ∃ c : M, c ≠ 0 ∧ divisionNorm M L z = ‖c‖ := by
  intro z hz
  obtain ⟨c, hc, hcz⟩ := hurK z hz
  refine ⟨algebraMap K M c, (map_ne_zero_iff _ (algebraMap K M).injective).2 hc, ?_⟩
  rw [divisionNorm_eq_of_base hnorm, hcz, hnorm]

/-! ### The Frobenius automorphism over the intermediate field -/

variable [FiniteDimensional K L]

/-- **An automorphism inducing the `[M : K]`-th power of the Frobenius automorphism of `L / K`
raises every residue to the power given by the number of residues of `M`.** -/
theorem isDivisionFrobenius_base (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (hq : Nat.card (DivisionResidue M M) = Nat.card (DivisionResidue K K) ^ finrank K M)
    {hurK : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖} {σ : L ≃ₐ[M] L}
    (hσ : σ.restrictScalars K = divisionFrobenius K L hurK ^ finrank K M) :
    IsDivisionFrobenius σ := by
  rw [isDivisionFrobenius_iff]
  intro x
  have hmem : (x : L) ∈ divisionIntegers K L := by
    rw [mem_divisionIntegers, ← divisionNorm_eq_of_base hnorm]
    exact mem_divisionIntegers.1 x.2
  have happ : σ (x : L) = (divisionFrobenius K L hurK ^ finrank K M) (x : L) := by
    rw [← hσ]
    rfl
  rw [hq, divisionNorm_eq_of_base hnorm, happ]
  exact divisionNorm_pow_sub_lt_one (isDivisionFrobenius_divisionFrobenius K L hurK) _
    ⟨(x : L), hmem⟩

/-- **An automorphism inducing the `[M : K]`-th power of the Frobenius automorphism of `L / K` is
the Frobenius automorphism of `L / M`.** -/
theorem eq_divisionFrobenius_of_restrictScalars (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (hq : Nat.card (DivisionResidue M M) = Nat.card (DivisionResidue K K) ^ finrank K M)
    {hurK : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖} {σ : L ≃ₐ[M] L}
    (hσ : σ.restrictScalars K = divisionFrobenius K L hurK ^ finrank K M) :
    σ = divisionFrobenius M L (unramified_base hnorm hurK) :=
  eq_divisionFrobenius M L _ (isDivisionFrobenius_base hnorm hq hσ)

end Base

end InverseGalois.CFT

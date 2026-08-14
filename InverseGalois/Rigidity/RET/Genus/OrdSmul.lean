/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.OrdMem

/-!
# Orders are invariant under automorphisms fixing the place

A ring automorphism carries the `j`-th power of an ideal onto the `j`-th power of its image, so an
automorphism fixing a height-one prime preserves membership in each of its powers.  Since the order
of an element at the prime is pinned by exactly those memberships, the order is invariant: a
decomposition-group element cannot change how deeply an element vanishes at the place it fixes.

This is the transport rule that lets a computation with orders at one place of a cover be read as a
statement about the deck transformations preserving that place — in particular about its inertia
group.

## Main results

* `Rigidity.RET.smul_mem_pow_iff_of_smul_eq` — membership in a power of a fixed prime is invariant.
* `Rigidity.RET.ord_smul_eq` — the order at a fixed prime is invariant.
-/

open IsDedekindDomain Pointwise

noncomputable section

namespace Rigidity.RET

variable {B : Type*} [CommRing B] [IsDedekindDomain B]
variable {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
variable {G : Type*} [Group G] [MulSemiringAction G B]

omit [IsDedekindDomain B] in
/-- An automorphism carries the `j`-th power of an ideal onto the `j`-th power of its image. -/
theorem smul_mem_pow_smul_iff (σ : G) (I : Ideal B) (j : ℕ) (x : B) :
    σ • x ∈ (σ • I) ^ j ↔ x ∈ I ^ j := by
  have h : (σ • I) ^ j = σ • I ^ j :=
    (map_pow (MulDistribMulAction.toMonoidHom (Ideal B) σ) I j).symm
  rw [h]
  exact Ideal.smul_mem_pointwise_smul_iff

omit [IsDedekindDomain B] in
/-- An automorphism fixing an ideal preserves membership in each of its powers. -/
theorem smul_mem_pow_iff_of_smul_eq {σ : G} {I : Ideal B} (hσ : σ • I = I) (j : ℕ) (x : B) :
    σ • x ∈ I ^ j ↔ x ∈ I ^ j := by
  conv_lhs => rw [← hσ]
  exact smul_mem_pow_smul_iff σ I j x

/-- Half of the invariance of the order: an automorphism fixing the place cannot decrease it. -/
theorem le_ord_smul_of_smul_eq {v : HeightOneSpectrum B} {σ : G} (hσ : σ • v.asIdeal = v.asIdeal)
    (x : B) : ord L v (algebraMap B L x) ≤ ord L v (algebraMap B L (σ • x)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ord_zero]
  have hσx : σ • x ≠ 0 := fun h => hx (by simpa using congrArg (fun y => σ⁻¹ • y) h)
  set j : ℕ := (ord L v (algebraMap B L x)).toNat with hj
  have hjx : (j : ℤ) = ord L v (algebraMap B L x) :=
    Int.toNat_of_nonneg (ord_nonneg (K := L) v x)
  have hmem : x ∈ v.asIdeal ^ j :=
    (mem_pow_iff_le_ord (K := L) v hx j).mpr hjx.le
  have := (mem_pow_iff_le_ord (K := L) v hσx j).mp
    ((smul_mem_pow_iff_of_smul_eq hσ j x).mpr hmem)
  omega

/-- **The order at a place is invariant under an automorphism fixing that place.** -/
theorem ord_smul_eq {v : HeightOneSpectrum B} {σ : G} (hσ : σ • v.asIdeal = v.asIdeal) (x : B) :
    ord L v (algebraMap B L (σ • x)) = ord L v (algebraMap B L x) := by
  refine le_antisymm ?_ (le_ord_smul_of_smul_eq hσ x)
  have hσ' : σ⁻¹ • v.asIdeal = v.asIdeal := by
    conv_lhs => rw [← hσ]
    rw [inv_smul_smul]
  simpa using le_ord_smul_of_smul_eq (L := L) hσ' (σ • x)

end Rigidity.RET

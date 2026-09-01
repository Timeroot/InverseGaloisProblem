/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Quotient

/-!
# The cohomology of an infinite Galois group

The Galois group of an arbitrary Galois extension carries the Krull topology, whose open normal
subgroups are exactly the subgroups fixing a finite Galois intermediate field.  Restriction to such
a field is surjective with that subgroup as kernel, so it is a smooth homomorphism with open
kernel, and composing a cochain with it is inflation from the finite level.

The two directions of the dictionary are both easy from the Mathlib description of the Krull
topology.  A finite Galois intermediate field gives an open normal subgroup, and conversely an open
subgroup is a neighbourhood of the identity, hence contains the subgroup fixing a finite
intermediate field, hence the one fixing its normal closure.  So the finite Galois levels are
cofinal among the open normal subgroups, and every class of the first or second cohomology is
represented by a cocycle that comes from one of them.

## Main definitions

* `InverseGalois.CFT.galInflH1`, `InverseGalois.CFT.galInflH2`: **inflation from a finite Galois
  level.**

## Main results

* `InverseGalois.CFT.isOpenNormal_fixingSubgroup`: the subgroup fixing a finite Galois intermediate
  field is open and normal.
* `InverseGalois.CFT.exists_fixingSubgroup_le`: **the finite Galois levels are cofinal**, every
  open normal subgroup containing one of them.
* `InverseGalois.CFT.galInflH1_injective`: **inflation is injective in the first cohomology.**
* `InverseGalois.CFT.exists_galInflH1_eq`, `InverseGalois.CFT.exists_galInflH2_eq`: **a class
  represented at a finite Galois level is inflated from it.**
* `InverseGalois.CFT.exists_isGalois_smooth₁`, `InverseGalois.CFT.exists_isGalois_smooth₂`:
  **every class is represented at a finite Galois level.**

## Tags

infinite Galois theory, Krull topology, Galois cohomology, inflation, smooth cochain
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### The subgroup fixing a finite Galois level -/

section Fixing

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (L : IntermediateField k K)

/-- The subgroup fixing a normal intermediate field is normal. -/
theorem normal_fixingSubgroup [Normal k L] : L.fixingSubgroup.Normal := by
  rw [← IntermediateField.restrictNormalHom_ker L]
  exact MonoidHom.normal_ker _

/-- **The subgroup fixing a finite Galois intermediate field is open and normal.** -/
theorem isOpenNormal_fixingSubgroup [FiniteDimensional k L] [Normal k L] :
    IsOpenNormal L.fixingSubgroup :=
  ⟨normal_fixingSubgroup L, L.fixingSubgroup_isOpen⟩

/-- The kernel of restriction to a finite Galois intermediate field is open and normal. -/
theorem isOpenNormal_ker_restrictNormalHom [FiniteDimensional k L] [Normal k L] :
    IsOpenNormal (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) L).ker := by
  rw [IntermediateField.restrictNormalHom_ker L]
  exact isOpenNormal_fixingSubgroup L

/-- Restriction to a finite Galois intermediate field is a smooth homomorphism. -/
theorem isSmoothHom_restrictNormalHom [FiniteDimensional k L] [Normal k L] :
    IsSmoothHom (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) L) :=
  isSmoothHom_of_isOpenNormal_ker (isOpenNormal_ker_restrictNormalHom L)

end Fixing

/-! ### The finite Galois levels are cofinal -/

section Cofinal

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  (L : IntermediateField k K)

/-- Restriction to a normal intermediate field of a Galois extension is surjective. -/
theorem restrictNormalHom_surjective_level [Normal k L] :
    Function.Surjective (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) L) :=
  AlgEquiv.restrictNormalHom_surjective _

/-- **Every open normal subgroup of an infinite Galois group contains the subgroup fixing a finite
Galois intermediate field.** -/
theorem exists_fixingSubgroup_le {N : Subgroup Gal(K/k)} (hN : IsOpenNormal N) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧ IsGalois k E ∧ E.fixingSubgroup ≤ N := by
  have hmem : (N : Set Gal(K/k)) ∈ nhds (1 : Gal(K/k)) := hN.isOpen.mem_nhds N.one_mem
  obtain ⟨E, hfin, hnorm, hle⟩ := (krullTopology_mem_nhds_one_iff_of_normal k K _).1 hmem
  haveI := hfin
  haveI := hnorm
  have hON : IsOpen E.fixingSubgroup.carrier ∧ E.fixingSubgroup.Normal :=
    ⟨E.fixingSubgroup_isOpen, normal_fixingSubgroup E⟩
  obtain ⟨-, hgal⟩ := (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois E).1 hON
  exact ⟨E, hfin, hgal, hle⟩

end Cofinal

/-! ### Inflation from a finite Galois level -/

section Inflation

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  (L : IntermediateField k K) [FiniteDimensional k L] [IsGalois k L]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(K/k) M]
  [MulDistribMulAction (L ≃ₐ[k] L) M]
  (hπ : ∀ (g : Gal(K/k)) (m : M), g • m = AlgEquiv.restrictNormalHom L g • m)

include hπ

/-- **Inflation from a finite Galois level, in the first cohomology.** -/
noncomputable def galInflH1 : SmoothH1 (L ≃ₐ[k] L) M →* SmoothH1 Gal(K/k) M :=
  comapH1 _ hπ (isSmoothHom_restrictNormalHom L)

/-- **Inflation from a finite Galois level, in the second cohomology.** -/
noncomputable def galInflH2 : SmoothH2 (L ≃ₐ[k] L) M →* SmoothH2 Gal(K/k) M :=
  comapH2 _ hπ (isSmoothHom_restrictNormalHom L)

/-- **Inflation from a finite Galois level is injective in the first cohomology.** -/
theorem galInflH1_injective : Function.Injective (galInflH1 L hπ) :=
  comapH1_injective hπ (isSmoothHom_restrictNormalHom L)
    (restrictNormalHom_surjective_level L)

/-- **A class of the first cohomology whose restriction to a finite Galois level is a coboundary is
inflated from that level.** -/
theorem exists_galInflH1_eq [IsSmoothAction Gal(K/k) M] {v : Gal(K/k) → M} (hv : IsMulCocycle₁ v)
    (hvs : IsSmooth₁ v) (t : M) (ht : ∀ σ ∈ L.fixingSubgroup, σ • t / t = v σ) :
    ∃ z : SmoothH1 (L ≃ₐ[k] L) M, galInflH1 L hπ z = smoothH1Mk v hv hvs := by
  refine exists_comapH1_eq hπ (isSmoothHom_restrictNormalHom L)
    (restrictNormalHom_surjective_level L) hv hvs t fun σ hσ => ht σ ?_
  rwa [IntermediateField.restrictNormalHom_ker L] at hσ

/-- **A class of the second cohomology represented by a cocycle constant on the cosets of a finite
Galois level is inflated from that level.** -/
theorem exists_galInflH2_eq {a : Gal(K/k) × Gal(K/k) → M} (ha : IsMulCocycle₂ a)
    (has : IsSmooth₂ a) (hs : ∀ x y : Gal(K/k), ∀ σ ∈ L.fixingSubgroup, ∀ τ ∈ L.fixingSubgroup,
      a (x * σ, y * τ) = a (x, y)) :
    ∃ z : SmoothH2 (L ≃ₐ[k] L) M, galInflH2 L hπ z = smoothH2Mk a ha has := by
  refine exists_comapH2_eq hπ (isSmoothHom_restrictNormalHom L)
    (restrictNormalHom_surjective_level L) ha has fun x y σ hσ τ hτ => hs x y σ ?_ τ ?_
  · rwa [IntermediateField.restrictNormalHom_ker L] at hσ
  · rwa [IntermediateField.restrictNormalHom_ker L] at hτ

end Inflation

/-! ### Every class lives at a finite Galois level -/

section Levels

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {M : Type*} [CommGroup M] [MulDistribMulAction Gal(K/k) M] [IsSmoothAction Gal(K/k) M]

/-- **Every class of the first cohomology of an infinite Galois group is represented at a finite
Galois level**: by a cocycle constant on the cosets of the subgroup fixing a finite Galois
intermediate field, which acts trivially on the coefficients. -/
theorem exists_isGalois_smooth₁ (z : SmoothH1 Gal(K/k) M) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧ IsGalois k E ∧
      (∀ σ ∈ E.fixingSubgroup, ∀ m : M, σ • m = m) ∧
      ∃ (u : Gal(K/k) → M) (hu : IsMulCocycle₁ u) (hs : IsSmooth₁ u),
        (∀ g : Gal(K/k), ∀ σ ∈ E.fixingSubgroup, u (g * σ) = u g) ∧ smoothH1Mk u hu hs = z := by
  obtain ⟨N, hN, hact, u, hu, hs, hcon, hz⟩ := exists_isOpenNormal_smooth₁ z
  obtain ⟨E, hfin, hgal, hle⟩ := exists_fixingSubgroup_le hN
  exact ⟨E, hfin, hgal, fun σ hσ m => hact σ (hle hσ) m, u, hu, hs,
    fun g σ hσ => hcon g σ (hle hσ), hz⟩

/-- **Every class of the second cohomology of an infinite Galois group is represented at a finite
Galois level**: by a cocycle constant on the cosets of the subgroup fixing a finite Galois
intermediate field, which acts trivially on the coefficients. -/
theorem exists_isGalois_smooth₂ (z : SmoothH2 Gal(K/k) M) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧ IsGalois k E ∧
      (∀ σ ∈ E.fixingSubgroup, ∀ m : M, σ • m = m) ∧
      ∃ (a : Gal(K/k) × Gal(K/k) → M) (ha : IsMulCocycle₂ a) (hs : IsSmooth₂ a),
        (∀ x y : Gal(K/k), ∀ σ ∈ E.fixingSubgroup, ∀ τ ∈ E.fixingSubgroup,
          a (x * σ, y * τ) = a (x, y)) ∧ smoothH2Mk a ha hs = z := by
  obtain ⟨N, hN, hact, a, ha, hs, hcon, hz⟩ := exists_isOpenNormal_smooth₂ z
  obtain ⟨E, hfin, hgal, hle⟩ := exists_fixingSubgroup_le hN
  exact ⟨E, hfin, hgal, fun σ hσ m => hact σ (hle hσ) m, a, ha, hs,
    fun x y σ hσ τ hτ => hcon x y σ (hle hσ) τ (hle hτ), hz⟩

end Levels

end InverseGalois.CFT

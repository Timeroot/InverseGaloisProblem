/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.H1Transport
import InverseGalois.CFT.Units.IdeleClassComap
import InverseGalois.CFT.Units.IdeleNormTower
import InverseGalois.CFT.Units.IdeleRep

/-!
# The first cohomology of the idele class group along a tower

Let a tower of number fields have a middle field normal over the base and a top field Galois over
the base.  Restriction to the middle field is a surjection of the Galois group of the top field over
the base onto the Galois group of the middle field over the base, whose kernel is the group of
automorphisms fixing the middle field pointwise; and the idele class group of the middle field sits
inside the idele class group of the top field as the part fixed by that kernel.

That is exactly the situation of the dévissage for the first cohomology.  A `1`-cocycle of the top
group restricts to a `1`-cocycle of the kernel, which is a coboundary when the first cohomology over
the middle field vanishes; correcting by that coboundary makes the cocycle vanish on the kernel, so
it comes from a `1`-cocycle of the Galois group of the middle field over the base, and that one is a
coboundary when the first cohomology of the middle field vanishes.

## Main definitions

* `InverseGalois.CFT.ideleClassComapLin`: the inclusion of the idele classes of a subfield, as a
  linear map of the underlying modules of the representations.

## Main results

* `InverseGalois.CFT.eq_zero_H1_ideleClassRep_of_tower`: **the first cohomology of the idele class
  group of the top field over the base vanishes as soon as it vanishes for the middle field over
  the base and for the top field over the middle field.**

## Tags

number field, idele class group, group cohomology, tower, dévissage
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open groupCohomology

namespace InverseGalois.CFT

section Tower

variable {k F K : Type} [Field k] [NumberField k] [Field F] [NumberField F] [Field K]
  [NumberField K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]
  [IsGalois k F] [IsGalois F K] [IsGalois k K]

/-- The inclusion of the idele classes of a subfield, as a linear map of the underlying modules of
the representations. -/
noncomputable def ideleClassComapLin (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [IsGalois F K] : IdeleClass F →ₗ[ℤ] IdeleClass K :=
  (ideleClassComap F K).toIntLinearMap

@[simp]
theorem ideleClassComapLin_apply (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [IsGalois F K] (x : IdeleClass F) :
    ideleClassComapLin F K x = ideleClassComap F K x := rfl

omit [NumberField k] in
/-- **Dévissage of the first cohomology of the idele class group along a tower.**  If the first
cohomology of the idele class group of the middle field over the base vanishes, and so does the
first cohomology of the idele class group of the top field over the middle field, then the first
cohomology of the idele class group of the top field over the base vanishes. -/
theorem eq_zero_H1_ideleClassRep_of_tower
    (hF : ∀ y : groupCohomology (ideleClassRep k F) 1, y = 0)
    (hKF : ∀ y : groupCohomology (ideleClassRep F K) 1, y = 0)
    (z : groupCohomology (ideleClassRep k K) 1) : z = 0 := by
  refine eq_zero_H1_of_devissage (A := ideleClassRep k K) (B := ideleClassRep k F)
    (π := AlgEquiv.restrictNormalHom F)
    (hπ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := F) (E := K))
    (φ := ideleClassComapLin F K)
    (hφinj := fun _ _ h => ideleClassComap_injective F K h)
    (hφeq := fun g b => (ideleClassAut_ideleClassComap F g b).symm)
    (hφrange := fun a ha => ?_) (hres := fun x => ?_) (hB := hF) z
  · obtain ⟨b, hb⟩ := (mem_range_ideleClassComap_iff F K a).mpr
      fun σ => ha (σ.restrictScalars k) (restrictNormalHom_restrictScalars k F σ)
    exact ⟨b, hb⟩
  · have hmem : (fun σ : Gal(K/F) =>
        (x : Gal(K/k) → IdeleClass K) (σ.restrictScalars k)) ∈ cocycles₁ (ideleClassRep F K) := by
      rw [mem_cocycles₁_iff]
      intro σ τ
      exact (mem_cocycles₁_iff (x : Gal(K/k) → IdeleClass K)).1 x.2
        (σ.restrictScalars k) (τ.restrictScalars k)
    obtain ⟨b, hb⟩ := (H1π_eq_zero_iff _).1 (hKF (H1π _ ⟨_, hmem⟩))
    refine ⟨b, fun s hs => ?_⟩
    obtain ⟨σ, rfl⟩ := exists_restrictScalars_of_restrictNormalHom_eq_one k hs
    have hbσ : (ideleClassRep F K).ρ σ b - b
        = (x : Gal(K/k) → IdeleClass K) (σ.restrictScalars k) := congrFun hb σ
    exact hbσ.symm

end Tower

end InverseGalois.CFT

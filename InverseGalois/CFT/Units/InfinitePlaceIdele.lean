/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.InfiniteFamily
import InverseGalois.CFT.Units.Idele
import InverseGalois.CFT.Units.PlaceIdele

/-!
# The component of an idele at an infinite place

An idele of a number field has a component at every place, the archimedean ones included, and
reading that component is a homomorphism to the units of the completion there.  A Galois
automorphism permutes the archimedean components exactly as it permutes the finite ones, so an
automorphism fixing an infinite place moves the component there by the action of the decomposition
group, and reading the component is equivariant for that group.

The component of a principal idele is the image of the unit in the completion, and the component of
an idele supported at a single finite place is trivial.  These are the archimedean halves of the
computations that separate a distinguished finite place from all the others.

## Main definitions

* `InverseGalois.CFT.infinitePlaceComponent`: **the component at an infinite place of an idele.**

## Main results

* `InverseGalois.CFT.infinitePlaceComponent_ideleAut_stabilizer`: **reading the component at an
  infinite place is equivariant for the decomposition group there.**
* `InverseGalois.CFT.infinitePlaceComponent_ideleDiag`: the component of a principal idele is the
  image of the unit in the completion.
* `InverseGalois.CFT.infinitePlaceComponent_adicPlaceIdele`: the component at an infinite place of
  an idele supported at a finite place is trivial.

## Tags

number field, idele, infinite place, completion, decomposition group, Galois action
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

noncomputable section

section Component

variable {K : Type*} [Field K] [NumberField K] (u : InfinitePlace K)

/-- **The component at an infinite place of an idele.** -/
def infinitePlaceComponent : ↥(idele K) →+ Additive u.Completionˣ where
  toFun x := (x : FullIdele K).1 u
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem infinitePlaceComponent_apply (x : ↥(idele K)) :
    infinitePlaceComponent u x = (x : FullIdele K).1 u := rfl

/-- The component at an infinite place of a principal idele is the image of the unit in the
completion there. -/
@[simp]
theorem infinitePlaceComponent_ideleDiag (a : Additive Kˣ) :
    infinitePlaceComponent u (ideleDiag K a) = Additive.ofMul (infiniteUnitHom u a.toMul) := rfl

/-- The component at an infinite place of an idele supported at a finite place is trivial. -/
@[simp]
theorem infinitePlaceComponent_adicPlaceIdele (v : HeightOneSpectrum (𝓞 K))
    (a : Additive (v.adicCompletion K)ˣ) :
    infinitePlaceComponent u (adicPlaceIdele K v a) = 0 := rfl

end Component

section Equivariance

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K] (u : InfinitePlace K)

/-- **An automorphism fixing an infinite place moves the component of an idele there by the
transport of the family at that place.** -/
theorem infinitePlaceComponent_ideleAut (σ : Gal(K/k)) (hσ : σ • u = u) (x : ↥(idele K)) :
    infinitePlaceComponent u (ideleAut (k := k) σ x)
      = (infiniteRingFamily (k := k) (K := K)).unitsFamily.transport hσ
          (infinitePlaceComponent u x) := by
  rw [infinitePlaceComponent_apply, coe_ideleAut, fullIdeleAut, prodAut_apply]
  show (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ ((x : FullIdele K).1) u
    = (infiniteRingFamily (k := k) (K := K)).unitsFamily.transport hσ
        (infinitePlaceComponent u x)
  rw [FamilyAction.familyAut_apply_eq_transport _ hσ, infinitePlaceComponent_apply]

/-- **Reading the component at an infinite place is equivariant for the decomposition group
there.** -/
theorem infinitePlaceComponent_ideleAut_stabilizer (σ : ↥(stabilizer Gal(K/k) u))
    (x : ↥(idele K)) :
    infinitePlaceComponent u (ideleAut (k := k) (σ : Gal(K/k)) x)
      = smulUnitsAut σ (infinitePlaceComponent u x) := by
  rw [infinitePlaceComponent_ideleAut u (σ : Gal(K/k)) (mem_stabilizer_iff.mp σ.2) x,
    transport_infiniteUnitsFamily u (σ : Gal(K/k)) (mem_stabilizer_iff.mp σ.2) _]

end Equivariance

end

end InverseGalois.CFT

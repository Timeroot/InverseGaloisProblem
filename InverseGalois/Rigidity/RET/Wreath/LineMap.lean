/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Descent.GeomAKLB
import InverseGalois.Rigidity.RET.LineParam

/-!
# Finite maps to the line, and the model attached to a chosen coordinate

A cover of the line is packaged by `LineCover` as a finite *Galois* extension of `ℚ̄(T)` carrying
the integral model `ℚ̄[X] ⊆ M`.  That Galois hypothesis is exactly what one has to give up when a
covering surface is looked at through a coordinate that was not the one it was built from: if `M`
is a Galois extension of `ℚ̄(T)` and `θ ∈ M` is any non-constant function, then `θ` presents `M` as
a finite extension of `ℚ̄(θ)`, and that extension is almost never Galois.  Yet all of the local
theory — places, orders, ramification — depends only on the finiteness, so it is worth having the
Galois-free version of the package.

`LineMap` is that version: `LineCover` with `IsGalois` deleted.  The algebra structures are
*structure fields* rather than instances, and this is not incidental.  A field `F` carries at most
one `Algebra ℚ̄(T) F` instance that typeclass search can find, whereas the whole point here is to
equip one and the same `F` with the algebra structure determined by a chosen `θ`; since `θ` is not
recoverable from the goal, no such structure can live in the instance cache.  Carrying it in a
structure field, and only opening it with `attribute [instance]` on the projections, makes the
choice explicit and keeps the two possible readings of `F` from colliding.

The integral model of a line map is the integral closure `R` of `ℚ̄[X]` in `M`, which is a Dedekind
domain with fraction field `M`, so that the order function of `Genus.Ord` applies to it; the
coordinate `T` is the image of `X`.  Finally `ofParam` performs the construction described above,
turning a transcendental `θ` in a field `F` over `ℚ̄` into a line map whose coordinate is `θ`.

## Main definitions

* `Rigidity.RET.Wreath.LineMap` — a finite, not necessarily Galois, extension of `ℚ̄(T)` with its
  integral model.
* `Rigidity.RET.Wreath.LineMap.R` — the integral closure of `ℚ̄[X]` in the covering field.
* `Rigidity.RET.Wreath.LineMap.T` — the coordinate, the image of `X` in the covering field.
* `Rigidity.RET.Wreath.LineMap.ofParam` — the line map presented by a transcendental element.

## Main results

* `Rigidity.RET.Wreath.LineMap.ofParam_M` — the covering field of `ofParam` is the field it was
  built from.
* `Rigidity.RET.Wreath.LineMap.ofParam_T` — the coordinate of `ofParam` is the chosen element.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Wreath

open GeomAKLB (k)

/-- A **finite map to the line** over the algebraically closed constant field `ℚ̄`, given by its
function field: a finite extension `M / ℚ̄(T)`, not assumed Galois, together with the integral
model `ℚ̄[X] ⊆ M` through which the places of the line above a point are addressed, and the
constant field `ℚ̄` sitting inside everything compatibly. -/
structure LineMap where
  /-- the function field of the source of the map. -/
  M : Type
  [field : Field M]
  [alg : Algebra (RatFunc k) M]
  [algk : Algebra k M]
  [algPoly : Algebra (Polynomial k) M]
  [tower : IsScalarTower (Polynomial k) (RatFunc k) M]
  [towerk : IsScalarTower k (Polynomial k) M]
  [towerk' : IsScalarTower k (RatFunc k) M]
  [findim : FiniteDimensional (RatFunc k) M]

namespace LineMap

attribute [instance] LineMap.field LineMap.alg LineMap.algk LineMap.algPoly LineMap.tower
  LineMap.towerk LineMap.towerk' LineMap.findim

/-- The **integral model** of a finite map to the line: the integral closure of `ℚ̄[X]` in the
function field.  Its height-one primes are the places of the source lying over the affine line. -/
abbrev R (L : LineMap) : Type := ↥(integralClosure (Polynomial k) L.M)

set_option synthInstance.maxHeartbeats 400000

/-- **The function field is the fraction field of the integral model.** -/
instance instIsFractionRing (L : LineMap) : IsFractionRing L.R L.M :=
  IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial k) (RatFunc k) L.M _

/-- **The integral model is a Dedekind domain**, so its height-one primes carry an order
function. -/
instance instIsDedekindDomain (L : LineMap) : IsDedekindDomain L.R :=
  integralClosure.isDedekindDomain (Polynomial k) (RatFunc k) L.M

/-- **The integral model is a finite module over the polynomial ring.** -/
instance instModuleFinite (L : LineMap) : Module.Finite (Polynomial k) L.R :=
  IsIntegralClosure.finite (Polynomial k) (RatFunc k) L.M _

/-- **The integral model is integral over the polynomial ring.** -/
instance instIsIntegral (L : LineMap) : Algebra.IsIntegral (Polynomial k) L.R :=
  IsIntegralClosure.isIntegral_algebra (Polynomial k) L.M

/-- **The polynomial ring embeds in the integral model.**  A polynomial already becomes zero in the
function field only if it is zero, and the integral model sits inside the function field. -/
instance instFaithfulSMul (L : LineMap) : FaithfulSMul (Polynomial k) L.R := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have hAL : Function.Injective (algebraMap (Polynomial k) L.M) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial k) (RatFunc k) L.M]
    exact (algebraMap (RatFunc k) L.M).injective.comp
      (IsFractionRing.injective (Polynomial k) (RatFunc k))
  intro x y hxy
  apply hAL
  rw [IsScalarTower.algebraMap_apply (Polynomial k) L.R L.M,
    IsScalarTower.algebraMap_apply (Polynomial k) L.R L.M, hxy]

/-- The **coordinate** of a finite map to the line: the image in the function field of the
coordinate `X` of the affine line downstairs. -/
abbrev T (L : LineMap) : L.M := algebraMap (Polynomial k) L.M X

/-- **A transcendental element presents its field as a finite map to the line.**  Reading a field
`F` over `ℚ̄` through a transcendental `θ` embeds `ℚ̄(T)` into `F` by `T ↦ θ`, and the resulting
extension, once known to be finite, is a finite map to the line whose coordinate is `θ`.  The
`ℚ̄`-algebra structure of `F` is untouched by the reading, so the constant field is the same one it
started with. -/
def ofParam (F : Type) [Field F] [Algebra k F] (θ : F) (hθ : Transcendental k θ)
    (hfin : @FiniteDimensional (RatFunc k) F _ _
      (@Algebra.toModule _ _ _ _ ((paramHom (M := F) θ hθ).toAlgebra))) : LineMap :=
  letI : Algebra (RatFunc k) F := (paramHom (M := F) θ hθ).toAlgebra
  letI : Algebra (Polynomial k) F :=
    ((algebraMap (RatFunc k) F).comp (algebraMap (Polynomial k) (RatFunc k))).toAlgebra
  haveI : IsScalarTower (Polynomial k) (RatFunc k) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hC : ∀ c : k, (paramHom (M := F) θ hθ) (algebraMap k (RatFunc k) c)
      = algebraMap k F c := fun c => by
    rw [IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k), paramHom_algebraMap]
    simp
  haveI : IsScalarTower k (Polynomial k) F := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap k F c = _
    rw [RingHom.algebraMap_toAlgebra]
    show _ = (paramHom (M := F) θ hθ) _
    rw [← IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k), hC]
  haveI : IsScalarTower k (RatFunc k) F := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap k F c = _
    rw [RingHom.algebraMap_toAlgebra]
    exact (hC c).symm
  haveI := hfin
  { M := F }

/-- **The reading of a field through a transcendental element leaves the field alone.** -/
@[simp]
theorem ofParam_M (F : Type) [Field F] [Algebra k F] (θ : F) (hθ : Transcendental k θ)
    (hfin : @FiniteDimensional (RatFunc k) F _ _
      (@Algebra.toModule _ _ _ _ ((paramHom (M := F) θ hθ).toAlgebra))) :
    (ofParam F θ hθ hfin).M = F := rfl

/-- **The coordinate of the reading is the element it was read through.** -/
@[simp]
theorem ofParam_algebraMap_X (F : Type) [Field F] [Algebra k F] (θ : F)
    (hθ : Transcendental k θ)
    (hfin : @FiniteDimensional (RatFunc k) F _ _
      (@Algebra.toModule _ _ _ _ ((paramHom (M := F) θ hθ).toAlgebra))) :
    algebraMap (Polynomial k) (ofParam F θ hθ hfin).M X = θ := by
  show (paramHom (M := F) θ hθ) (algebraMap (Polynomial k) (RatFunc k) X) = θ
  rw [paramHom_algebraMap]
  simp

/-- **The coordinate of the reading is the element it was read through**, stated for the coordinate
of the line map. -/
theorem ofParam_T (F : Type) [Field F] [Algebra k F] (θ : F) (hθ : Transcendental k θ)
    (hfin : @FiniteDimensional (RatFunc k) F _ _
      (@Algebra.toModule _ _ _ _ ((paramHom (M := F) θ hθ).toAlgebra))) :
    (ofParam F θ hθ hfin).T = θ :=
  ofParam_algebraMap_X F θ hθ hfin

end LineMap

end Rigidity.RET.Wreath

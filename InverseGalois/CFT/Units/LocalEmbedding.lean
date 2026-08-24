/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicFamily
import InverseGalois.CFT.Local.InfiniteFamily
import InverseGalois.CFT.Local.UnitValuation
import InverseGalois.Rigidity.RET.Genus.OrdValuation

/-!
# A unit of a number field as a unit of each completion

The ideles of a number field receive the multiplicative group of the field itself: a nonzero element
is a unit of every completion, and the resulting family of local units is the diagonal image of the
element.  This file records the local pieces of that diagonal, one at each place.

At a finite place the valuation of the local unit is the order of the element at the corresponding
prime, up to sign: the valuation of the completion extends the valuation of the field, and the
valuation of the field is the exponential of minus the order.  At an infinite place there is nothing
to compute, but the embedding is injective, which is what makes the diagonal injective.

## Main definitions

* `InverseGalois.CFT.adicUnitHom`: **a unit of the field as a unit of the completion at a finite
  place.**
* `InverseGalois.CFT.infiniteUnitHom`: **a unit of the field as a unit of the completion at an
  infinite place.**

## Main results

* `InverseGalois.CFT.unitVal_adicUnitHom`: **the valuation of the local unit at a finite place is
  minus the order of the element at the corresponding prime.**
* `InverseGalois.CFT.infiniteUnitHom_injective`: the embedding at an infinite place is injective.

## Tags

number field, completion, unit, valuation, order, idele
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### The local unit at a finite place -/

section Finite

variable {K : Type*} [Field K] [NumberField K]

/-- **A unit of the field as a unit of the completion at a finite place.** -/
noncomputable def adicUnitHom (v : HeightOneSpectrum (𝓞 K)) : Kˣ →* (v.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.adicCompletion K) : K →+* v.adicCompletion K).toMonoidHom

@[simp]
theorem coe_adicUnitHom (v : HeightOneSpectrum (𝓞 K)) (y : Kˣ) :
    ((adicUnitHom v y : (v.adicCompletion K)ˣ) : v.adicCompletion K) = adicCoe (y : K) v := rfl

/-- **The valuation of the local unit at a finite place is minus the order of the element at the
corresponding prime**, because the valuation of the completion extends the valuation of the field
and the latter is the exponential of minus the order. -/
theorem unitVal_adicUnitHom (v : HeightOneSpectrum (𝓞 K)) (y : Kˣ) :
    unitVal (Additive.ofMul (adicUnitHom v y)) = -ord K v (y : K) := by
  rw [unitVal_apply, coe_adicUnitHom]
  show WithZero.log (Valued.v (((y : K) : WithVal (v.valuation K)) : v.adicCompletion K)) = _
  rw [Valued.valuedCompletion_apply]
  show WithZero.log (v.valuation K (y : K)) = _
  rw [valuation_eq_exp_neg_ord K v (Units.ne_zero y), WithZero.log_exp]

end Finite

/-! ### The local unit at an infinite place -/

section Infinite

variable {K : Type*} [Field K]

/-- **A unit of the field as a unit of the completion at an infinite place.** -/
noncomputable def infiniteUnitHom (w : InfinitePlace K) : Kˣ →* w.Completionˣ :=
  Units.map (algebraMap K w.Completion : K →+* w.Completion).toMonoidHom

@[simp]
theorem coe_infiniteUnitHom (w : InfinitePlace K) (y : Kˣ) :
    ((infiniteUnitHom w y : w.Completionˣ) : w.Completion) = infiniteCoe (y : K) w := rfl

/-- The embedding of the units of the field into the units of a completion at an infinite place is
injective, the completion being a field extension. -/
theorem infiniteUnitHom_injective (w : InfinitePlace K) :
    Function.Injective (infiniteUnitHom w) := fun _ _ h =>
  Units.ext ((algebraMap K w.Completion).injective (congrArg Units.val h))

end Infinite

end InverseGalois.CFT

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.OrbitDivisor
import InverseGalois.CFT.PoitouTate.TensorInvariant
import InverseGalois.CFT.Units.OrdFinsupp

/-!
# The order vector of a number field as an equivariant valuation

The abstract descent asks for an abelian group carrying an equivariant valuation onto the free
abelian group on a permuted set of places, whose kernel is the coefficient group of the
obstruction.  For a number field the group is the units of the field, the places are the primes
outside a finite set stable under the Galois group, the valuation is the vector of orders, and its
kernel is the group of units for that set.

Everything asked for is already available: the order vector is **onto** once the set carries the
ideal classes, it is **equivariant** because an automorphism moves the order of an element along
the permutation it induces on the primes, and its **kernel** is the group of units for the set.
This file records the three facts in the form the descent consumes, in terms of the action of the
Galois group on the units rather than of the additive automorphism it induces.

## Main results

* `InverseGalois.CFT.ordFinsupp_smul_apply`: **the order vector is equivariant**, in the pointwise
  form the descent asks for.
* `InverseGalois.CFT.mem_sUnits_iff_ordFinsupp_eq_zero`: **the kernel of the order vector is the
  group of units for the set.**

## Tags

number field, height one prime, order, S-unit, Galois action, valuation, descent
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

section Ord

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]
variable (T : Set (HeightOneSpectrum (𝓞 K)))

omit [NumberField K] in
/-- The action of an automorphism on a unit of the field is the action on the field itself. -/
theorem coe_galSMul_units (σ : Gal(K/k)) (a : Kˣ) : ((σ • a : Kˣ) : K) = σ (a : K) := rfl

omit [NumberField K] in
/-- The additive automorphism of the units induced by an automorphism of the field is the action
of that automorphism. -/
theorem globalUnitsAut_ofMul (σ : Gal(K/k)) (a : Kˣ) :
    globalUnitsAut σ (Additive.ofMul a) = Additive.ofMul (σ • a) :=
  Additive.toMul.injective (Units.ext rfl)

variable [IsGaloisStablePlaces k K T]

/-- **The order vector is equivariant**: the order of a translated unit at a translated prime is
the order of the unit at the prime. -/
theorem ordFinsupp_smul_apply (σ : Gal(K/k)) (a : Kˣ)
    (y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) :
    ordFinsupp T (Additive.ofMul (σ • a)) (σ • y) = ordFinsupp T (Additive.ofMul a) y := by
  rw [← globalUnitsAut_ofMul, ordFinsupp_globalUnitsAut, inv_smul_smul]

/-- **The kernel of the order vector is the group of units for the set.** -/
theorem mem_sUnits_iff_ordFinsupp_eq_zero (a : Kˣ) :
    a ∈ sUnits K T ↔ ordFinsupp T (Additive.ofMul a) = 0 :=
  (mem_ker_ordFinsupp T (u := Additive.ofMul a)).symm.trans AddMonoidHom.mem_ker

end Ord

end InverseGalois.CFT

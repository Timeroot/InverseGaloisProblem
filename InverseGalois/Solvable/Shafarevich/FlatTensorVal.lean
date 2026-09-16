/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.OrdInvariant
import InverseGalois.CFT.PoitouTate.SUnitReduce
import InverseGalois.Solvable.Shafarevich.FlatTwist

/-!
# The valuation of a presented tensor, read as the prescription

The descent through the units for a finite set of places produces a tensor together with the value
of its valuation at each place outside that set.  The flat prescription, on the other hand, asks
for a product of powers of a fixed family of the target, the exponents being the values of a family
of units at a named place, read modulo the exponent.

The two are the same statement.  A tensor presented along the fixed family is the sum of the pure
tensors of a family of units against it, its valuation at a place is the product of the powers of
the family by the orders of the units there, and the value of a unit at a place is minus its order.
So the valuation of the presented tensor at a named place is the inverse of the product the
prescription asks for, and prescribing one prescribes the other.

## Main results

* `InverseGalois.Shafarevich.zpow_eq_pow_val` — a power of an element killed by the exponent is
  read off the residue of the exponent.
* `InverseGalois.Shafarevich.tensorVal_sum_tmul` — **the valuation of a presented tensor is the
  product of the powers of the coefficient family by the orders of the radicands.**
* `InverseGalois.Shafarevich.prod_pow_placeValue_val_eq_of_tensorVal` — **prescribing the valuation
  of a presented tensor prescribes the product of powers the flat prescription asks for.**

## Tags

Shafarevich's theorem, Kummer theory, tensor product, valuation, order, number field
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain NumberField Rigidity.RET TensorProduct

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### Integer powers modulo the exponent -/

section Zpow

variable {ℓ : ℕ} [NeZero ℓ]

/-- **A power of an element killed by the exponent is read off the residue of the exponent.** -/
theorem zpow_eq_pow_val {M : Type*} [Group M] {c : M} (hc : c ^ ℓ = 1) (n : ℤ) :
    c ^ n = c ^ ((n : ZMod ℓ)).val := by
  have h1 : (((((n : ZMod ℓ)).val : ℤ)) : ZMod ℓ) = ((n : ℤ) : ZMod ℓ) := by
    rw [Int.cast_natCast, ZMod.natCast_rightInverse]
  have h0 : ((ℓ : ℤ)) ∣ ((((n : ZMod ℓ)).val : ℤ) - n) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).1 (by rw [Int.cast_sub, h1, sub_self])
  obtain ⟨j, hj⟩ := h0
  have hval : ((((n : ZMod ℓ)).val : ℤ)) = n + (ℓ : ℤ) * j := by omega
  rw [← zpow_natCast c ((n : ZMod ℓ)).val, hval, zpow_add, zpow_mul, zpow_natCast c ℓ, hc,
    one_zpow, mul_one]

end Zpow

/-! ### The valuation of a presented tensor -/

section Val

variable {Q : Type*} [Group Q] {A : Type*} [CommGroup A] [MulDistribMulAction Q A]
variable (C : Type*) [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type*} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ))

/-- **The valuation of a presented tensor is the product of the powers of the coefficient family by
the orders of the radicands.** -/
theorem tensorVal_sum_tmul {T : Type*} [Fintype T] (z : T → A) (b : T → C) (x : X) :
    tensorVal C g (∑ q, Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (b q)) x
      = Additive.ofMul (∏ q, b q ^ (g (Additive.ofMul (z q)) x)) := by
  rw [map_sum, Finsupp.finset_sum_apply, _root_.ofMul_prod]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [tensorVal_tmul_apply]
  exact (_root_.ofMul_zpow _ _).symm

end Val

/-! ### The prescription read off the valuation -/

section Prescribe

variable {ℓ : ℕ} [NeZero ℓ] {K : Type} [Field K] [NumberField K]
variable (T : Set (HeightOneSpectrum (𝓞 K)))
variable [DecidableEq {v : HeightOneSpectrum (𝓞 K) // v ∉ T}]
variable (C : Type) [CommGroup C]

/-- **Prescribing the valuation of a presented tensor prescribes the product of powers the flat
prescription asks for**, the value of a unit at a place being minus its order there. -/
theorem prod_pow_placeValue_val_eq_of_tensorVal {S : Type*} [Fintype S] (hexp : ∀ c : C, c ^ ℓ = 1)
    (z : S → Kˣ) (b : S → C) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ T) (V : C)
    (hs : tensorVal C (ordFinsupp T) (∑ q, Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (b q))
      ⟨v, hv⟩ = Additive.ofMul V) :
    ∏ q, b q ^ ((placeValue v (z q) : ZMod ℓ)).val = V⁻¹ := by
  rw [tensorVal_sum_tmul C (ordFinsupp T) z b ⟨v, hv⟩] at hs
  have hs' : ∏ q, b q ^ (ordFinsupp T (Additive.ofMul (z q)) ⟨v, hv⟩) = V :=
    Additive.ofMul.injective hs
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hs', ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun q _ => ?_
  have hord : ordFinsupp T (Additive.ofMul (z q)) ⟨v, hv⟩ = -placeValue v (z q) := by
    rw [ordFinsupp_apply, placeValue_eq_neg_ord, neg_neg]
    rfl
  rw [hord, ← zpow_eq_pow_val (hexp (b q)), zpow_neg, mul_inv_cancel]

end Prescribe

end InverseGalois.Shafarevich

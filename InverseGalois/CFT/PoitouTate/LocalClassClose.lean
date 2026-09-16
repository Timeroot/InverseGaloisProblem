/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CharPlace
import InverseGalois.CFT.Local.UnitRootPower

/-!
# Units close to one are local powers

A unit of a number field congruent to one at a finite place is a power in the completion there, as
soon as the exponent is prime to the residue characteristic: the binomial series converges on the
units congruent to one, so those units are divisible by every exponent prime to the residue
characteristic.  Two units whose difference is smaller than either of them therefore have the same
local class.

## Main results

* `InverseGalois.CFT.localClassHom_eq_one_of_valuation_sub_one_lt`: a unit congruent to one at a
  place is a power in the completion there.
* `InverseGalois.CFT.localClassHom_eq_of_valuation_sub_lt`: **two units whose difference is smaller
  at a place than the second of them have the same local class there.**

## Tags

local class, power, unit filtration, number field, class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section Close

variable {K : Type} [Field K] [NumberField K] {n p e : ℕ} [NeZero n]
  {v : HeightOneSpectrum (𝓞 K)}

/-- **A unit congruent to one at a place is a power in the completion there**, for an exponent
prime to the residue characteristic. -/
theorem localClassHom_eq_one_of_valuation_sub_one_lt
    (h : HasResidueChar (v.adicCompletion K) p e) (hpn : ¬ p ∣ n) {a : Kˣ}
    (ha : v.valuation K ((a : K) - 1) < 1) : localClassHom v n a = 1 := by
  set A := v.adicCompletion K with hA
  set x : Aˣ := Units.map (algebraMap K A).toMonoidHom a with hx
  have hcoe : (x : A) - 1 = ((((a : K) - 1 : K)) : A) := by
    show algebraMap K A (a : K) - 1 = algebraMap K A ((a : K) - 1)
    rw [map_sub, map_one]
  have hx1 : Valued.v ((x : A) - 1) < 1 := by
    rw [hcoe, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v)]
    exact ha
  have hxv : Valued.v (x : A) = 1 := valued_eq_one_of_sub_one_lt_one hx1
  obtain ⟨y, hy⟩ := exists_pow_eq_of_valued_sub_lt_one h (NeZero.ne n) hpn (b := 1) hxv
    (by simpa using hx1)
  refine (localClassHom_eq_one_iff_exists_pow v a).2 ⟨(y : A), ?_⟩
  rw [← Units.val_pow_eq_pow_val, hy]
  rfl

/-- **Two units whose difference at a place is smaller than the second of them have the same local
class there**, for an exponent prime to the residue characteristic.  Their quotient is congruent to
one, hence a power in the completion. -/
theorem localClassHom_eq_of_valuation_sub_lt (h : HasResidueChar (v.adicCompletion K) p e)
    (hpn : ¬ p ∣ n) {a b : Kˣ}
    (hab : v.valuation K ((a : K) - (b : K)) < v.valuation K (b : K)) :
    localClassHom v n a = localClassHom v n b := by
  have hbne : ((b : Kˣ) : K) ≠ 0 := b.ne_zero
  have hbpos : 0 < v.valuation K (b : K) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hbne)
  have hdiv : ((a * b⁻¹ : Kˣ) : K) - 1 = ((a : K) - (b : K)) / (b : K) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hquot : localClassHom v n (a * b⁻¹) = 1 := by
    refine localClassHom_eq_one_of_valuation_sub_one_lt h hpn ?_
    rw [hdiv, map_div₀]
    exact (div_lt_one₀ hbpos).2 hab
  rw [_root_.map_mul, _root_.map_inv] at hquot
  exact mul_inv_eq_one.1 hquot

end Close

end InverseGalois.CFT

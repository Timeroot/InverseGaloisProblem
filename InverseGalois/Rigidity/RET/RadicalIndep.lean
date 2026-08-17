/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.RatFuncConstants

/-!
# Products of linear factors in a rational function field

Fix a field `F` and a finite family `rt : ι → F` of **distinct** points.  This file studies the
group homomorphism

`Φ e = ∏ j (T - rt j) ^ e j : (ι → ℤ) → F(T)ˣ`

sending an integer exponent vector to the corresponding product of linear factors, taken with
integer (so possibly negative) exponents inside `F(T)`.

Two facts are recorded.  First, `Φ` is a homomorphism out of the additive group of exponent
vectors, compatible with finite products and with integer powers.  Second — the reason the
construction is useful — the exponents can be read back off from root multiplicities, so `Φ` is
**injective**, and more precisely a value `Φ E` is an `n`-th power in `F(T)` exactly when every
exponent `E j` is divisible by `n`.

The divisibility statement is the engine behind multiplicative independence of Kummer radicands:
several products of linear factors with disjoint supports are independent modulo `n`-th powers as
soon as the linear factors involved are pairwise distinct.
-/

open Polynomial

namespace Rigidity.RET

noncomputable section

attribute [local instance] Polynomial.algebra

open scoped RatFunc

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-! ### The exponent-vector homomorphism -/

/-- The linear polynomial `T - r`, as an element of `F(T)`. -/
def linF (r : F) : RatFunc F := algebraMap F[X] (RatFunc F) (X - C r)

theorem linF_ne_zero (r : F) : linF r ≠ 0 := fun h =>
  X_sub_C_ne_zero r (IsFractionRing.injective F[X] (RatFunc F) (by rw [map_zero]; exact h))

/-- **The exponent-vector homomorphism** `Φ e = ∏ (T - rt j) ^ e j`. -/
def phiF (rt : ι → F) (e : ι → ℤ) : RatFunc F := ∏ j, linF (rt j) ^ e j

variable (rt : ι → F)

theorem phiF_ne_zero (e : ι → ℤ) : phiF rt e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (linF_ne_zero (rt j))

theorem phiF_congr {e₁ e₂ : ι → ℤ} (h : ∀ j, e₁ j = e₂ j) : phiF rt e₁ = phiF rt e₂ :=
  Finset.prod_congr rfl fun j _ => by rw [h j]

theorem phiF_zero : phiF rt (fun _ => 0) = 1 :=
  Finset.prod_eq_one fun _ _ => zpow_zero _

theorem phiF_add (e₁ e₂ : ι → ℤ) :
    phiF rt (fun j => e₁ j + e₂ j) = phiF rt e₁ * phiF rt e₂ := by
  rw [phiF, phiF, phiF, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (linF_ne_zero (rt j)) _ _

theorem phiF_zpow (e : ι → ℤ) (m : ℤ) : phiF rt e ^ m = phiF rt (fun j => m * e j) := by
  rw [phiF, phiF, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun j _ => by rw [← zpow_mul, mul_comm]

theorem phiF_prod {κ : Type*} (s : Finset κ) (e : κ → ι → ℤ) :
    ∏ i ∈ s, phiF rt (e i) = phiF rt (fun j => ∑ i ∈ s, e i j) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact (phiF_zero rt).symm
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, ih, ← phiF_add]
      exact phiF_congr rt fun j => by rw [Finset.sum_insert hi]

/-- `Φ` of a vector of natural numbers is the image of an honest polynomial. -/
theorem phiF_natCast (A : ι → ℕ) :
    phiF rt (fun j => (A j : ℤ)) = algebraMap F[X] (RatFunc F) (∏ j, (X - C (rt j)) ^ A j) := by
  rw [phiF, map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [map_pow, zpow_natCast]; rfl

omit [Fintype ι] in
/-- Every integer exponent vector is a difference of two natural ones. -/
theorem exists_natCast_sub (e : ι → ℤ) :
    ∃ A B : ι → ℕ, ∀ j, (A j : ℤ) - (B j : ℤ) = e j :=
  ⟨fun j => (e j).toNat, fun j => (-(e j)).toNat, fun j => by
    show ((e j).toNat : ℤ) - ((-(e j)).toNat : ℤ) = e j
    omega⟩

/-! ### Base change -/

section BaseChange

variable {F' : Type*} [Field F'] [Algebra F F']

theorem algebraMap_linF (r : F) :
    algebraMap (RatFunc F) (RatFunc F') (linF r) = linF (algebraMap F F' r) := by
  rw [linF, linF, algebraMap_ratFunc_ratFunc, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C]

/-- Extending the constants commutes with the exponent-vector homomorphism. -/
theorem algebraMap_phiF (e : ι → ℤ) :
    algebraMap (RatFunc F) (RatFunc F') (phiF rt e)
      = phiF (fun j => algebraMap F F' (rt j)) e := by
  rw [phiF, phiF, map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [map_zpow₀, algebraMap_linF]

end BaseChange

/-! ### Reading the exponents off from root multiplicities -/

variable [DecidableEq ι] (hrt : Function.Injective rt)
include hrt

/-- **`Φ` is injective**: the exponents are recovered as root multiplicities. -/
theorem eq_zero_of_phiF_eq_one {e : ι → ℤ} (he : phiF rt e = 1) (j : ι) : e j = 0 := by
  obtain ⟨A, B, hAB⟩ := exists_natCast_sub e
  have hphi : phiF rt (fun j => (A j : ℤ)) = phiF rt (fun j => (B j : ℤ)) := by
    have hfun : (fun j => (A j : ℤ)) = fun j => e j + (B j : ℤ) :=
      funext fun j => by have := hAB j; omega
    rw [hfun, phiF_add, he, one_mul]
  have hpoly : (∏ j, (X - C (rt j)) ^ A j) = ∏ j, (X - C (rt j)) ^ B j :=
    IsFractionRing.injective F[X] (RatFunc F)
      (by rw [← phiF_natCast, ← phiF_natCast]; exact hphi)
  have hmul : (∏ j, (X - C (rt j)) ^ A j).rootMultiplicity (rt j)
      = (∏ j, (X - C (rt j)) ^ B j).rootMultiplicity (rt j) := by rw [hpoly]
  rw [rootMultiplicity_prod_pow _ hrt, rootMultiplicity_prod_pow _ hrt] at hmul
  have := hAB j
  omega

/-- **An `n`-th power pins the exponents down modulo `n`.** -/
theorem dvd_of_pow_eq_phiF {n : ℕ} (e : ι → ℤ) {y : RatFunc F} (hy : y ≠ 0)
    (h : y ^ n = phiF rt e) (j : ι) : (n : ℤ) ∣ e j := by
  obtain ⟨A, B, hAB⟩ := exists_natCast_sub e
  have hkey : y ^ n * phiF rt (fun j => (B j : ℤ)) = phiF rt (fun j => (A j : ℤ)) := by
    rw [h, ← phiF_add]
    exact phiF_congr rt fun j => by have := hAB j; omega
  have hnum0 : y.num ≠ 0 := RatFunc.num_ne_zero hy
  have hden0 : y.denom ≠ 0 := RatFunc.denom_ne_zero y
  have hnum : y * algebraMap F[X] (RatFunc F) y.denom = algebraMap F[X] (RatFunc F) y.num := by
    have hd : algebraMap F[X] (RatFunc F) y.denom ≠ 0 := fun hc =>
      hden0 (IsFractionRing.injective F[X] (RatFunc F) (by rw [map_zero]; exact hc))
    rw [eq_comm, ← div_eq_iff hd]
    exact RatFunc.num_div_denom y
  have hpolyeq : y.num ^ n * (∏ j, (X - C (rt j)) ^ B j)
      = (∏ j, (X - C (rt j)) ^ A j) * y.denom ^ n := by
    refine IsFractionRing.injective F[X] (RatFunc F) ?_
    rw [map_mul, map_mul, map_pow, map_pow, ← phiF_natCast, ← phiF_natCast, ← hnum, mul_pow,
      mul_right_comm, hkey]
  have hne1 : y.num ^ n * (∏ j, (X - C (rt j)) ^ B j) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hnum0) (prod_pow_ne_zero _ _)
  have hne2 : (∏ j, (X - C (rt j)) ^ A j) * y.denom ^ n ≠ 0 :=
    mul_ne_zero (prod_pow_ne_zero _ _) (pow_ne_zero _ hden0)
  have heq : n * y.num.rootMultiplicity (rt j) + B j
      = A j + n * y.denom.rootMultiplicity (rt j) := by
    have hb : (y.num ^ n * (∏ j, (X - C (rt j)) ^ B j)).rootMultiplicity (rt j)
        = ((∏ j, (X - C (rt j)) ^ A j) * y.denom ^ n).rootMultiplicity (rt j) := by rw [hpolyeq]
    rwa [rootMultiplicity_mul hne1, rootMultiplicity_mul hne2, rootMultiplicity_pow hnum0,
      rootMultiplicity_pow hden0, rootMultiplicity_prod_pow _ hrt,
      rootMultiplicity_prod_pow _ hrt] at hb
  have hcast : (n : ℤ) * (y.num.rootMultiplicity (rt j) : ℤ) + (B j : ℤ)
      = (A j : ℤ) + (n : ℤ) * (y.denom.rootMultiplicity (rt j) : ℤ) := by exact_mod_cast heq
  refine ⟨(y.num.rootMultiplicity (rt j) : ℤ) - (y.denom.rootMultiplicity (rt j) : ℤ), ?_⟩
  rw [← hAB j]
  linear_combination -hcast

end

end Rigidity.RET

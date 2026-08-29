/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.PowNeighbourhood
import InverseGalois.CFT.Local.UnitRootPower

/-!
# Roots of a unit congruent to one are again congruent to one

A unit of a complete valued field which is congruent to one to sufficient accuracy is an `n`-th
power, and the root produced by the exponential is itself congruent to one: it is the exponential
of a small element.  Recording that extra information turns the statement into one about the unit
filtration alone, and the Bezout trick which removes the accuracy requirement for an exponent prime
to the residue characteristic keeps it, because a step of the filtration is a group.

So for an exponent prime to the residue characteristic **raising to the `n`-th power is a bijection
of the units congruent to one**: it is onto by the above, and one to one because a unit congruent to
one whose order is prime to the residue characteristic is trivial.  This is the statement that lets
a root of unity be chosen inside a prescribed class modulo the maximal ideal.

## Main results

* `InverseGalois.CFT.exists_mem_unitFiltration_pow_eq`: a unit congruent to one to sufficient
  accuracy is the `n`-th power of a unit congruent to one.
* `InverseGalois.CFT.exists_mem_unitFiltration_zero_pow_eq`: **a unit congruent to one is the
  `n`-th power of a unit congruent to one**, for an exponent prime to the residue characteristic.
* `InverseGalois.CFT.pow_bijective_unitFiltration_zero`: **raising to an exponent prime to the
  residue characteristic is a bijection of the units congruent to one.**

## Tags

valued field, unit filtration, power, root, residue characteristic
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] [CompleteSpace A] {p e : ℕ}

/-! ### Roots inside the filtration -/

/-- **A unit congruent to one to sufficient accuracy is the `n`-th power of a unit congruent to
one.**  The root is the exponential of a small element, so it lies in the step of the filtration on
which the exponential is defined. -/
theorem exists_mem_unitFiltration_pow_eq (h : HasResidueChar A p e) {n : ℕ} (hn : n ≠ 0)
    {m : ℕ} (hvn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) {u : Aˣ}
    (hu : u ∈ unitFiltration A (e + m)) : ∃ y ∈ unitFiltration A e, y ^ n = u := by
  have hp : 1 < (p : ℤ) := h.one_lt_p
  have hL : (e : ℤ) < (((e + m : ℕ) : ℤ) + 1) * ((p : ℤ) - 1) :=
    lt_mul_pred_of_le hp (Nat.le_add_right e m)
  have hj : (e : ℤ) < (((e : ℕ) : ℤ) + 1) * ((p : ℤ) - 1) := lt_mul_pred_of_le hp le_rfl
  obtain ⟨X, hX⟩ := padicExpHom_surjective h hL ⟨Additive.ofMul u, hu⟩
  have hXu : padicExp ((X : A)) = (u : A) := by
    rw [← coe_padicExpHom h hL X, hX]
    rfl
  have hn0 : ((n : ℕ) : A) ≠ 0 := h.natCast_ne_zero hn
  have hXmem : Valued.v (X : A) ≤ WithZero.exp (-(((e + m : ℕ) : ℤ) + 1)) :=
    mem_valAddSubgroup.mp X.2
  have hy : (X : A) / ((n : ℕ) : A) ∈ valAddSubgroup A (((e : ℕ) : ℤ) + 1) := by
    rw [mem_valAddSubgroup, map_div₀, hvn, div_eq_mul_inv, ← WithZero.exp_neg, neg_neg]
    calc Valued.v (X : A) * WithZero.exp ((m : ℤ))
        ≤ WithZero.exp (-(((e + m : ℕ) : ℤ) + 1)) * WithZero.exp ((m : ℤ)) :=
          mul_le_mul_left hXmem _
      _ = WithZero.exp (-(((e : ℕ) : ℤ) + 1)) := by
          rw [← WithZero.exp_add]
          congr 1
          push_cast
          ring
  obtain ⟨Y, hYval⟩ : ∃ Y : ↥(valAddSubgroup A (((e : ℕ) : ℤ) + 1)),
      (Y : A) = (X : A) / ((n : ℕ) : A) := ⟨⟨_, hy⟩, rfl⟩
  have hnY : ((n • Y : ↥(valAddSubgroup A (((e : ℕ) : ℤ) + 1))) : A) = (X : A) := by
    have hcoe : ((n • Y : ↥(valAddSubgroup A (((e : ℕ) : ℤ) + 1))) : A) = n • (Y : A) := rfl
    rw [hcoe, hYval, nsmul_eq_mul]
    field_simp
  have hmap : padicExpHom h hj (n • Y) = n • padicExpHom h hj Y := map_nsmul _ _ _
  have hcong := congrArg (fun w : ↥(unitFiltrationAdd A e) =>
    ((Additive.toMul (w : Additive Aˣ) : Aˣ) : A)) hmap
  dsimp only at hcong
  rw [coe_padicExpHom, coe_nsmul_unitFiltrationAdd, coe_padicExpHom, hnY, hYval, hXu] at hcong
  refine ⟨Additive.toMul ((padicExpHom h hj Y : Additive Aˣ)), (padicExpHom h hj Y).2,
    Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, coe_padicExpHom, hYval]
  exact hcong.symm

/-- **A unit congruent to one is the `n`-th power of a unit congruent to one**, for an exponent
prime to the residue characteristic.  A high enough power with exponent a power of the residue
characteristic is such a power, and the two exponents are coprime. -/
theorem exists_mem_unitFiltration_zero_pow_eq (h : HasResidueChar A p e) {n : ℕ} (hn : n ≠ 0)
    (hpn : ¬ p ∣ n) {c : Aˣ} (hc : c ∈ unitFiltration A 0) :
    ∃ y ∈ unitFiltration A 0, y ^ n = c := by
  have hp := h.prime
  have hvn : Valued.v ((n : ℕ) : A) = WithZero.exp (-((0 : ℕ) : ℤ)) := by
    rw [h.valued_natCast hn, padicValNat.eq_zero_of_not_dvd hpn]
    norm_num
  have hmem : c ^ p ^ e ∈ unitFiltration A (e + 0) := by
    simpa using pow_pow_residueChar_mem_unitFiltration h hc e
  obtain ⟨z, hzmem, hzn⟩ := exists_mem_unitFiltration_pow_eq h hn hvn hmem
  have hz0 : z ∈ unitFiltration A 0 := unitFiltration_le_unitFiltration (Nat.zero_le e) hzmem
  have hcop : Nat.Coprime n (p ^ e) :=
    (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm).pow_right e
  have hbez : (n : ℤ) * Nat.gcdA n (p ^ e) + ((p : ℤ) ^ e) * Nat.gcdB n (p ^ e) = 1 := by
    have hg := Nat.gcd_eq_gcd_ab n (p ^ e)
    rw [Nat.Coprime.gcd_eq_one hcop] at hg
    push_cast at hg ⊢
    omega
  refine ⟨c ^ Nat.gcdA n (p ^ e) * z ^ Nat.gcdB n (p ^ e),
    Subgroup.mul_mem _ (Subgroup.zpow_mem _ hc _) (Subgroup.zpow_mem _ hz0 _), ?_⟩
  have hstep : (c ^ Nat.gcdA n (p ^ e) * z ^ Nat.gcdB n (p ^ e)) ^ n
      = c ^ ((n : ℤ) * Nat.gcdA n (p ^ e)) * (z ^ n) ^ Nat.gcdB n (p ^ e) := by
    rw [mul_pow, ← zpow_natCast (c ^ Nat.gcdA n (p ^ e)) n, ← zpow_mul,
      ← zpow_natCast (z ^ Nat.gcdB n (p ^ e)) n, ← zpow_mul, ← zpow_natCast z n, ← zpow_mul]
    ring_nf
  rw [hstep, hzn, ← zpow_natCast c (p ^ e), ← zpow_mul, ← zpow_add]
  push_cast
  rw [hbez, zpow_one]

/-! ### The power map on the units congruent to one -/

/-- **Raising to an exponent prime to the residue characteristic is a bijection of the units
congruent to one.** -/
theorem pow_bijective_unitFiltration_zero (h : HasResidueChar A p e) {n : ℕ} (hn : n ≠ 0)
    (hpn : ¬ p ∣ n) :
    Function.Bijective fun y : ↥(unitFiltration A 0) => y ^ n := by
  constructor
  · intro y₁ y₂ hy
    have hquot : ((y₁ * y₂⁻¹ : ↥(unitFiltration A 0)) : Aˣ) ^ n = 1 := by
      have h₁ : (y₁ : Aˣ) ^ n = (y₂ : Aˣ) ^ n := congrArg Subtype.val hy
      push_cast
      rw [mul_pow, inv_pow, h₁, mul_inv_cancel]
    have hmem : ((y₁ * y₂⁻¹ : ↥(unitFiltration A 0)) : Aˣ) ∈ unitFiltration A 0 :=
      (y₁ * y₂⁻¹).2
    have := eq_one_of_pow_eq_one_of_mem_unitFiltration h hmem hpn hquot
    have hone : (y₁ * y₂⁻¹ : ↥(unitFiltration A 0)) = 1 := Subtype.ext this
    exact mul_inv_eq_one.mp hone
  · rintro ⟨c, hc⟩
    obtain ⟨y, hymem, hy⟩ := exists_mem_unitFiltration_zero_pow_eq h hn hpn hc
    exact ⟨⟨y, hymem⟩, Subtype.ext hy⟩

end InverseGalois.CFT

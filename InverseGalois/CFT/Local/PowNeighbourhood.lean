/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.ExpEquiv

/-!
# The `n`-th powers of a complete valued field surround one

In a complete valued field of residue characteristic `p` the exponential is an isomorphism from a
deep enough step of the additive filtration onto the corresponding step of the unit filtration.
Dividing by `n` inside the additive filtration and transporting the result through the exponential
turns multiplication by `n` into raising to the `n`-th power, so a unit congruent to one to
sufficiently high accuracy is an `n`-th power.

The accuracy needed is governed by two numbers: the valuation `e` of the residue characteristic,
which controls where the exponential converges, and the valuation `m` of `n`, which measures how
much dividing by `n` costs.  A unit congruent to one modulo the `(e + m + 1)`-st step of the
additive filtration is an `n`-th power.

## Main results

* `InverseGalois.CFT.exists_pow_eq_of_mem_unitFiltration`: **a unit congruent to one to sufficient
  accuracy is an `n`-th power.**
* `InverseGalois.CFT.unitFiltration_le_range_powMonoidHom`: a deep enough step of the unit
  filtration is contained in the `n`-th powers.
* `InverseGalois.CFT.exists_pow_eq_of_valued_sub_one_le`: **the `n`-th powers contain every element
  close enough to one.**

## Tags

valued field, exponential, unit filtration, power, neighbourhood of one
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] [CompleteSpace A] {p e : ℕ}

/-! ### Convergence of the exponential above the residue level -/

/-- Every step of the additive filtration at or beyond the valuation of the residue characteristic
is deep enough for the exponential to converge. -/
theorem lt_mul_pred_of_le (hp : 1 < (p : ℤ)) {k : ℕ} (hk : e ≤ k) :
    (e : ℤ) < ((k : ℤ) + 1) * ((p : ℤ) - 1) := by
  have hke : (e : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  calc (e : ℤ) < (k : ℤ) + 1 := by omega
    _ = ((k : ℤ) + 1) * 1 := (mul_one _).symm
    _ ≤ ((k : ℤ) + 1) * ((p : ℤ) - 1) := mul_le_mul_of_nonneg_left (by omega) (by omega)

/-! ### Raising to the `n`-th power inside the unit filtration -/

omit [CompleteSpace A] in
/-- Multiplying in the additive form of the unit group is raising to a power. -/
theorem coe_nsmul_unitFiltrationAdd {i n : ℕ} (w : ↥(unitFiltrationAdd A i)) :
    ((Additive.toMul ((n • w : ↥(unitFiltrationAdd A i)) : Additive Aˣ) : Aˣ) : A)
      = ((Additive.toMul (w : Additive Aˣ) : Aˣ) : A) ^ n := by
  simp

/-- **A unit congruent to one to sufficient accuracy is an `n`-th power.**  The accuracy is
measured by the valuation `e` of the residue characteristic together with the valuation `m` of
`n`. -/
theorem exists_pow_eq_of_mem_unitFiltration (h : HasResidueChar A p e) {n : ℕ} (hn : n ≠ 0)
    {m : ℕ} (hvn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) {u : Aˣ}
    (hu : u ∈ unitFiltration A (e + m)) : ∃ y : A, y ^ n = (u : A) := by
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
  refine ⟨padicExp ((X : A) / ((n : ℕ) : A)), ?_⟩
  have hmap : padicExpHom h hj (n • Y) = n • padicExpHom h hj Y := map_nsmul _ _ _
  have hcong := congrArg (fun w : ↥(unitFiltrationAdd A e) =>
    ((Additive.toMul (w : Additive Aˣ) : Aˣ) : A)) hmap
  dsimp only at hcong
  rw [coe_padicExpHom, coe_nsmul_unitFiltrationAdd, coe_padicExpHom, hnY, hYval, hXu] at hcong
  exact hcong.symm

/-- A deep enough step of the unit filtration is contained in the `n`-th powers. -/
theorem unitFiltration_le_range_powMonoidHom (h : HasResidueChar A p e) {n : ℕ} (hn : n ≠ 0)
    {m : ℕ} (hvn : Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ))) :
    unitFiltration A (e + m) ≤ (powMonoidHom n : Aˣ →* Aˣ).range := by
  intro u hu
  obtain ⟨y, hy⟩ := exists_pow_eq_of_mem_unitFiltration h hn hvn hu
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hy
    exact u.ne_zero hy.symm
  exact ⟨Units.mk0 y hy0, Units.ext (by rw [show ((powMonoidHom n (Units.mk0 y hy0) : Aˣ) : A)
    = y ^ n from rfl, hy])⟩

/-- **The `n`-th powers contain every element close enough to one.** -/
theorem exists_pow_eq_of_valued_sub_one_le (h : HasResidueChar A p e) {n : ℕ} (hn : n ≠ 0) :
    ∃ i : ℕ, ∀ u : A, Valued.v (u - 1) ≤ WithZero.exp (-(i : ℤ)) → ∃ y : A, y ^ n = u := by
  obtain ⟨m, hvn⟩ : ∃ m : ℕ, Valued.v ((n : ℕ) : A) = WithZero.exp (-(m : ℤ)) :=
    ⟨e * padicValNat p n, by
      rw [h.valued_natCast hn]
      congr 1⟩
  refine ⟨e + m + 1, fun u hu => ?_⟩
  have hlt : Valued.v (u - 1) < 1 := lt_one_of_le_exp_neg (by omega) hu
  have hu1 : Valued.v u = 1 := valued_eq_one_of_sub_one_lt_one hlt
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu1
    exact zero_ne_one hu1
  have hmem : Units.mk0 u hu0 ∈ unitFiltration A (e + m) := by
    rw [mem_unitFiltration]
    refine le_trans (le_of_eq (congrArg Valued.v (by rw [Units.val_mk0]))) ?_
    refine le_trans hu (WithZero.exp_le_exp.mpr ?_)
    push_cast
    omega
  exact exists_pow_eq_of_mem_unitFiltration h hn hvn hmem

end InverseGalois.CFT

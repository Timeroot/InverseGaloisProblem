/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.Exp
import InverseGalois.CFT.Local.UnitFiltration

/-!
# The exponential exhausts a small enough neighbourhood of one

A unit congruent to one modulo a small enough power of the maximal ideal is an exponential.  One
divides the unit by the exponential of its difference from one, which gains one digit; iterating
produces a sequence of increments whose sum converges, and the exponential of that sum is the
original unit, because the two differ by less than every power of the maximal ideal.

## Main definitions

* `InverseGalois.CFT.expApprox`: the successive approximations to a unit.
* `InverseGalois.CFT.expIncr`, `InverseGalois.CFT.expPartial`: the increments and their partial
  sums.

## Main results

* `InverseGalois.CFT.valued_expApprox_sub_one`: each approximation gains one digit.
* `InverseGalois.CFT.exists_padicExp_eq`: **every unit congruent to one modulo a small enough power
  of the maximal ideal is an exponential.**

## Tags

valued field, exponential, successive approximation, unit filtration
-/

namespace InverseGalois.CFT

open Filter Topology

open scoped WithZero

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {p e : ℕ}

/-! ### The successive approximations -/

/-- **The successive approximations to a unit**: at each stage one divides by the exponential of
the difference from one. -/
noncomputable def expApprox (u : A) : ℕ → A
  | 0 => u
  | n + 1 => expApprox u n * (padicExp (expApprox u n - 1))⁻¹

/-- **The increments of the successive approximations.** -/
noncomputable def expIncr (u : A) (n : ℕ) : A := expApprox u n - 1

/-- **The partial sums of the increments.** -/
noncomputable def expPartial (u : A) (n : ℕ) : A := ∑ m ∈ Finset.range n, expIncr u m

@[simp]
theorem expApprox_zero (u : A) : expApprox u 0 = u := rfl

theorem expApprox_succ (u : A) (n : ℕ) :
    expApprox u (n + 1) = expApprox u n * (padicExp (expIncr u n))⁻¹ := rfl

@[simp]
theorem expIncr_zero (u : A) : expIncr u 0 = u - 1 := rfl

@[simp]
theorem expPartial_zero (u : A) : expPartial u 0 = 0 := rfl

theorem expPartial_succ (u : A) (n : ℕ) :
    expPartial u (n + 1) = expPartial u n + expIncr u n :=
  Finset.sum_range_succ _ n

variable [CompleteSpace A]

/-- **Dividing by an exponential gains one digit.** -/
theorem valued_mul_inv_padicExp_sub_one (h : HasResidueChar A p e) {j : ℤ}
    (hj : (e : ℤ) < j * ((p : ℤ) - 1)) {a : A} (ha : Valued.v (a - 1) ≤ WithZero.exp (-j)) :
    Valued.v (a * (padicExp (a - 1))⁻¹ - 1) ≤ WithZero.exp (-(j + 1)) := by
  have hexp : Valued.v (padicExp (a - 1)) = 1 := valued_padicExp h ha hj
  have hne : padicExp (a - 1) ≠ 0 := fun hz => by
    rw [hz, map_zero] at hexp
    exact zero_ne_one hexp
  have hstep : a * (padicExp (a - 1))⁻¹ - 1
      = -((padicExp (a - 1) - (1 + (a - 1))) * (padicExp (a - 1))⁻¹) := by
    field_simp
    ring
  rw [hstep, Valuation.map_neg, map_mul, map_inv₀, hexp, inv_one, mul_one]
  exact valued_padicExp_sub_one_add h ha hj

/-- **Each successive approximation gains one digit.** -/
theorem valued_expApprox_sub_one (h : HasResidueChar A p e) {j : ℤ}
    (hj : (e : ℤ) < j * ((p : ℤ) - 1)) {u : A} (hu : Valued.v (u - 1) ≤ WithZero.exp (-j))
    (n : ℕ) : Valued.v (expIncr u n) ≤ WithZero.exp (-(j + n)) := by
  have hp1 : (0 : ℤ) < (p : ℤ) - 1 := by have := h.one_lt_p; omega
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    have hjn : (e : ℤ) < (j + n) * ((p : ℤ) - 1) := by nlinarith [Int.natCast_nonneg n]
    have hcast : -(j + ((n + 1 : ℕ) : ℤ)) = -((j + (n : ℤ)) + 1) := by push_cast; ring
    rw [hcast]
    have := valued_mul_inv_padicExp_sub_one h hjn ih
    rwa [show expApprox u n * (padicExp (expApprox u n - 1))⁻¹ - 1 = expIncr u (n + 1) from rfl]
      at this

/-! ### The limit -/

/-- The increments are summable. -/
theorem summable_expIncr (h : HasResidueChar A p e) {j : ℤ}
    (hj : (e : ℤ) < j * ((p : ℤ) - 1)) {u : A} (hu : Valued.v (u - 1) ≤ WithZero.exp (-j)) :
    Summable (expIncr u) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_zero_of_valued fun N => ?_)
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨(N - j).toNat, fun n hn => ?_⟩
  refine le_trans (valued_expApprox_sub_one h hj hu n) (WithZero.exp_le_exp.mpr ?_)
  have : N - j ≤ ((N - j).toNat : ℤ) := Int.self_le_toNat _
  have hn' : (((N - j).toNat : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  omega

/-- The partial sums stay in the ball. -/
theorem valued_expPartial (h : HasResidueChar A p e) {j : ℤ}
    (hj : (e : ℤ) < j * ((p : ℤ) - 1)) {u : A} (hu : Valued.v (u - 1) ≤ WithZero.exp (-j))
    (n : ℕ) : Valued.v (expPartial u n) ≤ WithZero.exp (-j) := by
  have hmem : expPartial u n ∈ valAddSubgroup A j :=
    AddSubgroup.sum_mem _ fun m _ => mem_valAddSubgroup.mpr
      (le_trans (valued_expApprox_sub_one h hj hu m) (WithZero.exp_le_exp.mpr (by omega)))
  exact mem_valAddSubgroup.mp hmem

/-- The approximation and the exponential of the partial sum recover the unit. -/
theorem expApprox_mul_padicExp_expPartial (h : HasResidueChar A p e) {j : ℤ}
    (hj : (e : ℤ) < j * ((p : ℤ) - 1)) {u : A} (hu : Valued.v (u - 1) ≤ WithZero.exp (-j))
    (n : ℕ) : expApprox u n * padicExp (expPartial u n) = u := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hy : Valued.v (expIncr u n) ≤ WithZero.exp (-j) :=
      le_trans (valued_expApprox_sub_one h hj hu n) (WithZero.exp_le_exp.mpr (by omega))
    have hne : padicExp (expIncr u n) ≠ 0 := fun hz => by
      have := valued_padicExp h hy hj
      rw [hz, map_zero] at this
      exact zero_ne_one this
    rw [expPartial_succ, padicExp_add h (valued_expPartial h hj hu n) hy hj, expApprox_succ,
      show expApprox u n * (padicExp (expIncr u n))⁻¹
          * (padicExp (expPartial u n) * padicExp (expIncr u n))
        = expApprox u n * padicExp (expPartial u n)
          * ((padicExp (expIncr u n))⁻¹ * padicExp (expIncr u n)) by ring,
      inv_mul_cancel₀ hne, mul_one]
    exact ih

/-- **Every unit congruent to one modulo a small enough power of the maximal ideal is an
exponential.** -/
theorem exists_padicExp_eq (h : HasResidueChar A p e) {j : ℤ}
    (hj : (e : ℤ) < j * ((p : ℤ) - 1)) {u : A} (hu : Valued.v (u - 1) ≤ WithZero.exp (-j)) :
    ∃ x : A, Valued.v x ≤ WithZero.exp (-j) ∧ padicExp x = u := by
  have hy : ∀ n : ℕ, Valued.v (expIncr u n) ≤ WithZero.exp (-(j + n)) :=
    valued_expApprox_sub_one h hj hu
  have hyj : ∀ n : ℕ, Valued.v (expIncr u n) ≤ WithZero.exp (-j) := fun n =>
    le_trans (hy n) (WithZero.exp_le_exp.mpr (by omega))
  have hsum : HasSum (expIncr u) (∑' n, expIncr u n) := (summable_expIncr h hj hu).hasSum
  refine ⟨∑' n, expIncr u n, valued_le_of_hasSum hsum hyj, ?_⟩
  have hxv : Valued.v (∑' n, expIncr u n) ≤ WithZero.exp (-j) := valued_le_of_hasSum hsum hyj
  have hfinal : ∀ n : ℕ,
      Valued.v (u - padicExp (∑' n, expIncr u n)) ≤ WithZero.exp (-(j + n)) := by
    intro n
    have h1 : HasSum (fun m => expIncr u (m + n)) (∑' n, expIncr u n - expPartial u n) :=
      (hasSum_nat_add_iff' n).mpr hsum
    have h2 : Valued.v (∑' n, expIncr u n - expPartial u n) ≤ WithZero.exp (-(j + n)) :=
      valued_le_of_hasSum h1 fun m =>
        le_trans (hy (m + n)) (WithZero.exp_le_exp.mpr (by omega))
    have h4 : Valued.v (padicExp (expPartial u n) - padicExp (∑' n, expIncr u n))
        ≤ WithZero.exp (-(j + n)) := by
      rw [valued_padicExp_sub_padicExp h (valued_expPartial h hj hu n) hxv hj,
        Valuation.map_sub_swap]
      exact h2
    have hsplit : u - padicExp (∑' n, expIncr u n)
        = expIncr u n * padicExp (expPartial u n)
          + (padicExp (expPartial u n) - padicExp (∑' n, expIncr u n)) := by
      have heq := expApprox_mul_padicExp_expPartial h hj hu n
      simp only [expIncr]
      linear_combination -heq
    rw [hsplit]
    refine le_trans (Valuation.map_add Valued.v _ _) (max_le ?_ h4)
    rw [map_mul, valued_padicExp h (valued_expPartial h hj hu n) hj, mul_one]
    exact hy n
  by_contra hne
  have hsub : u - padicExp (∑' n, expIncr u n) ≠ 0 := fun hz => hne (by
    have : u = padicExp (∑' n, expIncr u n) := by linear_combination hz
    exact this.symm)
  have h0 : Valued.v (u - padicExp (∑' n, expIncr u n)) ≠ 0 := by simpa using hsub
  obtain ⟨d, hd⟩ : ∃ d : ℤ, Valued.v (u - padicExp (∑' n, expIncr u n)) = WithZero.exp (-d) :=
    ⟨-WithZero.log _, by rw [neg_neg, WithZero.exp_log h0]⟩
  have hbig := hfinal ((d - j).toNat + 1)
  rw [hd] at hbig
  have hle := WithZero.exp_le_exp.mp hbig
  have htoNat : d - j ≤ ((d - j).toNat : ℤ) := Int.self_le_toNat _
  have hcast : (((d - j).toNat + 1 : ℕ) : ℤ) = ((d - j).toNat : ℤ) + 1 := by push_cast; ring
  rw [hcast] at hle
  omega

end InverseGalois.CFT

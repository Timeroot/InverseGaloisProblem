/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.DivisionResidue

/-!
# The value group of a division algebra over a local field

A nonarchimedean local field has a uniformizer: the closed unit ball is compact and the open unit
ball is closed as well, so the absolute value attains a largest value below one, and that value is
not zero because the field is nontrivially normed.  The same argument inside a finite-dimensional
division algebra `D` over such a field, or rather the discreteness already established for the
absolute value of `D`, produces a uniformizer of `D`.

Once a uniformizer `ϖ` of `D` is fixed, the absolute values of the nonzero elements of `D` are
exactly the integer powers of the absolute value of `ϖ`: an element whose absolute value lies
between two consecutive powers can be divided by the appropriate power of `ϖ`, and what is left
has absolute value at most one and greater than that of `ϖ`, hence equal to one.  The absolute
value of a uniformizer of the base field is then a positive power `e` of that of `ϖ`, and `e` is at
most `n`, where `n ^ 2` is the dimension of `D`.

## Main definitions

* `InverseGalois.CFT.IsDivisionUniformizer`: a uniformizer of a division algebra.

## Main results

* `InverseGalois.CFT.exists_isNormUniformizer`: **a nonarchimedean local field has a uniformizer.**
* `InverseGalois.CFT.IsDivisionUniformizer.exists_zpow`: **the absolute values of the nonzero
  elements of `D` are the integer powers of that of a uniformizer.**
* `InverseGalois.CFT.IsDivisionUniformizer.exists_pow_eq_norm`: the absolute value of a uniformizer
  of the base field is a positive power of that of a uniformizer of `D`.
* `InverseGalois.CFT.IsDivisionUniformizer.ramification_le`: **that power is at most `n`.**

## Tags

division algebra, local field, value group, uniformizer, ramification
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u

open Module

namespace InverseGalois.CFT

/-! ### Powers of the absolute value -/

section Powers

variable {K D : Type u} [NormedField K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

omit [FiniteDimensional K D] in
theorem divisionNorm_pow (x : D) (m : ℕ) :
    divisionNorm K D (x ^ m) = divisionNorm K D x ^ m := by
  induction m with
  | zero => simp [divisionNorm_one]
  | succ k ih => rw [pow_succ, pow_succ, divisionNorm_mul, ih]

theorem divisionNorm_inv (x : D) : divisionNorm K D x⁻¹ = (divisionNorm K D x)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : divisionNorm K D (0 : D) = 0 := divisionNorm_eq_zero_iff.2 rfl
    rw [inv_zero, h0, inv_zero]
  · have h1 : divisionNorm K D x * divisionNorm K D x⁻¹ = 1 := by
      rw [← divisionNorm_mul, mul_inv_cancel₀ hx, divisionNorm_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm

theorem divisionNorm_zpow (x : D) (i : ℤ) :
    divisionNorm K D (x ^ i) = divisionNorm K D x ^ i := by
  cases i with
  | ofNat m => simpa using divisionNorm_pow x m
  | negSucc m => rw [zpow_negSucc, zpow_negSucc, divisionNorm_inv, divisionNorm_pow]

end Powers

/-! ### A uniformizer of the base field -/

section BaseUniformizer

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]

/-- **A nonarchimedean local field has a uniformizer.**  In an ultrametric space the open unit ball
is closed, so it is compact, and the absolute value attains a maximum on it; the maximum is not
zero because the field contains an element of absolute value strictly between zero and one. -/
theorem exists_isNormUniformizer : ∃ π : K, IsNormUniformizer π := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  have hnc : (0 : ℝ) < ‖c‖ := lt_trans zero_lt_one hc
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnc
    exact absurd hnc (lt_irrefl 0)
  have hc₀pos : 0 < ‖c⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hc0)
  have hprod : ‖c⁻¹‖ * ‖c‖ = 1 := by
    rw [← norm_mul, inv_mul_cancel₀ hc0, norm_one]
  have hc₀lt : ‖c⁻¹‖ < 1 := by nlinarith
  have hc₀mem : c⁻¹ ∈ Metric.ball (0 : K) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hc₀lt
  have hclosed : IsClosed (Metric.ball (0 : K) 1) := (IsUltrametricDist.isClopen_ball 0 1).isClosed
  have hcpt : IsCompact (Metric.ball (0 : K) 1) :=
    Metric.isCompact_of_isClosed_isBounded hclosed Metric.isBounded_ball
  obtain ⟨π, hπmem, hπmax⟩ := hcpt.exists_isMaxOn ⟨c⁻¹, hc₀mem⟩ continuous_norm.continuousOn
  rw [Metric.mem_ball, dist_zero_right] at hπmem
  refine ⟨π, ?_, hπmem, fun z hz => hπmax (by rwa [Metric.mem_ball, dist_zero_right])⟩
  intro h
  have hle : ‖c⁻¹‖ ≤ ‖π‖ := hπmax hc₀mem
  rw [h, norm_zero] at hle
  exact absurd (lt_of_lt_of_le hc₀pos hle) (lt_irrefl 0)

end BaseUniformizer

/-! ### A uniformizer of the division algebra -/

/-- A **uniformizer** of a division algebra over a nonarchimedean field: a nonzero element whose
absolute value is the largest one below one. -/
structure IsDivisionUniformizer (K D : Type u) [NormedField K] [DivisionRing D] [Algebra K D]
    (ϖ : D) : Prop where
  /-- A uniformizer is nonzero. -/
  ne_zero : ϖ ≠ 0
  /-- A uniformizer has absolute value less than one. -/
  norm_lt_one : divisionNorm K D ϖ < 1
  /-- No element of absolute value less than one exceeds a uniformizer. -/
  le_norm : ∀ x : D, divisionNorm K D x < 1 → divisionNorm K D x ≤ divisionNorm K D ϖ

section DivisionUniformizer

variable {K D : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

variable (K D) in
omit [IsUltrametricDist K] [ProperSpace K] in
/-- **A division algebra over a nonarchimedean local field has a uniformizer.** -/
theorem exists_isDivisionUniformizer [Algebra.IsCentral K D] {π : K} (hπ : IsNormUniformizer π)
    {n : ℕ} (hn : n * n = finrank K D) : ∃ ϖ : D, IsDivisionUniformizer K D ϖ := by
  obtain ⟨ϖ, h1, h2, h3⟩ := exists_isNormUniformizer_divisionNorm K D hπ hn
  exact ⟨ϖ, h1, h2, h3⟩

omit [IsUltrametricDist K] [ProperSpace K] in
theorem IsDivisionUniformizer.norm_pos {ϖ : D} (hϖ : IsDivisionUniformizer K D ϖ) :
    0 < divisionNorm K D ϖ :=
  lt_of_le_of_ne (divisionNorm_nonneg _) fun h =>
    hϖ.ne_zero (divisionNorm_eq_zero_iff.1 h.symm)

omit [IsUltrametricDist K] [ProperSpace K] in
/-- **The absolute values of the nonzero elements of a division algebra are the integer powers of
the absolute value of a uniformizer.**  An element whose absolute value lies between two
consecutive powers becomes, after division by the smaller power, an element of absolute value at
most one and greater than that of the uniformizer, hence of absolute value one. -/
theorem IsDivisionUniformizer.exists_zpow {ϖ : D} (hϖ : IsDivisionUniformizer K D ϖ) {x : D}
    (hx : x ≠ 0) : ∃ i : ℤ, divisionNorm K D x = divisionNorm K D ϖ ^ i := by
  set ρ : ℝ := divisionNorm K D ϖ with hρdef
  have hρpos : 0 < ρ := hϖ.norm_pos
  have hρ1 : ρ < 1 := hϖ.norm_lt_one
  have hxpos : 0 < divisionNorm K D x := divisionNorm_pos hx
  have hinv : 1 < ρ⁻¹ := (one_lt_inv₀ hρpos).2 hρ1
  obtain ⟨m, hm⟩ := exists_mem_Ioc_zpow hxpos hinv
  have hconv : ∀ k : ℤ, (ρ⁻¹) ^ k = ρ ^ (-k) := fun k => by rw [inv_zpow, zpow_neg]
  set i : ℤ := -m - 1 with hidef
  have hlow : ρ ^ (i + 1) < divisionNorm K D x := by
    have h := hm.1
    rw [hconv] at h
    have : -m = i + 1 := by omega
    rwa [this] at h
  have hhigh : divisionNorm K D x ≤ ρ ^ i := by
    have h := hm.2
    rw [hconv] at h
    have : -(m + 1) = i := by omega
    rwa [this] at h
  refine ⟨i, ?_⟩
  have hipos : (0 : ℝ) < ρ ^ i := zpow_pos hρpos i
  set z : D := x * ϖ ^ (-i) with hzdef
  have hzn : divisionNorm K D z = divisionNorm K D x * (ρ ^ i)⁻¹ := by
    rw [hzdef, divisionNorm_mul, divisionNorm_zpow, ← hρdef, zpow_neg]
  have hzle : divisionNorm K D z ≤ 1 := by
    rw [hzn]
    rw [mul_inv_le_iff₀ hipos, one_mul]
    exact hhigh
  have hzgt : ρ < divisionNorm K D z := by
    rw [hzn, lt_mul_inv_iff₀ hipos]
    calc ρ * ρ ^ i = ρ ^ (i + 1) := by rw [zpow_add₀ hρpos.ne' i 1, zpow_one]; ring
      _ < divisionNorm K D x := hlow
  have hzeq : divisionNorm K D z = 1 := by
    rcases lt_or_eq_of_le hzle with h | h
    · exact absurd (hϖ.le_norm z h) (not_le.2 hzgt)
    · exact h
  rw [hzn] at hzeq
  field_simp at hzeq
  exact hzeq

variable (K D) in
omit [IsUltrametricDist K] [ProperSpace K] in
/-- **The absolute value of a uniformizer of the base field is a positive power of the absolute
value of a uniformizer of the division algebra.** -/
theorem IsDivisionUniformizer.exists_pow_eq_norm {ϖ : D} (hϖ : IsDivisionUniformizer K D ϖ)
    {π : K} (hπ : IsNormUniformizer π) :
    ∃ e : ℕ, 0 < e ∧ divisionNorm K D ϖ ^ e = ‖π‖ := by
  have hne : algebraMap K D π ≠ 0 := fun h =>
    hπ.ne_zero ((algebraMap K D).injective (h.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ := hϖ.exists_zpow hne
  rw [divisionNorm_algebraMap] at hi
  set ρ : ℝ := divisionNorm K D ϖ with hρdef
  have hρpos : 0 < ρ := hϖ.norm_pos
  have hρ1 : ρ < 1 := hϖ.norm_lt_one
  have hipos : 0 < i := by
    by_contra hcon
    push_neg at hcon
    have h1 : ρ ^ (0 : ℤ) ≤ ρ ^ i := zpow_le_zpow_right_of_le_one₀ hρpos hρ1.le hcon
    rw [zpow_zero, ← hi] at h1
    exact absurd hπ.norm_lt_one (not_lt.2 h1)
  refine ⟨i.toNat, by omega, ?_⟩
  rw [hi, ← zpow_natCast ρ i.toNat]
  congr 1
  omega

variable (K D) in
omit [IsUltrametricDist K] [ProperSpace K] in
/-- **The ramification index of a division algebra over a local field is at most `n`**, where
`n ^ 2` is its dimension.  Some power at most `n` of the absolute value of a uniformizer is the
absolute value of a scalar, and the absolute values of scalars are the powers of that of a
uniformizer of the base field. -/
theorem IsDivisionUniformizer.ramification_le [Algebra.IsCentral K D] {ϖ : D}
    (hϖ : IsDivisionUniformizer K D ϖ) {π : K} (hπ : IsNormUniformizer π) {n e : ℕ}
    (hn : n * n = finrank K D) (he : 0 < e) (hee : divisionNorm K D ϖ ^ e = ‖π‖) : e ≤ n := by
  set ρ : ℝ := divisionNorm K D ϖ with hρdef
  have hρpos : 0 < ρ := hϖ.norm_pos
  have hρ1 : ρ < 1 := hϖ.norm_lt_one
  obtain ⟨m, c, hm0, hmn, hc0, hmc⟩ := exists_norm_eq_divisionNorm_pow K D hn hϖ.ne_zero
  obtain ⟨j, hj⟩ := hπ.exists_zpow hc0
  have hstep : ρ ^ ((m : ℤ)) = ρ ^ ((e : ℤ) * j) := by
    rw [zpow_natCast, hmc, hj, ← hee, ← zpow_natCast ρ e, ← zpow_mul]
  have hexp : (m : ℤ) = (e : ℤ) * j :=
    (zpow_right_strictAnti₀ hρpos hρ1).injective hstep
  have hjpos : 0 < j := by
    rcases le_or_gt j 0 with h | h
    · exfalso
      have : (e : ℤ) * j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
      omega
    · exact h
  have : (e : ℤ) ≤ (m : ℤ) := by nlinarith
  omega

end DivisionUniformizer

end InverseGalois.CFT

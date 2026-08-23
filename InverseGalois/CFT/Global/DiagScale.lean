import Mathlib
import InverseGalois.CFT.Global.DiagForm

/-!
# Rescaling a diagonal quadratic form

Isotropy of a diagonal quadratic form only depends on the square classes of its coefficients, and
it is unchanged when the whole form is multiplied by a nonzero scalar.  This file records those
two elementary invariances, together with the dyadic normalisation that lets one choose the
scaling factors: over `ℚ_[2]` every nonzero number becomes, after multiplication by a nonzero
square, either a unit or a uniformiser times a unit.

## Main results

* `InverseGalois.CFT.isDiagIsotropic_mul_sq`: isotropy is unchanged when each coefficient is
  multiplied by a nonzero square.
* `InverseGalois.CFT.isDiagIsotropic_const_mul`: isotropy is unchanged when the whole form is
  multiplied by a nonzero scalar.
* `InverseGalois.CFT.exists_sq_mul_norm_eq`: a nonzero `2`-adic number can be multiplied by a
  nonzero square so that its absolute value becomes `1` or `2⁻¹`.
* `InverseGalois.CFT.exists_scale_norm`: the same normalisation performed simultaneously on a
  whole family of nonzero `2`-adic numbers.
-/

namespace InverseGalois.CFT

open Local

variable {K : Type*} [Field K]

/-- **Isotropy only depends on the square classes of the coefficients.**  Multiplying the
coefficient `a i` by the nonzero square `s i ^ 2` amounts to the substitution `x i ↦ x i / s i`,
which is a bijection of the nonzero vectors. -/
theorem isDiagIsotropic_mul_sq {n : ℕ} {a s : Fin n → K} (hs : ∀ i, s i ≠ 0) :
    IsDiagIsotropic (fun i => a i * s i ^ 2) ↔ IsDiagIsotropic a := by
  constructor
  · rintro ⟨x, hx, hsum⟩
    refine ⟨fun i => x i * s i, ?_, ?_⟩
    · intro h
      refine hx (funext fun i => ?_)
      have hi := congrFun h i
      simp only [Pi.zero_apply] at hi ⊢
      exact (mul_eq_zero.1 hi).resolve_right (hs i)
    · rw [← hsum]
      exact Finset.sum_congr rfl fun i _ => by ring
  · rintro ⟨x, hx, hsum⟩
    refine ⟨fun i => x i / s i, ?_, ?_⟩
    · intro h
      refine hx (funext fun i => ?_)
      have hi := congrFun h i
      simp only [Pi.zero_apply] at hi ⊢
      exact (div_eq_zero_iff.1 hi).resolve_right (hs i)
    · rw [← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsi : s i ≠ 0 := hs i
      field_simp

/-- **Isotropy is unchanged by a global nonzero scalar.**  The same isotropic vector works for
both forms, because the scalar factors out of the sum. -/
theorem isDiagIsotropic_const_mul {n : ℕ} {a : Fin n → K} {c : K} (hc : c ≠ 0) :
    IsDiagIsotropic (fun i => c * a i) ↔ IsDiagIsotropic a := by
  have key : ∀ x : Fin n → K, ∑ i, c * a i * x i ^ 2 = c * ∑ i, a i * x i ^ 2 := by
    intro x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  constructor
  · rintro ⟨x, hx, hsum⟩
    exact ⟨x, hx, ((mul_eq_zero.1 ((key x).symm.trans hsum)).resolve_left hc)⟩
  · rintro ⟨x, hx, hsum⟩
    exact ⟨x, hx, by rw [key x, hsum, mul_zero]⟩

/-- **Dyadic normalisation of a single coefficient.**  Every nonzero `2`-adic number becomes,
after multiplication by a nonzero square, either a unit or a uniformiser times a unit: the square
`(2 ^ (-m)) ^ 2` shifts the valuation by an arbitrary even amount, and the valuation of the
result is `0` or `1` according to the parity of the valuation one started with. -/
theorem exists_sq_mul_norm_eq {x : ℚ_[2]} (hx : x ≠ 0) :
    ∃ s : ℚ_[2], s ≠ 0 ∧ (‖x * s ^ 2‖ = 1 ∨ ‖x * s ^ 2‖ = (2 : ℝ)⁻¹) := by
  have h2R : ((2 : ℕ) : ℝ) ≠ 0 := by norm_num
  obtain ⟨m, hm⟩ := Int.even_or_odd' x.valuation
  refine ⟨((2 : ℕ) : ℚ_[2]) ^ (-m : ℤ), zpow_ne_zero _ (NeZero.ne _), ?_⟩
  have hn : ‖x * (((2 : ℕ) : ℚ_[2]) ^ (-m : ℤ)) ^ 2‖
      = ((2 : ℕ) : ℝ) ^ (-x.valuation + 2 * m) := by
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hx, norm_pow, Padic.norm_p_zpow,
      ← zpow_natCast (((2 : ℕ) : ℝ) ^ (- -m)) 2, ← zpow_mul, ← zpow_add₀ h2R]
    norm_num
    ring_nf
  rcases hm with hm | hm
  · left
    rw [hn, hm]
    norm_num
  · right
    rw [hn, hm]
    push_cast
    rw [show -(2 * m + 1) + 2 * m = (-1 : ℤ) by ring]
    norm_num

/-- **Dyadic normalisation of a whole family of coefficients.**  Choosing a scaling factor
independently at each index normalises every coefficient at once. -/
theorem exists_scale_norm {n : ℕ} {a : Fin n → ℚ_[2]} (ha : ∀ i, a i ≠ 0) :
    ∃ s : Fin n → ℚ_[2], (∀ i, s i ≠ 0) ∧
      ∀ i, ‖a i * s i ^ 2‖ = 1 ∨ ‖a i * s i ^ 2‖ = (2 : ℝ)⁻¹ := by
  choose s hs hnorm using fun i => exists_sq_mul_norm_eq (ha i)
  exact ⟨s, hs, hnorm⟩

end InverseGalois.CFT

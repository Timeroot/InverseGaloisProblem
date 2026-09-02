/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.RadicalDegree

/-!
# Fourth roots of a rational number in an abelian extension

A rational number that is not a square in the rationals can perfectly well become a square in an
abelian extension — the square root generates a quadratic field, which is abelian.  A *fourth* root
is another matter: adjoining one of them to a field that does not already contain a square root of
minus one produces a non-normal extension, and adjoining one to a field that does contain such a
square root produces a cyclic quartic extension only for very special numbers.  The clean statement
proved here is that whenever `m`, `-m` and `-1` are all non-squares in the rationals, no abelian
extension of the rationals contains a fourth root of `m`.

The proof is a computation with two automorphisms.  Write `w` for the square of a putative fourth
root `u`, so that `w` is a square root of `m`.  If minus one has no square root in the field, then
every automorphism scales `u` by a fourth root of unity whose square is `1`, hence fixes `w`; but
some automorphism must send `w` to `-w`, and that forces `w = 0`.  If minus one does have a square
root `z`, then one builds an automorphism `σ` sending `w` to `-w` while fixing `z`, and takes `τ`
sending `z` to `-z`.  The scaling factor of `u` under `σ` is a square root of minus one, so `τ`
negates it, while the scaling factor of `u` under `τ` is a fourth root of unity, so `σ` fixes it.
Comparing `σ (τ u)` with `τ (σ u)` in a commutative Galois group then yields `2 u = 0`.

The companion result is the irreducibility of `X ^ 4` minus a constant over a field containing a
square root of minus one: there the norm of a square root of the adjoined square root, corrected by
that square root of minus one, would be a square root of the constant.

## Main results

* `InverseGalois.CFT.X_pow_four_sub_C_irreducible`: over a field containing a square root of minus
  one, `X ^ 4` minus a non-square is irreducible.
* `InverseGalois.CFT.exists_algEquiv_eq_neg`: a square root of a rational non-square is negated by
  some automorphism.
* `InverseGalois.CFT.pow_four_ne_algebraMap_of_mul_comm`: **an abelian extension of the rationals
  contains no fourth root of a rational number `m` for which `m`, `-m` and `-1` are non-squares.**
* `InverseGalois.CFT.rat_sq_ne_two`: two is not a rational square.

## Tags

Kummer theory, fourth root, abelian extension, irreducibility, quartic
-/

open Module Polynomial IntermediateField

namespace InverseGalois.CFT

/-! ### Irreducibility of `X ^ 4 - C a` -/

section Quartic

variable {K : Type*} [Field K]

/-- **Over a field containing a square root of minus one, `X ^ 4` minus a non-square is
irreducible.**  Adjoining a square root `x` of the constant, a square root of `x` would have a norm
whose square is minus the constant, and multiplying that norm by the square root of minus one would
produce a square root of the constant itself. -/
theorem X_pow_four_sub_C_irreducible {i : K} (hi : i ^ 2 = -1) {a : K}
    (ha : ∀ b : K, b ^ 2 ≠ a) : Irreducible ((X : K[X]) ^ 4 - C a) := by
  have h4 : (4 : ℕ) = 2 * 2 := by norm_num
  rw [h4]
  refine X_pow_mul_sub_C_irreducible (X_pow_sub_C_irreducible_of_prime Nat.prime_two ha) ?_
  intro E _ _ x hx
  have hint : IsIntegral K x := not_not.mp fun h ↦ by
    simpa only [degree_zero, degree_X_pow_sub_C Nat.prime_two.pos,
      WithBot.natCast_ne_bot] using congr_arg degree (hx.symm.trans (dif_neg h))
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => ha (i * Algebra.norm K b) ?_
  have hnorm : Algebra.norm K b ^ 2 = -a := by
    rw [← map_pow, hb, ← adjoin.powerBasis_gen hint,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    simp [minpoly_gen, hx]
  rw [mul_pow, hi, hnorm]
  ring

end Quartic

/-! ### Square roots under the Galois group -/

section Abelian

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- An automorphism over the rationals either fixes a square root of a rational number or negates
it. -/
theorem eq_or_eq_neg_of_sq_eq_algebraMap {x : K} {m : ℚ}
    (hx : x ^ 2 = algebraMap ℚ K m) (ρ : Gal(K/ℚ)) : ρ x = x ∨ ρ x = -x :=
  eq_or_eq_neg_of_sq_eq_sq _ _ (by rw [← map_pow, hx, AlgEquiv.commutes])

/-- **A square root of a rational number that is not a rational square is negated by some
automorphism**, since minus that square root has the same minimal polynomial. -/
theorem exists_algEquiv_eq_neg [Normal ℚ K] {x : K} {m : ℚ}
    (hx : x ^ 2 = algebraMap ℚ K m) (hm : ∀ y : ℚ, y ^ 2 ≠ m) :
    ∃ ρ : Gal(K/ℚ), ρ x = -x := by
  have hirr : Irreducible ((X : ℚ[X]) ^ 2 - C m) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hm
  have hmonic : ((X : ℚ[X]) ^ 2 - C m).Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have haeval : Polynomial.aeval (-x) ((X : ℚ[X]) ^ 2 - C m) = 0 := by
    have h : Polynomial.aeval (-x) ((X : ℚ[X]) ^ 2 - C m) = x ^ 2 - algebraMap ℚ K m := by
      simp only [map_sub, map_pow, aeval_X, aeval_C]
      ring
    rw [h, hx, sub_self]
  have hmin : (X : ℚ[X]) ^ 2 - C m = minpoly ℚ (-x) :=
    minpoly.eq_of_irreducible_of_monic hirr haeval hmonic
  refine minpoly.exists_algEquiv_of_root ⟨_, hmonic.ne_zero, haeval⟩ ?_
  rw [← hmin]
  have h : Polynomial.aeval x ((X : ℚ[X]) ^ 2 - C m) = x ^ 2 - algebraMap ℚ K m := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
  rw [h, hx, sub_self]

/-- An automorphism fixing a square root of minus one fixes every fourth root of unity, those being
plus or minus one and plus or minus that square root. -/
theorem map_eq_self_of_pow_four_eq_one {z : K} (hz : z ^ 2 = -1) {σ : Gal(K/ℚ)}
    (hσz : σ z = z) {β : K} (hβ : β ^ 4 = 1) : σ β = β := by
  have hfac : (β ^ 2 - 1) * (β ^ 2 + 1) = 0 := by linear_combination hβ
  rcases mul_eq_zero.mp hfac with h | h
  · rcases eq_or_eq_neg_of_sq_eq_sq β 1 (by linear_combination h) with h2 | h2
    · rw [h2, map_one]
    · rw [h2, map_neg, map_one]
  · rcases eq_or_eq_neg_of_sq_eq_sq β z (by rw [hz]; linear_combination h) with h2 | h2
    · rw [h2, hσz]
    · rw [h2, map_neg, hσz]

/-- An automorphism negating a square root of minus one negates every square root of minus one,
there being only the two. -/
theorem map_eq_neg_of_sq_eq_neg_one {z : K} (hz : z ^ 2 = -1) {τ : Gal(K/ℚ)}
    (hτz : τ z = -z) {α : K} (hα : α ^ 2 = -1) : τ α = -α := by
  rcases eq_or_eq_neg_of_sq_eq_sq α z (by rw [hz, hα]) with h2 | h2
  · rw [h2, hτz]
  · rw [h2, map_neg, hτz]

/-- **When minus one has no square root, the square of a fourth root of a rational number is fixed
by every automorphism**: the scaling factor is a fourth root of unity whose square, not being minus
one, is one. -/
theorem map_sq_eq_self_of_forall_sq_ne_neg_one (hex : ∀ z : K, z ^ 2 ≠ -1) {u : K} {m : ℚ}
    (hu : u ^ 4 = algebraMap ℚ K m) (ρ : Gal(K/ℚ)) : ρ (u ^ 2) = u ^ 2 := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp
  obtain ⟨ξ, hξ⟩ : ∃ ξ : K, ρ u = ξ * u := ⟨ρ u * u⁻¹, by field_simp⟩
  have h4 : ξ ^ 4 * u ^ 4 = u ^ 4 := by
    rw [← mul_pow, ← hξ, ← map_pow, hu, AlgEquiv.commutes]
  have hξ4 : ξ ^ 4 = 1 := by
    rcases mul_eq_zero.mp (show (ξ ^ 4 - 1) * u ^ 4 = 0 by linear_combination h4) with h | h
    · linear_combination h
    · exact absurd h (pow_ne_zero 4 hu0)
  have hξ2 : ξ ^ 2 = 1 := by
    rcases mul_eq_zero.mp (show (ξ ^ 2 - 1) * (ξ ^ 2 + 1) = 0 by linear_combination hξ4) with h | h
    · linear_combination h
    · exact absurd (show ξ ^ 2 = -1 by linear_combination h) (hex ξ)
  rw [map_pow, hξ, mul_pow, hξ2, one_mul]

/-- **A rational number whose square, whose negative and whose sign-reversed unit are all rational
non-squares has no fourth root in an abelian extension of the rationals.**  More precisely, if
neither `m` nor `-m` nor `-1` is the square of a rational number, then no element of a normal
extension with commutative Galois group has fourth power `m`. -/
theorem pow_four_ne_algebraMap_of_mul_comm [Normal ℚ K]
    (hcomm : ∀ σ τ : Gal(K/ℚ), σ * τ = τ * σ) {m : ℚ}
    (hm : ∀ y : ℚ, y ^ 2 ≠ m) (hmneg : ∀ y : ℚ, y ^ 2 ≠ -m) (hone : ∀ y : ℚ, y ^ 2 ≠ -1)
    (u : K) : u ^ 4 ≠ algebraMap ℚ K m := by
  haveI : CharZero K := algebraRat.charZero K
  intro hu
  have hm0 : m ≠ 0 := fun h => hm 0 (by rw [h]; ring)
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at hu
    exact hm0 ((map_eq_zero_iff _ (algebraMap ℚ K).injective).mp hu.symm)
  have hw2 : (u ^ 2) ^ 2 = algebraMap ℚ K m := by rw [← pow_mul]; exact hu
  obtain ⟨ρw, hρw⟩ := exists_algEquiv_eq_neg hw2 hm
  by_cases hex : ∃ z : K, z ^ 2 = -1
  · obtain ⟨z, hz⟩ := hex
    have hzsq : z ^ 2 = algebraMap ℚ K (-1) := by rw [hz]; simp
    obtain ⟨ρz, hρz⟩ := exists_algEquiv_eq_neg hzsq hone
    have hv : (u ^ 2 * z) ^ 2 = algebraMap ℚ K (-m) := by
      rw [mul_pow, hw2, hz, map_neg]; ring
    obtain ⟨ρv, hρv⟩ := exists_algEquiv_eq_neg hv hmneg
    obtain ⟨σ, hσw, hσz⟩ : ∃ σ : Gal(K/ℚ), σ (u ^ 2) = -(u ^ 2) ∧ σ z = z := by
      rcases eq_or_eq_neg_of_sq_eq_algebraMap hzsq ρw with hb | hb
      · exact ⟨ρw, hρw, hb⟩
      · have hexp : ρv (u ^ 2) * ρv z = -(u ^ 2 * z) := by rw [← map_mul]; exact hρv
        rcases eq_or_eq_neg_of_sq_eq_algebraMap hw2 ρv with h' | h'
        · rw [h'] at hexp
          have hzv : ρv z = -z :=
            mul_left_cancel₀ (pow_ne_zero 2 hu0)
              (show u ^ 2 * ρv z = u ^ 2 * -z by linear_combination hexp)
          refine ⟨ρv.trans ρw, ?_, ?_⟩
          · rw [AlgEquiv.trans_apply, h', hρw]
          · rw [AlgEquiv.trans_apply, hzv, map_neg, hb, neg_neg]
        · rw [h'] at hexp
          have hzv : ρv z = z :=
            mul_left_cancel₀ (pow_ne_zero 2 hu0)
              (show u ^ 2 * ρv z = u ^ 2 * z by linear_combination -hexp)
          exact ⟨ρv, h', hzv⟩
    obtain ⟨α, hα⟩ : ∃ α : K, σ u = α * u := ⟨σ u * u⁻¹, by field_simp⟩
    obtain ⟨β, hβ⟩ : ∃ β : K, ρz u = β * u := ⟨ρz u * u⁻¹, by field_simp⟩
    have hα2 : α ^ 2 = -1 := by
      have h1 : (σ u) ^ 2 = -(u ^ 2) := by rw [← map_pow]; exact hσw
      rw [hα, mul_pow] at h1
      rcases mul_eq_zero.mp (show (α ^ 2 + 1) * u ^ 2 = 0 by linear_combination h1) with h | h
      · linear_combination h
      · exact absurd h (pow_ne_zero 2 hu0)
    have hβ4 : β ^ 4 = 1 := by
      have h1 : (ρz u) ^ 4 = u ^ 4 := by rw [← map_pow, hu, AlgEquiv.commutes]
      rw [hβ, mul_pow] at h1
      rcases mul_eq_zero.mp (show (β ^ 4 - 1) * u ^ 4 = 0 by linear_combination h1) with h | h
      · linear_combination h
      · exact absurd h (pow_ne_zero 4 hu0)
    have hα0 : α ≠ 0 := by
      intro h
      rw [h] at hα2
      exact one_ne_zero (show (1 : K) = 0 by linear_combination hα2)
    have hβ0 : β ≠ 0 := by
      intro h
      rw [h] at hβ4
      exact one_ne_zero (show (1 : K) = 0 by linear_combination -hβ4)
    have hσβ : σ β = β := map_eq_self_of_pow_four_eq_one hz hσz hβ4
    have hτα : ρz α = -α := map_eq_neg_of_sq_eq_neg_one hz hρz hα2
    have e1 : σ (ρz u) = β * (α * u) := by rw [hβ, map_mul, hσβ, hα]
    have e2 : ρz (σ u) = -α * (β * u) := by rw [hα, map_mul, hτα, hβ]
    have hcom : σ (ρz u) = ρz (σ u) := by
      have h := AlgEquiv.ext_iff.mp (hcomm σ ρz) u
      simpa only [AlgEquiv.mul_apply] using h
    rw [e1, e2] at hcom
    have hzero : (2 : K) * (α * β * u) = 0 := by linear_combination hcom
    rcases mul_eq_zero.mp hzero with h | h
    · exact (by norm_num : (2 : K) ≠ 0) h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact hα0 h''
        · exact hβ0 h''
      · exact hu0 h'
  · push_neg at hex
    have hfix := map_sq_eq_self_of_forall_sq_ne_neg_one hex hu ρw
    have hzero : (2 : K) * u ^ 2 = 0 := by linear_combination hρw - hfix
    rcases mul_eq_zero.mp hzero with h | h
    · exact (by norm_num : (2 : K) ≠ 0) h
    · exact pow_ne_zero 2 hu0 h

end Abelian

/-! ### Small rational non-squares -/

section Rational

/-- **Two is not the square of a rational number**, the square root of two being irrational. -/
theorem rat_sq_ne_two (y : ℚ) : y ^ 2 ≠ 2 := by
  intro h
  refine irrational_sqrt_two ⟨|y|, ?_⟩
  rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs]
  congr 1
  exact_mod_cast h

/-- A negative rational number is not the square of a rational number. -/
theorem rat_sq_ne_of_neg {m : ℚ} (hm : m < 0) (y : ℚ) : y ^ 2 ≠ m :=
  fun h => absurd (h ▸ sq_nonneg y) (not_le.mpr hm)

end Rational

/-! ### Transfer to an intermediate field of the algebraic closure -/

section Transfer

variable {A : IntermediateField ℚ (AlgebraicClosure ℚ)} {m : ℚ}

/-- **Over an intermediate field containing a square root of minus one, `X ^ 4` minus a rational
number without a square root there is irreducible.** -/
theorem irreducible_X_pow_four_sub_C_of_forall_sq_ne {i : AlgebraicClosure ℚ} (hiA : i ∈ A)
    (hi : i ^ 2 = -1)
    (hm : ∀ u ∈ A, u ^ 2 ≠ algebraMap ℚ (AlgebraicClosure ℚ) m) :
    Irreducible ((X : (↥A)[X]) ^ 4 - C (algebraMap ℚ ↥A m)) := by
  refine X_pow_four_sub_C_irreducible (i := ⟨i, hiA⟩) (Subtype.ext (by simpa using hi)) ?_
  intro b hb
  refine hm (b : AlgebraicClosure ℚ) b.2 ?_
  have h := congrArg (fun y : ↥A => (y : AlgebraicClosure ℚ)) hb
  simpa [algebraMap_intermediateField_eq] using h

/-- **An abelian intermediate field of the algebraic closure contains no fourth root of a rational
number `m` for which `m`, `-m` and `-1` are rational non-squares.** -/
theorem forall_mem_pow_four_ne_of_mul_comm [Normal ℚ ↥A]
    (hcomm : ∀ σ τ : Gal(↥A/ℚ), σ * τ = τ * σ)
    (hm : ∀ y : ℚ, y ^ 2 ≠ m) (hmneg : ∀ y : ℚ, y ^ 2 ≠ -m) (hone : ∀ y : ℚ, y ^ 2 ≠ -1) :
    ∀ u ∈ A, u ^ 4 ≠ algebraMap ℚ (AlgebraicClosure ℚ) m := by
  intro u hu heq
  refine pow_four_ne_algebraMap_of_mul_comm hcomm hm hmneg hone ⟨u, hu⟩ (Subtype.ext ?_)
  simpa [algebraMap_intermediateField_eq] using heq

end Transfer

end InverseGalois.CFT

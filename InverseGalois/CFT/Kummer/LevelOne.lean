/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The level of a unit whose conjugate is a power of itself

Let `v` be a discrete valuation with uniformizer `π` on a field of residue characteristic `ℓ`, in
which `ℓ` itself has valuation `π ^ (ℓ - 1)`, and let `δ` be an automorphism which preserves `v`,
acts trivially on the residue field, and satisfies `δ π ≡ g π` modulo `π ^ 2` for an integer `g`.
A unit `u` congruent to one whose conjugate `δ u` is `u ^ g` times an `ℓ`-th power then has a very
restricted *level*, the valuation of `u - 1` measured in powers of `π`: writing `u = 1 + c π ^ n`
with `c` a unit, the two ways of computing `δ u` modulo `π ^ (n + 1)` give `g ^ n c ≡ g c`, so `g`
raised to `n - 1` is congruent to one.  Below the ramification index `ℓ - 1` of the cyclotomic
field this forces the level to be one as soon as `g` is a primitive root.

The computation is elementary and is carried out here for an arbitrary valuation, so that only the
listed congruences have to be verified at the place under consideration.

## Main results

* `InverseGalois.CFT.valuation_natCast_le_one`: an integer has valuation at most one.
* `InverseGalois.CFT.valuation_pow_sub_pow_le`: the valuation of a difference of powers.
* `InverseGalois.CFT.valuation_pow_prime_sub_one_le`: the valuation of `(1 + s) ^ ℓ - 1`.
* `InverseGalois.CFT.valuation_sub_one_lt_one_of_pow`: an `ℓ`-th root of a unit congruent to one
  is congruent to one, the Frobenius being injective on the residue field.
* `InverseGalois.CFT.valuation_natCast_pow_sub_self_le`: **the congruence satisfied by the level**,
  `g ^ n ≡ g` modulo the maximal ideal.

## Tags

valuation, uniformizer, level, ramification, Kummer theory
-/

open Finset

namespace InverseGalois.CFT

/-! ### Valuations of sums, powers and integers -/

section Ring

variable {R Γ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ)

/-- **A natural number has valuation at most one**, because the valuation of a sum is at most the
larger of the two valuations. -/
theorem valuation_natCast_le_one (n : ℕ) : v (n : R) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact le_trans (v.map_add _ _) (max_le ih (le_of_eq v.map_one))

/-- A geometric sum of elements of valuation at most one has valuation at most one. -/
theorem valuation_geom_sum_le {x : R} (hx : v x ≤ 1) (n : ℕ) :
    v (∑ i ∈ range n, x ^ i) ≤ 1 :=
  Valuation.map_sum_le _ fun i _ => by rw [v.map_pow]; exact pow_le_one' hx i

/-- **The valuation of a difference of powers.**  Each term of the geometric sum is bounded by a
common bound for the two elements. -/
theorem valuation_pow_sub_pow_le {x y : R} {a : Γ} (hx : v x ≤ a) (hy : v y ≤ a) (n : ℕ) :
    v (x ^ n - y ^ n) ≤ v (x - y) * a ^ (n - 1) := by
  rw [← geom_sum₂_mul x y n, v.map_mul]
  refine le_trans (le_of_eq (mul_comm _ _)) (mul_le_mul_right ?_ _)
  refine Valuation.map_sum_le _ fun i hi => ?_
  rw [v.map_mul, v.map_pow, v.map_pow]
  refine le_trans (mul_le_mul' (pow_le_pow_left' hx i) (pow_le_pow_left' hy _)) ?_
  rw [← pow_add]
  exact le_of_eq (congrArg _ (by have := mem_range.mp hi; omega : i + (n - 1 - i) = n - 1))

/-- The valuation of `x ^ n - 1`, for `x` of valuation at most one. -/
theorem valuation_pow_sub_one_le {x : R} (hx : v x ≤ 1) (n : ℕ) :
    v (x ^ n - 1) ≤ v (x - 1) := by
  rw [← geom_sum_mul x n, v.map_mul]
  exact mul_le_of_le_one_left' (valuation_geom_sum_le v hx n)

/-- **A power of `1 + t` is `1 + n t` up to a multiple of `t ^ 2`** with integral coefficient. -/
theorem exists_valuation_one_add_pow {t : R} (ht : v t ≤ 1) (n : ℕ) :
    ∃ B : R, v B ≤ 1 ∧ (1 + t) ^ n = 1 + n * t + t ^ 2 * B := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨B, hB, hEq⟩ := ih
    refine ⟨B + n + t * B, ?_, ?_⟩
    · refine le_trans (v.map_add _ _) (max_le (le_trans (v.map_add _ _)
        (max_le hB (valuation_natCast_le_one v n))) ?_)
      rw [v.map_mul]
      exact mul_le_one' ht hB
    · rw [pow_succ, hEq]
      push_cast
      ring

/-- **The `ℓ`-th power of `1 + s` is `1 + s ^ ℓ` up to a multiple of `ℓ s`**, for `ℓ` prime. -/
theorem valuation_one_add_pow_prime_sub {ℓ : ℕ} (hℓ : ℓ.Prime) {s : R} (hs : v s ≤ 1) :
    v ((1 + s) ^ ℓ - 1 - s ^ ℓ) ≤ v (ℓ : R) * v s := by
  have h := add_pow_prime_eq hℓ (1 : R) s
  rw [one_pow] at h
  have hrw : (1 + s) ^ ℓ - 1 - s ^ ℓ = (ℓ : R) * s *
      ∑ k ∈ Ioo 0 ℓ, (1 : R) ^ (k - 1) * s ^ (ℓ - k - 1) * ((ℓ.choose k / ℓ : ℕ) : R) := by
    rw [h]; ring
  rw [hrw, v.map_mul, v.map_mul]
  refine mul_le_of_le_one_right' (Valuation.map_sum_le _ fun k _ => ?_)
  rw [v.map_mul, v.map_mul, v.map_pow, v.map_pow]
  exact mul_le_one' (mul_le_one' (pow_le_one' (le_of_eq v.map_one) _) (pow_le_one' hs _))
    (valuation_natCast_le_one v _)

/-- **The valuation of `(1 + s) ^ ℓ - 1`**, for `ℓ` prime. -/
theorem valuation_pow_prime_sub_one_le {ℓ : ℕ} (hℓ : ℓ.Prime) {s : R} {b : Γ} (hb : b ≤ 1)
    (hs : v s ≤ b) : v ((1 + s) ^ ℓ - 1) ≤ max (v (ℓ : R) * b) (b ^ ℓ) := by
  have hs1 : v s ≤ 1 := le_trans hs hb
  have hrw : (1 + s) ^ ℓ - 1 = ((1 + s) ^ ℓ - 1 - s ^ ℓ) + s ^ ℓ := by ring
  rw [hrw]
  refine le_trans (v.map_add _ _) (max_le_max ?_ ?_)
  · exact le_trans (valuation_one_add_pow_prime_sub v hℓ hs1) (mul_le_mul_right hs _)
  · rw [v.map_pow]
    exact pow_le_pow_left' hs ℓ

end Ring

/-! ### The level of an eigen-unit -/

section Field

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- Cancelling a nonzero factor in an inequality of a linearly ordered commutative group with
zero. -/
theorem le_of_mul_le_mul_right₀ {a b c : Γ} (hc : c ≠ 0) (h : a * c ≤ b * c) : a ≤ b := by
  have h' := mul_le_mul_left h c⁻¹
  rwa [mul_inv_cancel_right₀ hc, mul_inv_cancel_right₀ hc] at h'

/-- **An `ℓ`-th root of a unit congruent to one is congruent to one.**  The residue field has
characteristic `ℓ`, on which the Frobenius is injective. -/
theorem valuation_sub_one_lt_one_of_pow {v : Valuation K Γ} {ℓ : ℕ} (hℓ : ℓ.Prime) {s : K}
    (hs : v s ≤ 1) (hvℓ : v (ℓ : K) < 1) (h : v ((1 + s) ^ ℓ - 1) < 1) : v s < 1 := by
  have key : v (s ^ ℓ) < 1 := by
    have hrw : s ^ ℓ = ((1 + s) ^ ℓ - 1) - ((1 + s) ^ ℓ - 1 - s ^ ℓ) := by ring
    rw [hrw]
    refine lt_of_le_of_lt (v.map_sub _ _) (max_lt h ?_)
    exact lt_of_le_of_lt (valuation_one_add_pow_prime_sub v hℓ hs)
      (lt_of_le_of_lt (mul_le_of_le_one_right' hs) hvℓ)
  rw [v.map_pow] at key
  by_contra hc
  exact absurd key (not_lt.mpr (one_le_pow_of_one_le' (not_lt.mp hc) ℓ))

variable {v : Valuation K Γ} {π u y : K} {δ : K →+* K} {ℓ g n : ℕ}

/-- **The congruence satisfied by the level of an eigen-unit.**  Comparing the two computations of
`δ u` modulo the `n + 1`-st power of the maximal ideal, one from the equation `δ u = u ^ g y ^ ℓ`
and one from the action of `δ` on a uniformizer, gives `g ^ n ≡ g`. -/
theorem valuation_natCast_pow_sub_self_le (hℓ : ℓ.Prime) (hπ0 : v π ≠ 0) (hπ1 : v π < 1)
    (hunif : ∀ x : K, v x < 1 → v x ≤ v π) (hvℓ : v (ℓ : K) = v π ^ (ℓ - 1))
    (hδv : ∀ x : K, v (δ x) = v x) (hδres : ∀ x : K, v x ≤ 1 → v (δ x - x) < 1)
    (hδπ : v (δ π - g * π) ≤ v π ^ 2) (hu : v u = 1) (hy : v y = 1) (heq : δ u = u ^ g * y ^ ℓ)
    (hn1 : 1 ≤ n) (hnℓ : n + 1 ≤ ℓ) (hlev : v (u - 1) = v π ^ n) :
    v ((g : K) ^ n - g) ≤ v π := by
  haveI : Nontrivial Γ := ⟨⟨v π, 1, ne_of_lt hπ1⟩⟩
  have hπle : v π ≤ 1 := hπ1.le
  have hgle : v ((g : K)) ≤ 1 := valuation_natCast_le_one v g
  have hule : v u ≤ 1 := le_of_eq hu
  have hune : u ≠ 0 := (Valuation.ne_zero_iff v).mp (by rw [hu]; exact one_ne_zero)
  have hvt1 : v (u - 1) < 1 := by
    rw [hlev]
    calc v π ^ n ≤ v π ^ 1 := pow_le_pow_right_of_le_one' hπle hn1
      _ = v π := pow_one _
      _ < 1 := hπ1
  have hvℓ1 : v (ℓ : K) < 1 := by
    rw [hvℓ]
    calc v π ^ (ℓ - 1) ≤ v π ^ 1 := pow_le_pow_right_of_le_one' hπle (by have := hℓ.two_le; omega)
      _ = v π := pow_one _
      _ < 1 := hπ1
  -- the conjugate of `u` differs from `u ^ g` by at most `π ^ ℓ`
  have hδu1 : v (δ u - 1) = v (u - 1) := by
    have hrw : δ u - 1 = δ (u - 1) := by rw [map_sub, map_one]
    rw [hrw, hδv]
  have hug1 : v (u ^ g - 1) ≤ v (u - 1) := valuation_pow_sub_one_le v hule g
  have hdiff : v (δ u - u ^ g) ≤ v (u - 1) := by
    have hrw : δ u - u ^ g = (δ u - 1) - (u ^ g - 1) := by ring
    rw [hrw]
    exact v.map_sub_le (le_of_eq hδu1) hug1
  have hyl : v (y ^ ℓ - 1) ≤ v (u - 1) := by
    have hrw : y ^ ℓ - 1 = (δ u - u ^ g) / u ^ g := by
      rw [heq, eq_div_iff (pow_ne_zero g hune)]
      ring
    rw [hrw, map_div₀, v.map_pow, hu, one_pow, div_one]
    exact hdiff
  have hone : (1 : K) + (y - 1) = y := by ring
  have hs1 : v (y - 1) ≤ 1 :=
    le_trans (v.map_sub _ _) (max_le (le_of_eq hy) (le_of_eq v.map_one))
  have hylt : v (y - 1) < 1 := by
    refine valuation_sub_one_lt_one_of_pow hℓ hs1 hvℓ1 ?_
    rw [hone]
    exact lt_of_le_of_lt hyl hvt1
  have hsπ : v (y - 1) ≤ v π := hunif _ hylt
  have hylπ : v (y ^ ℓ - 1) ≤ v π ^ ℓ := by
    rw [← hone]
    refine le_trans (valuation_pow_prime_sub_one_le v hℓ hπle hsπ) (max_le ?_ (le_refl _))
    rw [hvℓ, ← pow_succ]
    exact le_of_eq (congrArg _ (by have := hℓ.two_le; omega : ℓ - 1 + 1 = ℓ))
  have hstep2 : v (δ u - u ^ g) ≤ v π ^ ℓ := by
    have hrw : δ u - u ^ g = u ^ g * (y ^ ℓ - 1) := by rw [heq]; ring
    rw [hrw, v.map_mul, v.map_pow, hu, one_pow, one_mul]
    exact hylπ
  -- the binomial expansion of `u ^ g`
  have hstep3 : v (u ^ g - 1 - (g : K) * (u - 1)) ≤ v π ^ (n + 1) := by
    obtain ⟨B, hB, hEq⟩ := exists_valuation_one_add_pow v hvt1.le g
    have honeu : (1 : K) + (u - 1) = u := by ring
    rw [honeu] at hEq
    have hrw : u ^ g - 1 - (g : K) * (u - 1) = (u - 1) ^ 2 * B := by rw [hEq]; ring
    rw [hrw, v.map_mul, v.map_pow, hlev]
    calc (v π ^ n) ^ 2 * v B ≤ (v π ^ n) ^ 2 * 1 := mul_le_mul_right hB _
      _ = v π ^ (n * 2) := by rw [mul_one, ← pow_mul]
      _ ≤ v π ^ (n + 1) := pow_le_pow_right_of_le_one' hπle (by omega)
  have hstep4 : v (δ (u - 1) - (g : K) * (u - 1)) ≤ v π ^ (n + 1) := by
    have hrw : δ (u - 1) - (g : K) * (u - 1)
        = (δ u - u ^ g) + (u ^ g - 1 - (g : K) * (u - 1)) := by
      rw [map_sub, map_one]; ring
    rw [hrw]
    refine le_trans (v.map_add _ _) (max_le ?_ hstep3)
    exact le_trans hstep2 (pow_le_pow_right_of_le_one' hπle hnℓ)
  -- the action of `δ` on a uniformizer
  have hπne : π ≠ 0 := (Valuation.ne_zero_iff v).mp hπ0
  have hvc : v ((u - 1) / π ^ n) = 1 := by
    rw [map_div₀, v.map_pow, hlev]
    exact div_self (pow_ne_zero n hπ0)
  have htc : u - 1 = ((u - 1) / π ^ n) * π ^ n := by field_simp
  have hδc : v (δ ((u - 1) / π ^ n) - (u - 1) / π ^ n) ≤ v π :=
    hunif _ (hδres _ (le_of_eq hvc))
  have hδπn : v ((δ π) ^ n - ((g : K) * π) ^ n) ≤ v π ^ (n + 1) := by
    have h1 : v (δ π) ≤ v π := le_of_eq (hδv π)
    have h2 : v ((g : K) * π) ≤ v π := by
      rw [v.map_mul]
      exact mul_le_of_le_one_left' hgle
    calc v ((δ π) ^ n - ((g : K) * π) ^ n) ≤ v (δ π - (g : K) * π) * v π ^ (n - 1) :=
          valuation_pow_sub_pow_le v h1 h2 n
      _ ≤ v π ^ 2 * v π ^ (n - 1) := mul_le_mul_left hδπ _
      _ = v π ^ (n + 1) := by rw [← pow_add]; exact congrArg _ (by omega)
  have hδt : v (δ (u - 1) - (g : K) ^ n * (u - 1)) ≤ v π ^ (n + 1) := by
    set c := (u - 1) / π ^ n with hc
    have h1 : δ (u - 1) = δ c * δ π ^ n := by rw [htc, map_mul, map_pow]
    have hexp : δ (u - 1) - (g : K) ^ n * (u - 1)
        = (δ c - c) * δ π ^ n + c * (δ π ^ n - ((g : K) * π) ^ n) := by
      rw [h1, htc, mul_pow]
      ring
    rw [hexp]
    refine le_trans (v.map_add _ _) (max_le ?_ ?_)
    · rw [v.map_mul, v.map_pow, hδv]
      calc v (δ c - c) * v π ^ n ≤ v π * v π ^ n := mul_le_mul_left hδc _
        _ = v π ^ (n + 1) := by rw [pow_succ']
    · rw [v.map_mul, hvc, one_mul]
      exact hδπn
  -- comparing the two computations
  have hfin : v (((g : K) ^ n - g) * (u - 1)) ≤ v π ^ (n + 1) := by
    have hrw : ((g : K) ^ n - g) * (u - 1)
        = (δ (u - 1) - (g : K) * (u - 1)) - (δ (u - 1) - (g : K) ^ n * (u - 1)) := by ring
    rw [hrw]
    exact v.map_sub_le hstep4 hδt
  rw [v.map_mul, hlev] at hfin
  refine le_of_mul_le_mul_right₀ (pow_ne_zero n hπ0) ?_
  rwa [pow_succ'] at hfin

end Field

end InverseGalois.CFT

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Approximation.Completion
import InverseGalois.CFT.Local.PowClose

/-!
# Approximation modulo the `n`-th powers of the completions

Weak approximation places an element of a number field near prescribed elements of the completions
at all the infinite places and at finitely many primes at once.  Being near a nonzero element of a
completion means differing from it by a factor that is an `n`-th power there, and the accuracy
required for that depends on the place and on the prescribed element but not on the element
approximating it.  Taking the smallest of the finitely many accuracies therefore produces a single
element of the field which at every one of the prescribed places agrees with the prescribed element
up to an `n`-th power.

In other words the field surjects onto the product over the chosen places of the quotients of the
multiplicative groups of the completions by their `n`-th powers.

## Main results

* `InverseGalois.CFT.exists_ne_zero_pow_mul_eq_completion`: **an element of the field matches
  prescribed nonzero elements of the completions at all the infinite places and at finitely many
  primes up to `n`-th powers.**

## Tags

number field, weak approximation, completion, place, power
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]
variable {Y : Type*} [Finite Y] {ι : Y → HeightOneSpectrum (𝓞 K)}

/-- **An element of the field matches prescribed nonzero elements of the completions at all the
infinite places and at finitely many primes up to `n`-th powers.**  Each place supplies an accuracy
within which an element of its completion differs from the prescribed one by an `n`-th power; the
smallest of these finitely many accuracies, cut down further so as to keep the approximating element
away from zero, is the accuracy to run weak approximation at. -/
theorem exists_ne_zero_pow_mul_eq_completion {n : ℕ} (hn : n ≠ 0) (hinj : Function.Injective ι)
    (a : ∀ w : InfinitePlace K, w.Completion) (ha : ∀ w, a w ≠ 0)
    (c : ∀ y : Y, (ι y).adicCompletion K) (hc : ∀ y, c y ≠ 0) :
    ∃ b : K, b ≠ 0 ∧
      (∀ w : InfinitePlace K, ∃ z : w.Completion, z ^ n * a w = algebraMap K w.Completion b) ∧
      ∀ y : Y, ∃ z : (ι y).adicCompletion K,
        z ^ n * c y = algebraMap K ((ι y).adicCompletion K) b := by
  choose rA hrA hA using fun w : InfinitePlace K =>
    exists_pow_mul_eq_of_norm_sub_lt_infiniteCompletion w hn (ha w)
  choose rC hrC hC using fun y : Y =>
    exists_pow_mul_eq_of_norm_sub_lt_adicCompletion (ι y) hn (hc y)
  set f : InfinitePlace K ⊕ Y → ℝ :=
    Sum.elim (fun w => min (rA w) ‖a w‖) rC with hf
  have hfpos : ∀ i, 0 < f i := by
    rintro (w | y)
    · exact lt_min (hrA w) (norm_pos_iff.mpr (ha w))
    · exact hrC y
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
  obtain ⟨b, hbA, hbC⟩ := exists_norm_sub_lt_completion hinj a c (hfpos i₀)
  refine ⟨b, ?_, fun w => ?_, fun y => ?_⟩
  · obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    intro hb
    have h1 : ‖algebraMap K w.Completion b - a w‖ < ‖a w‖ :=
      lt_of_lt_of_le (hbA w) (le_trans (hi₀ (Sum.inl w)) (min_le_right _ _))
    rw [hb, map_zero, zero_sub, norm_neg] at h1
    exact absurd h1 (lt_irrefl _)
  · exact hA w _ (lt_of_lt_of_le (hbA w) (le_trans (hi₀ (Sum.inl w)) (min_le_left _ _)))
  · exact hC y _ (lt_of_lt_of_le (hbC y) (hi₀ (Sum.inr y)))

end InverseGalois.CFT

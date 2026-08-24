/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Approximation.Places

/-!
# Weak approximation in the completions of a number field

Weak approximation places an element of the field near prescribed elements *of the field* at
finitely many places at once.  The completions add nothing to this, because the field is dense in
each of them separately: a prescribed element of a completion is first replaced by an element of
the field near it, and the approximation is then carried out inside the field.

The result is the form in which approximation is used for the ideles, where a prescribed local
component is given at all the infinite places and at finitely many primes.

## Main results

* `InverseGalois.CFT.norm_algebraMap_infiniteCompletion`: the norm of an element of a number field
  in a completion at an infinite place is the value of that place.
* `InverseGalois.CFT.norm_algebraMap_adicCompletion`: the norm of an element of a number field in a
  completion at a prime is the value of the absolute value of that prime.
* `InverseGalois.CFT.exists_norm_sub_lt_completion`: **weak approximation in the completions**, that
  prescribed elements of the completions at all the infinite places and at finitely many primes are
  matched to any accuracy by a single element of the field.

## Tags

number field, weak approximation, completion, place
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField NumberField.RingOfIntegers.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-! ### The norm of an element of the field in a completion -/

omit [NumberField K] in
/-- The norm of an element of a number field in a completion at an infinite place is the value of
that place. -/
theorem norm_algebraMap_infiniteCompletion (w : InfinitePlace K) (x : K) :
    ‖algebraMap K w.Completion x‖ = w x := by
  have h := InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm x)
  rwa [RingEquiv.apply_symm_apply] at h

/-- The norm of an element of a number field in a completion at a prime is the value of the absolute
value of that prime. -/
theorem norm_algebraMap_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    ‖algebraMap K (v.adicCompletion K) x‖ = adicAbv v x :=
  FinitePlace.norm_def v x

omit [NumberField K] in
/-- A number field is dense in its completion at an infinite place. -/
theorem denseRange_algebraMap_infiniteCompletion (w : InfinitePlace K) :
    DenseRange (algebraMap K w.Completion) :=
  UniformSpace.Completion.denseRange_coe (α := WithAbs w.1)

/-- A number field is dense in its completion at a prime. -/
theorem denseRange_algebraMap_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    DenseRange (algebraMap K (v.adicCompletion K)) :=
  UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation K))

/-! ### Approximation in the completions -/

variable {Y : Type*} [Finite Y] {ι : Y → HeightOneSpectrum (𝓞 K)}

/-- **Weak approximation in the completions of a number field**: prescribed elements of the
completions at all the infinite places and at finitely many primes are matched to any accuracy by a
single element of the field. -/
theorem exists_norm_sub_lt_completion (hinj : Function.Injective ι)
    (a : ∀ w : InfinitePlace K, w.Completion) (c : ∀ y : Y, (ι y).adicCompletion K)
    {r : ℝ} (hr : 0 < r) :
    ∃ b : K, (∀ w : InfinitePlace K, ‖algebraMap K w.Completion b - a w‖ < r) ∧
      ∀ y : Y, ‖algebraMap K ((ι y).adicCompletion K) b - c y‖ < r := by
  have half : (0 : ℝ) < r / 2 := by positivity
  have hA : ∀ w : InfinitePlace K, ∃ t : K, ‖algebraMap K w.Completion t - a w‖ < r / 2 := by
    intro w
    obtain ⟨-, ⟨t, rfl⟩, ht⟩ := Metric.mem_closure_iff.mp
      (denseRange_algebraMap_infiniteCompletion w (a w)) (r / 2) half
    exact ⟨t, by rwa [← dist_eq_norm, dist_comm]⟩
  have hC : ∀ y : Y, ∃ t : K, ‖algebraMap K ((ι y).adicCompletion K) t - c y‖ < r / 2 := by
    intro y
    obtain ⟨-, ⟨t, rfl⟩, ht⟩ := Metric.mem_closure_iff.mp
      (denseRange_algebraMap_adicCompletion (ι y) (c y)) (r / 2) half
    exact ⟨t, by rwa [← dist_eq_norm, dist_comm]⟩
  choose a' ha' using hA
  choose c' hc' using hC
  obtain ⟨b, hb⟩ := exists_dist_lt_placeAbv hinj (Sum.elim a' c') half
  refine ⟨b, fun w => ?_, fun y => ?_⟩
  · have h1 : ‖algebraMap K w.Completion b - algebraMap K w.Completion (a' w)‖ < r / 2 := by
      rw [← map_sub, norm_algebraMap_infiniteCompletion]
      exact hb (Sum.inl w)
    calc ‖algebraMap K w.Completion b - a w‖
        ≤ ‖algebraMap K w.Completion b - algebraMap K w.Completion (a' w)‖
          + ‖algebraMap K w.Completion (a' w) - a w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < r / 2 + r / 2 := add_lt_add h1 (ha' w)
      _ = r := add_halves r
  · have h1 : ‖algebraMap K ((ι y).adicCompletion K) b
        - algebraMap K ((ι y).adicCompletion K) (c' y)‖ < r / 2 := by
      rw [← map_sub, norm_algebraMap_adicCompletion]
      exact hb (Sum.inr y)
    calc ‖algebraMap K ((ι y).adicCompletion K) b - c y‖
        ≤ ‖algebraMap K ((ι y).adicCompletion K) b
            - algebraMap K ((ι y).adicCompletion K) (c' y)‖
          + ‖algebraMap K ((ι y).adicCompletion K) (c' y) - c y‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < r / 2 + r / 2 := add_lt_add h1 (hc' y)
      _ = r := add_halves r

end InverseGalois.CFT

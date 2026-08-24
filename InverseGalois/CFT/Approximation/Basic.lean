/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Weak approximation for a finite family of absolute values

A finite family of nontrivial pairwise inequivalent absolute values on a field imposes independent
conditions: the field, embedded diagonally in the product of its copies carrying the topologies of
the members of the family, is dense.

The proof is the classical one.  For each index there is an element which the corresponding absolute
value makes large and every other absolute value makes small, so the powers of that element give a
sequence of idempotent-like weights, close to one at its own index and close to zero elsewhere.
Weighting a prescribed target at each index by the corresponding sequence produces a sequence of
elements of the field converging to the target in every member of the family at once.

## Main results

* `InverseGalois.CFT.denseRange_algebraMap_withAbs`: **weak approximation**, that a field is dense
  in the product of its copies carrying the topologies of a finite family of nontrivial pairwise
  inequivalent absolute values.
* `InverseGalois.CFT.exists_dist_lt_withAbs`: the same, read as the simultaneous solution of finitely
  many approximation conditions.

## Tags

weak approximation, absolute value, place, Artin-Whaples
-/

namespace InverseGalois.CFT

open Filter Topology

variable {K : Type*} [Field K] {ι : Type*} [Finite ι] {v : ι → AbsoluteValue K ℝ}

/-- **Weak approximation.**  A field is dense in the product of its copies carrying the topologies
of a finite family of nontrivial pairwise inequivalent absolute values. -/
theorem denseRange_algebraMap_withAbs (hnt : ∀ i, (v i).IsNontrivial)
    (hpw : Pairwise fun i j => ¬(v i).IsEquiv (v j)) :
    DenseRange (algebraMap K (∀ i, WithAbs (v i))) := by
  classical
  have := Fintype.ofFinite ι
  intro z
  choose a hx using AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv hnt hpw
  set y : ℕ → K := fun n => ∑ i, 1 / (1 + (a i)⁻¹ ^ n) * WithAbs.equiv (v i) (z i) with hy
  have key : atTop.Tendsto (fun n (i : ι) => (WithAbs.equiv (v i)).symm (y n)) (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u => ?_
    simp_rw [← Fintype.sum_pi_single u z, hy, map_sum, map_mul]
    refine tendsto_finset_sum _ fun w _ => ?_
    by_cases hw : u = w
    · rw [← hw, Pi.single_apply u (z u), if_pos rfl]
      have h1 : v u (a u)⁻¹ < 1 := by simpa [← inv_pow, inv_lt_one_iff₀] using .inr (hx u).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one h1).mul_const (z u)
    · simp only [Pi.single_apply w (z w), hw, if_false]
      have hne : a w ≠ 0 := fun ha => by
        have hlt := (hx w).1
        rw [ha, map_zero] at hlt
        linarith
      have h1 : 1 < v u (a w)⁻¹ := by
        simpa [one_lt_inv_iff₀] using ⟨hne, (hx w).2 u hw⟩
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 <|
        (v u).tendsto_div_one_add_pow_nhds_zero h1).mul_const ((WithAbs.equiv (v u)).symm _)
  exact mem_closure_of_tendsto key (Eventually.of_forall fun n => ⟨y n, rfl⟩)

/-- **Weak approximation, read as the simultaneous solution of finitely many approximation
conditions**: a prescribed target at each member of the family is matched to any accuracy by a
single element of the field. -/
theorem exists_dist_lt_withAbs (hnt : ∀ i, (v i).IsNontrivial)
    (hpw : Pairwise fun i j => ¬(v i).IsEquiv (v j)) (z : ∀ _ : ι, K) {r : ℝ} (hr : 0 < r) :
    ∃ b : K, ∀ i, v i (b - z i) < r := by
  have := Fintype.ofFinite ι
  set Z : ∀ i, WithAbs (v i) := fun i => (WithAbs.equiv (v i)).symm (z i) with hZ
  obtain ⟨-, ⟨c, rfl⟩, hlt⟩ :=
    Metric.mem_closure_iff.mp (denseRange_algebraMap_withAbs hnt hpw Z) r hr
  refine ⟨c, fun i => ?_⟩
  have h1 := lt_of_le_of_lt (dist_le_pi_dist Z (algebraMap K (∀ j, WithAbs (v j)) c) i) hlt
  rw [dist_comm, dist_eq_norm, WithAbs.norm_eq_abv, map_sub] at h1
  simpa [hZ] using h1

end InverseGalois.CFT

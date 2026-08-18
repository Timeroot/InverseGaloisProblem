/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Combine

/-!
# One function of moderate growth separating prescribed pairs of points

A single pair of distinct points of a covering is separated by some function of moderate growth;
finitely many pairs are separated by finitely many functions, one each.  A generic linear
combination of those functions separates every one of the pairs at once: for each pair the
combination that fails is a root of a polynomial in the coefficient whose leading behaviour is
governed by the function chosen for that very pair, so the polynomial is not zero, and the plane
has more points than the roots of a finite product of nonzero polynomials.

Unlike the combination of `RET/Analytic/Combine.lean`, the pairs of points here are prescribed:
nothing is chosen by the argument, so the resulting function can be asked to separate the fibres
over a prescribed finite set of points of the base.

## Main results

* `Rigidity.RET.exists_forall_ne_of_pairs` — finitely many pairs of points, each separated by some
  function of moderate growth, are all separated by a single one.
* `Rigidity.RET.smul_eq_self_forall` — a deck transformation of a connected covering fixing one
  point fixes every point.
* `Rigidity.RET.smul_ne_self` — a nontrivial deck transformation of a connected covering moves
  every point, so the pairs of distinct points of a fibre are the pairs of distinct deck
  transformations.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

section SeparatePoints

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {S : Finset ℂ}

/-- **Finitely many pairs of points of a covering, each separated by some function of moderate
growth, are all separated by a single function of moderate growth.**

The functions chosen for the individual pairs are combined linearly with the powers of one
coefficient; the coefficients for which the combination fails on a given pair are the roots of a
polynomial whose coefficient in the degree attached to that pair is the difference the function
chosen for it produces, hence a nonzero polynomial. -/
theorem exists_forall_ne_of_pairs (hf : IsLocalHomeomorph f) {ι : Type*} [Fintype ι]
    {u v : ι → Y} (hsep : ∀ i : ι, ∃ F ∈ coverRing hf S, F (u i) ≠ F (v i)) :
    ∃ F ∈ coverRing hf S, ∀ i : ι, F (u i) ≠ F (v i) := by
  classical
  choose Fc hFc hFcne using hsep
  -- an enumeration of the pairs by exponents
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set deg : ι → ℕ := fun i => (e i : ℕ) with hdeg
  have hdeginj : Function.Injective deg := fun i j h => e.injective (Fin.ext h)
  -- the differences to be made nonzero, recorded as polynomials in the coefficient
  set p : ι → ℂ[X] := fun j => ∑ i : ι, C (Fc i (u j) - Fc i (v j)) * X ^ deg i with hp
  have hcoeff : ∀ j i₀ : ι, (p j).coeff (deg i₀) = Fc i₀ (u j) - Fc i₀ (v j) := by
    intro j i₀
    rw [hp, finset_sum_coeff, Finset.sum_eq_single i₀]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro i _ hii
      have hne : deg i₀ ≠ deg i := fun h => hii (hdeginj h.symm)
      rw [coeff_C_mul, coeff_X_pow, if_neg hne, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  have hpne : ∀ j : ι, p j ≠ 0 := by
    intro j hzero
    refine hFcne j (sub_eq_zero.1 ?_)
    rw [← hcoeff j j, hzero, coeff_zero]
  -- a coefficient avoiding every failure
  set Q : ℂ[X] := ∏ j : ι, p j with hQ
  have hQne : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hpne j
  obtain ⟨t, ht⟩ := ((Polynomial.finite_setOf_isRoot hQne).infinite_compl).nonempty
  have hteval : ∀ j : ι, (p j).eval t ≠ 0 := by
    intro j hzero
    refine ht ?_
    show Q.IsRoot t
    rw [IsRoot, hQ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) hzero
  -- the linear combination
  refine ⟨fun y => ∑ i : ι, t ^ deg i * Fc i y, ?_, fun j hj => hteval j ?_⟩
  · have hrw : (fun y : Y => ∑ i : ι, t ^ deg i * Fc i y)
        = ∑ i : ι, (fun y : Y => t ^ deg i * Fc i y) := by
      funext y
      rw [Finset.sum_apply]
    rw [hrw]
    refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ (hFc i)
    exact const_mem_coverRing hf S _
  · have hdiff : ∑ i : ι, (t ^ deg i * Fc i (u j) - t ^ deg i * Fc i (v j)) = 0 := by
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.2 hj
    rw [hp, eval_finset_sum]
    calc ∑ i : ι, (C (Fc i (u j) - Fc i (v j)) * X ^ deg i).eval t
        = ∑ i : ι, (t ^ deg i * Fc i (u j) - t ^ deg i * Fc i (v j)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [eval_mul, eval_C, eval_pow, eval_X]
          ring
      _ = 0 := hdiff

end SeparatePoints

/-! ### The deck group acts freely -/

section Free

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [PreconnectedSpace Y] {f : Y → ℂ}
variable {H : Type*} [Group H] [MulAction H Y] [ContinuousConstSMul H Y] [IsOverBase H f]

/-- **A deck transformation of a connected covering fixing one point fixes every point.**

A deck transformation and the identity are two lifts of the projection to the plane along a
locally injective separated map; on a connected total space two such lifts agreeing at one point
agree everywhere. -/
theorem smul_eq_self_forall (hf : IsLocalHomeomorph f) {a : H} {y₀ : Y} (h : a • y₀ = y₀)
    (y : Y) : a • y = y := by
  have hlift : (fun z : Y => a • z) = (id : Y → Y) :=
    (T2Space.isSeparatedMap f).eq_of_comp_eq hf.isLocallyInjective (continuous_const_smul a)
      continuous_id (funext fun z => IsOverBase.smul_eq a z) y₀ h
  exact congrFun hlift y

/-- **A nontrivial deck transformation of a connected covering moves every point.**

A deck transformation fixing a point is the identity on the whole covering, and a faithful action
makes it the identity of the group. -/
theorem smul_ne_self [FaithfulSMul H Y] (hf : IsLocalHomeomorph f) {a : H} (ha : a ≠ 1) (y : Y) :
    a • y ≠ y := by
  intro h
  refine ha (eq_of_smul_eq_smul (α := Y) fun z => ?_)
  rw [one_smul]
  exact smul_eq_self_forall hf h z

end Free

end Rigidity.RET

end

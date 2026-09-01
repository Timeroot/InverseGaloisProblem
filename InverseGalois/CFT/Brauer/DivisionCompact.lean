/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.DivisionInteger

/-!
# A division algebra over a local field is proper

Let `K` be a nonarchimedean local field, that is, a field complete with respect to a nontrivial
nonarchimedean absolute value whose closed balls are compact, and let `D` be a finite-dimensional
division algebra over `K`.  The absolute value of `D` makes it a normed division ring over `K`, and
a finite-dimensional normed space over a locally compact field is again locally compact.  So the
integers of `D` are compact, and being covered by the open balls of radius one around their own
points they are covered by finitely many of them.

That last statement is the form in which the compactness is used: it says exactly that the residue
ring of `D` is finite, without mentioning quotients.

## Main definitions

* `InverseGalois.CFT.divisionAbsoluteValue`: the absolute value of `D`, bundled.
* `InverseGalois.CFT.divisionNormedDivisionRing`: the normed division ring structure it defines.

## Main results

* `InverseGalois.CFT.mem_of_forall_exists_divisionNorm_sub_lt`: **a subspace of `D` is closed for
  the absolute value.**
* `InverseGalois.CFT.exists_finset_divisionNorm_sub_lt_one`: **finitely many elements of the
  integers of `D` meet every ball of radius one centred in the integers.**

## Tags

division algebra, absolute value, local field, proper space, compactness
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u

open Module

namespace InverseGalois.CFT

section Normed

variable {K D : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

variable (K D) in
/-- The absolute value of a finite-dimensional division algebra over a complete nonarchimedean
field, bundled as an `AbsoluteValue`. -/
noncomputable def divisionAbsoluteValue : AbsoluteValue D ℝ where
  toFun := divisionNorm K D
  map_mul' := divisionNorm_mul
  nonneg' := divisionNorm_nonneg
  eq_zero' _ := divisionNorm_eq_zero_iff
  add_le' x y := (divisionNorm_isNonarchimedean x y).trans
    (max_le_add_of_nonneg (divisionNorm_nonneg x) (divisionNorm_nonneg y))

@[simp]
theorem divisionAbsoluteValue_apply (x : D) :
    divisionAbsoluteValue K D x = divisionNorm K D x := rfl

variable (K D) in
/-- The normed division ring structure on a finite-dimensional division algebra over a complete
nonarchimedean field. -/
noncomputable abbrev divisionNormedDivisionRing : NormedDivisionRing D where
  norm := divisionNorm K D
  dist x y := divisionNorm K D (x - y)
  dist_eq _ _ := rfl
  dist_self x := by simp only [sub_self, divisionNorm_zero]
  dist_comm x y := (divisionAbsoluteValue K D).map_sub x y
  dist_triangle x y z := (divisionAbsoluteValue K D).sub_le x y z
  edist_dist _ _ := rfl
  eq_of_dist_eq_zero h := sub_eq_zero.1 (divisionNorm_eq_zero_iff.1 h)
  norm_mul := divisionNorm_mul

variable (K D) in
/-- **A subspace of a finite-dimensional division algebra over a complete nonarchimedean field is
closed for the absolute value**: an element approximated arbitrarily well by a subspace belongs to
it.  Every subspace is finite-dimensional, and a finite-dimensional subspace of a normed space over
a complete field is closed. -/
theorem mem_of_forall_exists_divisionNorm_sub_lt (V : Submodule K D) {x : D}
    (hx : ∀ ε : ℝ, 0 < ε → ∃ v ∈ V, divisionNorm K D (x - v) < ε) : x ∈ V := by
  classical
  have hfd : FiniteDimensional K D := inferInstance
  letI : NormedDivisionRing D := divisionNormedDivisionRing K D
  have hdist : ∀ a b : D, dist a b = divisionNorm K D (a - b) := fun _ _ => rfl
  letI : NormedAlgebra K D :=
    { (inferInstance : Algebra K D) with
      norm_smul_le := fun r z => le_of_eq (by
        show divisionNorm K D (r • z) = ‖r‖ * divisionNorm K D z
        rw [Algebra.smul_def, divisionNorm_mul, divisionNorm_algebraMap]) }
  haveI : FiniteDimensional K D := hfd
  have hclosed : IsClosed (V : Set D) := V.closed_of_finiteDimensional
  have hmem : x ∈ closure (V : Set D) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨v, hv, hlt⟩ := hx ε hε
    exact ⟨v, hv, by rw [hdist]; exact hlt⟩
  rwa [hclosed.closure_eq] at hmem

end Normed

section Proper

variable {K D : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

variable (K D) in
/-- **The integers of a division algebra over a local field are covered by finitely many balls of
radius one.**  The integers are the closed unit ball, which is compact because a finite-dimensional
normed space over a locally compact field is proper, and the open unit balls around its points form
an open cover of it. -/
theorem exists_finset_divisionNorm_sub_lt_one :
    ∃ T : Finset D, (∀ t ∈ T, divisionNorm K D t ≤ 1) ∧
      ∀ x : D, divisionNorm K D x ≤ 1 → ∃ t ∈ T, divisionNorm K D (x - t) < 1 := by
  classical
  have hfd : FiniteDimensional K D := inferInstance
  letI : NormedDivisionRing D := divisionNormedDivisionRing K D
  have hdist : ∀ x y : D, dist x y = divisionNorm K D (x - y) := fun _ _ => rfl
  letI : NormedAlgebra K D :=
    { (inferInstance : Algebra K D) with
      norm_smul_le := fun r x => le_of_eq (by
        show divisionNorm K D (r • x) = ‖r‖ * divisionNorm K D x
        rw [Algebra.smul_def, divisionNorm_mul, divisionNorm_algebraMap]) }
  haveI : FiniteDimensional K D := hfd
  haveI : ProperSpace D := FiniteDimensional.proper K D
  have hcpt : IsCompact (Metric.closedBall (0 : D) 1) := isCompact_closedBall 0 1
  have hcover : Metric.closedBall (0 : D) 1 ⊆
      ⋃ y ∈ Metric.closedBall (0 : D) 1, Metric.ball y 1 := fun y hy =>
    Set.mem_biUnion hy (Metric.mem_ball_self one_pos)
  obtain ⟨T, hTsub, hTfin, hT⟩ :=
    hcpt.elim_finite_subcover_image (fun _ _ => Metric.isOpen_ball) hcover
  refine ⟨hTfin.toFinset, fun t ht => ?_, fun x hx => ?_⟩
  · have := hTsub (hTfin.mem_toFinset.1 ht)
    rw [Metric.mem_closedBall, hdist, sub_zero] at this
    exact this
  · have hxmem : x ∈ Metric.closedBall (0 : D) 1 := by
      rw [Metric.mem_closedBall, hdist, sub_zero]
      exact hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 (hT hxmem)
    rw [Metric.mem_ball, hdist] at hxt
    exact ⟨t, hTfin.mem_toFinset.2 ht, hxt⟩

end Proper

end InverseGalois.CFT

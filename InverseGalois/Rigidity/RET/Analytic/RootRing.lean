/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootMonodromy
import InverseGalois.Rigidity.RET.Analytic.RootBound
import InverseGalois.Rigidity.RET.Analytic.RootSection
import InverseGalois.Rigidity.RET.Analytic.Separating

/-!
# The coordinate of an algebraic covering is a function of moderate growth

A covering of a punctured plane cut out by an equation carries an obvious candidate for the
function the Galois correspondence for a covering asks of the analysis: the second coordinate.  It
is holomorphic, because at a simple root the equation determines the root as a holomorphic function
of the parameter; it is of moderate growth, because the Cauchy bound keeps the roots of a monic
family under a polynomial in the parameter; and it separates the points of every fibre for the
cheapest possible reason, since two points of the root variety over the same parameter with the
same coordinate are the same point.

So on a covering that comes from an equation the requirement isolated in `RET/Analytic/Wall.lean`
is a theorem, with nothing to prove about the group: a deck transformation which no function of
moderate growth moves fixes every point, and the only hypothesis needed is that the group acts
faithfully.  What the requirement asks in general is therefore exactly that an arbitrary
topological covering of a punctured plane comes from an equation.

## Main definitions

* `Rigidity.RET.RootTotal` — the part of the root variety lying over the punctured plane.
* `Rigidity.RET.rootBase`, `Rigidity.RET.rootCoord` — its two coordinates.

## Main results

* `Rigidity.RET.isLocalHomeomorph_rootBase` — the parameter is a local coordinate on the covering.
* `Rigidity.RET.isHolo_rootCoord`, `Rigidity.RET.isModerate_rootCoord`,
  `Rigidity.RET.rootCoord_mem_coverRing` — the second coordinate is a function of moderate growth.
* `Rigidity.RET.exists_ne_rootCoord` — every nontrivial deck transformation of an algebraic
  covering moves it.
* `Rigidity.RET.hasSeparatingFunction_rootTotal` — an algebraic covering with a free point carries
  a separating function.
-/

open Polynomial Topology

noncomputable section

namespace Rigidity.RET

open Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ}

/-! ### The two coordinates of an algebraic covering -/

/-- **The part of the root variety of a family of equations lying over the punctured plane.** -/
abbrev RootTotal (P : Polynomial (Polynomial ℂ)) (S : Finset ℂ) : Type :=
  ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))

/-- **The parameter of a point of an algebraic covering.** -/
def rootBase (P : Polynomial (Polynomial ℂ)) (S : Finset ℂ) : RootTotal P S → ℂ :=
  fun y => ((y : ↥(rootVariety P)) : ℂ × ℂ).1

/-- **The coordinate of a point of an algebraic covering**: the root of the equation it names. -/
def rootCoord (P : Polynomial (Polynomial ℂ)) (S : Finset ℂ) : RootTotal P S → ℂ :=
  fun y => ((y : ↥(rootVariety P)) : ℂ × ℂ).2

theorem continuous_rootBase : Continuous (rootBase P S) :=
  continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_rootCoord : Continuous (rootCoord P S) :=
  continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)

/-- **The coordinate of a point of the covering is a root of the equation at its parameter.** -/
theorem spec_eval_rootCoord (y : RootTotal P S) :
    (spec P (rootBase P S y)).eval (rootCoord P S y) = 0 :=
  (y : ↥(rootVariety P)).2

/-- **The parameter of a point of the covering avoids the punctures.** -/
theorem rootBase_notMem (y : RootTotal P S) : rootBase P S y ∉ (S : Set ℂ) := y.2

/-- **A point of an algebraic covering is determined by its parameter and its coordinate.** -/
theorem eq_of_rootBase_eq_of_rootCoord_eq {y y' : RootTotal P S}
    (h₁ : rootBase P S y = rootBase P S y') (h₂ : rootCoord P S y = rootCoord P S y') : y = y' :=
  Subtype.ext (Subtype.ext (Prod.ext h₁ h₂))

/-- **The parameter is a local coordinate on an algebraic covering**: the root projection is a
covering map onto the punctured plane, and the punctured plane is open in the plane. -/
theorem isLocalHomeomorph_rootBase (hP : P.Monic)
    (hsep : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) : IsLocalHomeomorph (rootBase P S) :=
  ((S.finite_toSet.isClosed.isOpen_compl).isOpenEmbedding_subtypeVal.isLocalHomeomorph).comp
    (isCoveringMap_puncturedProj hP hsep).isLocalHomeomorph

/-! ### The Cauchy bound without a hypothesis on the degree -/

/-- **The roots of a monic family are bounded by a polynomial in the parameter.**  A family of
degree zero is the constant `1`, which has no roots at all. -/
theorem exists_root_bound_of_monic (hP : P.Monic) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
      ∀ z w : ℂ, (spec P z).eval w = 0 → ‖w‖ ≤ C * (1 + ‖z‖) ^ d := by
  rcases Nat.eq_zero_or_pos P.natDegree with hdeg | hdeg
  · refine ⟨0, 0, le_refl 0, fun z w hw => absurd hw ?_⟩
    have hone : spec P z = 1 :=
      eq_one_of_monic_natDegree_zero (spec_monic hP z) ((natDegree_spec hP z).trans hdeg)
    rw [hone]
    simp
  · exact exists_root_bound P hP hdeg

/-! ### The coordinate is a function of moderate growth -/

/-- **The coordinate of an algebraic covering is holomorphic.**  Read in any local coordinate the
covering supplies, it is a continuous root of the equation at a parameter where the equation is
separable, and such a root depends holomorphically on the parameter. -/
theorem isHolo_rootCoord (hP : P.Monic) (hsep : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) :
    IsHolo (rootBase P S) (rootCoord P S) := by
  intro y
  obtain ⟨e, hy, hfe⟩ := isLocalHomeomorph_rootBase (S := S) hP hsep y
  refine ⟨e, ⟨hy, hfe⟩, ?_⟩
  have hbase : ∀ z ∈ e.target, rootBase P S (e.symm z) = z := by
    intro z hz
    rw [hfe]
    exact e.right_inv hz
  have hcont : ContinuousOn (fun z => rootCoord P S (e.symm z)) e.target :=
    continuous_rootCoord.comp_continuousOn e.continuousOn_invFun
  have hroot : ∀ z ∈ e.target, (spec P z).eval (rootCoord P S (e.symm z)) = 0 := by
    intro z hz
    have hz' := spec_eval_rootCoord (e.symm z)
    rwa [hbase z hz] at hz'
  have hdiff : DifferentiableOn ℂ (fun z => rootCoord P S (e.symm z)) e.target := by
    intro z hz
    have hzS : z ∉ (S : Set ℂ) := by
      have hz' := rootBase_notMem (e.symm z)
      rwa [hbase z hz] at hz'
    refine (differentiableAt_of_isRoot e.open_target hcont hroot hz ?_).differentiableWithinAt
    exact Polynomial.Separable.aeval_derivative_ne_zero (hsep z hzS) (hroot z hz)
  refine hdiff.analyticAt ?_
  rw [hfe]
  exact e.open_target.mem_nhds (e.map_source hy)

/-- **The coordinate of an algebraic covering is of moderate growth.**  The Cauchy bound holds
everywhere at once: near a puncture it bounds the coordinate outright, and at infinity it bounds it
by a power of the parameter. -/
theorem isModerate_rootCoord (hP : P.Monic) : IsModerate (rootBase P S) S (rootCoord P S) := by
  obtain ⟨C, d, hC, hbd⟩ := exists_root_bound_of_monic hP
  constructor
  · intro s _
    refine ⟨1, one_pos, C * (2 + ‖s‖) ^ d, by positivity, 0, fun y hy => ?_⟩
    rw [pow_zero, mul_one]
    refine (hbd _ _ (spec_eval_rootCoord y)).trans ?_
    have hz : ‖rootBase P S y‖ ≤ 1 + ‖s‖ := by
      have h1 : dist (rootBase P S y) s < 1 := Metric.mem_ball.1 hy.1
      have h2 : ‖rootBase P S y‖ - ‖s‖ ≤ ‖rootBase P S y - s‖ := norm_sub_norm_le _ _
      rw [← dist_eq_norm] at h2
      linarith
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) d) hC
  · refine ⟨C * 2 ^ d, 1, d, by positivity, fun y hy => ?_⟩
    refine (hbd _ _ (spec_eval_rootCoord y)).trans ?_
    have hle : (1 : ℝ) + ‖rootBase P S y‖ ≤ 2 * ‖rootBase P S y‖ := by linarith
    calc C * (1 + ‖rootBase P S y‖) ^ d
        ≤ C * (2 * ‖rootBase P S y‖) ^ d :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hle d) hC
      _ = C * 2 ^ d * ‖rootBase P S y‖ ^ d := by rw [mul_pow]; ring

/-- **The coordinate of an algebraic covering belongs to its ring of functions.** -/
theorem rootCoord_mem_coverRing (hP : P.Monic)
    (hsep : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) :
    rootCoord P S ∈ coverRing (isLocalHomeomorph_rootBase hP hsep) S :=
  ⟨isHolo_rootCoord hP hsep, isModerate_rootCoord hP⟩

/-! ### The requirement of the Galois correspondence, on an algebraic covering -/

variable {H : Type*} [Group H] [MulAction H (RootTotal P S)]

/-- **Two points of an algebraic covering with the same parameter and the same coordinate are the
same point**, so the coordinate separates the points of every fibre. -/
theorem smul_eq_of_rootCoord_eq [IsOverBase H (rootBase P S)] {a b : H} {y : RootTotal P S}
    (h : rootCoord P S (a • y) = rootCoord P S (b • y)) : a • y = b • y :=
  eq_of_rootBase_eq_of_rootCoord_eq
    ((IsOverBase.smul_eq a y).trans (IsOverBase.smul_eq b y).symm) h

/-- **Every nontrivial deck transformation of an algebraic covering moves a function of moderate
growth**: it moves some point of the covering, and the coordinate of that point is moved with it.

This is what the requirement isolated in `RET/Analytic/Wall.lean` asks, on a covering that comes
from an equation; the only hypothesis on the group is that it acts faithfully. -/
theorem exists_ne_rootCoord (hP : P.Monic) (hsep : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    [FaithfulSMul H (RootTotal P S)] [IsOverBase H (rootBase P S)] (a : H) (ha : a ≠ 1) :
    ∃ F ∈ coverRing (isLocalHomeomorph_rootBase hP hsep) S,
      ∃ y : RootTotal P S, F (a • y) ≠ F y := by
  refine ⟨rootCoord P S, rootCoord_mem_coverRing hP hsep, ?_⟩
  by_contra hcon
  push_neg at hcon
  refine ha (eq_of_smul_eq_smul (α := RootTotal P S) fun y => ?_)
  rw [one_smul]
  have h : rootCoord P S (a • y) = rootCoord P S ((1 : H) • y) := by
    rw [one_smul]; exact hcon y
  rw [smul_eq_of_rootCoord_eq h, one_smul]

/-- **An algebraic covering carries a separating function** as soon as the deck group fixes no
point of some fibre: the coordinate is one. -/
theorem hasSeparatingFunction_rootTotal (hP : P.Monic)
    (hsep : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) [IsOverBase H (rootBase P S)]
    {y₀ : RootTotal P S} (hfree : ∀ a : H, a • y₀ = y₀ → a = 1) :
    HasSeparatingFunction (isLocalHomeomorph_rootBase hP hsep) S H := by
  refine ⟨rootCoord P S, rootCoord_mem_coverRing hP hsep, y₀, fun a b hab => ?_⟩
  have h : (b⁻¹ * a) • y₀ = y₀ := by
    rw [mul_smul, smul_eq_of_rootCoord_eq hab, ← mul_smul, inv_mul_cancel, one_smul]
  have := hfree _ h
  rw [inv_mul_eq_one] at this
  exact this.symm

end Rigidity.RET

end

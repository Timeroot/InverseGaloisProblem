/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.SquareLoop
import InverseGalois.Rigidity.RET.Pi1.Topological.PushLoop

/-!
# The boundary of a small square winds once around the puncture

`SquareLoop.lean` shows that the boundary of a square centred at the puncture generates the
fundamental group of a punctured disc.  Combined with the pushforward of `PushLoop.lean`, that is
exactly the definition of a loop winding once around the puncture, read in any region containing
the punctured disc: no path back to the basepoint is needed, because the basepoint of the loop is
a corner of the square itself.

The four sides of the square are the four quarters `sqSide_subset` at the angles
`0, π/2, π, 3π/2`, which are spelled out here as the corner identities `sqCorner₀`–`sqCorner₄`.

## Main results

* `Rigidity.RET.sqSideAB`, `sqSideBC`, `sqSideCD`, `sqSideDA` — the four sides of the square
  centred at the puncture stay inside the punctured disc.
* `Rigidity.RET.isPunctureLoop_boxLoop` — the boundary of a small square centred at `s` winds once
  around `s`.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### The corners of the square as points of the circle -/

/-- The first corner of the square, at angle `0`. -/
theorem sqCorner₀ (s w : ℂ) : (s + w : ℂ) = s + Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * w := by
  rw [show ((0 : ℝ) : ℂ) * Complex.I = 0 by push_cast; ring, Complex.exp_zero]
  ring

/-- The second corner of the square, at angle `π / 2`. -/
theorem sqCorner₁ (s w : ℂ) : (s + Complex.I * w : ℂ)
    = s + Complex.exp (((0 + Real.pi / 2 : ℝ) : ℂ) * Complex.I) * w := by
  rw [show ((0 + Real.pi / 2 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) / 2 * Complex.I by
    push_cast; ring, Complex.exp_pi_div_two_mul_I]

/-- The third corner of the square, at angle `π`. -/
theorem sqCorner₂ (s w : ℂ) : (s - w : ℂ)
    = s + Complex.exp (((0 + Real.pi / 2 + Real.pi / 2 : ℝ) : ℂ) * Complex.I) * w := by
  rw [show ((0 + Real.pi / 2 + Real.pi / 2 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_pi_mul_I]
  ring

/-- The fourth corner of the square, at angle `3π / 2`. -/
theorem sqCorner₃ (s w : ℂ) : (s - Complex.I * w : ℂ)
    = s + Complex.exp (((0 + Real.pi / 2 + Real.pi / 2 + Real.pi / 2 : ℝ) : ℂ) * Complex.I)
      * w := by
  rw [show ((0 + Real.pi / 2 + Real.pi / 2 + Real.pi / 2 : ℝ) : ℂ) * Complex.I
      = (Real.pi : ℂ) * Complex.I + (Real.pi : ℂ) / 2 * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
  ring

/-- The first corner of the square again, at angle `2π`. -/
theorem sqCorner₄ (s w : ℂ) : (s + w : ℂ)
    = s + Complex.exp
      (((0 + Real.pi / 2 + Real.pi / 2 + Real.pi / 2 + Real.pi / 2 : ℝ) : ℂ) * Complex.I)
      * w := by
  rw [show ((0 + Real.pi / 2 + Real.pi / 2 + Real.pi / 2 + Real.pi / 2 : ℝ) : ℂ) * Complex.I
      = 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring, Complex.exp_two_pi_mul_I]
  ring

/-! ### The four sides -/

/-- The bottom side of the square centred at the puncture stays inside the punctured disc. -/
theorem sqSideAB {s w : ℂ} {ρ : ℝ} (hw : w ≠ 0) (hwρ : ‖w‖ < ρ) :
    seg (s + w) (s + Complex.I * w) ⊆ puncturedDisc s ρ :=
  sqSide_subset hw hwρ 0 (sqCorner₀ s w) (sqCorner₁ s w)

/-- The right side of the square centred at the puncture stays inside the punctured disc. -/
theorem sqSideBC {s w : ℂ} {ρ : ℝ} (hw : w ≠ 0) (hwρ : ‖w‖ < ρ) :
    seg (s + Complex.I * w) (s - w) ⊆ puncturedDisc s ρ :=
  sqSide_subset hw hwρ (0 + Real.pi / 2) (sqCorner₁ s w) (sqCorner₂ s w)

/-- The top side of the square centred at the puncture stays inside the punctured disc. -/
theorem sqSideCD {s w : ℂ} {ρ : ℝ} (hw : w ≠ 0) (hwρ : ‖w‖ < ρ) :
    seg (s - w) (s - Complex.I * w) ⊆ puncturedDisc s ρ :=
  sqSide_subset hw hwρ (0 + Real.pi / 2 + Real.pi / 2) (sqCorner₂ s w) (sqCorner₃ s w)

/-- The left side of the square centred at the puncture stays inside the punctured disc. -/
theorem sqSideDA {s w : ℂ} {ρ : ℝ} (hw : w ≠ 0) (hwρ : ‖w‖ < ρ) :
    seg (s - Complex.I * w) (s + w) ⊆ puncturedDisc s ρ :=
  sqSide_subset hw hwρ (0 + Real.pi / 2 + Real.pi / 2 + Real.pi / 2) (sqCorner₃ s w)
    (sqCorner₄ s w)

/-! ### The boundary of a small square is a puncture loop -/

/-- **The boundary of a small square centred at a puncture winds once around it.** -/
theorem isPunctureLoop_boxLoop {X : Set ℂ} {s w : ℂ} {ρ : ℝ} (hsub : puncturedDisc s ρ ⊆ X)
    (hw : w ≠ 0) (hwρ : ‖w‖ < ρ)
    (hab : seg (s + w) (s + Complex.I * w) ⊆ X)
    (hbc : seg (s + Complex.I * w) (s - w) ⊆ X)
    (hcd : seg (s - w) (s - Complex.I * w) ⊆ X)
    (hda : seg (s - Complex.I * w) (s + w) ⊆ X) :
    IsPunctureLoop X s (hab (left_mem_seg _ _))
      (FundamentalGroup.fromPath (boxLoop hab hbc hcd hda)) := by
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg w) hwρ
  refine ⟨ρ, hsub, ⟨s + w, sqSideAB hw hwρ (left_mem_seg _ _)⟩,
    FundamentalGroup.fromPath
      (boxLoop (sqSideAB hw hwρ) (sqSideBC hw hwρ) (sqSideCD hw hwρ) (sqSideDA hw hwρ)),
    Path.refl _, hρ, zpowers_boxLoop_eq_top hw hwρ _ _ _ _, ?_⟩
  symm
  refine (fundamentalGroupMulEquivOfPath_refl _ _).trans ?_
  show FundamentalGroup.fromPath
      ((boxLoop (sqSideAB hw hwρ) (sqSideBC hw hwρ) (sqSideCD hw hwρ) (sqSideDA hw hwρ)).map
        (subsetIncl hsub))
    = FundamentalGroup.fromPath (boxLoop hab hbc hcd hda)
  rw [map_boxLoop]

/-- The boundary of a small square centred at a puncture winds once around it, in the form where
the four vertices are given by equations. -/
theorem isPunctureLoop_boxLoop' {X : Set ℂ} {s w A B C D : ℂ} {ρ : ℝ}
    (hsub : puncturedDisc s ρ ⊆ X) (hw : w ≠ 0) (hwρ : ‖w‖ < ρ)
    (hA : A = s + w) (hB : B = s + Complex.I * w) (hC : C = s - w) (hD : D = s - Complex.I * w)
    (hab : seg A B ⊆ X) (hbc : seg B C ⊆ X) (hcd : seg C D ⊆ X) (hda : seg D A ⊆ X) :
    IsPunctureLoop X s (hab (left_mem_seg _ _))
      (FundamentalGroup.fromPath (boxLoop hab hbc hcd hda)) := by
  subst hA; subst hB; subst hC; subst hD
  exact isPunctureLoop_boxLoop hsub hw hwρ hab hbc hcd hda

end Rigidity.RET

end

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.CoverSymm
import InverseGalois.Rigidity.RET.Analytic.HoloCoeffs

/-!
# Interpolation along a fibre

A function on the total space of a covering is recovered from its values on a fibre by Lagrange
interpolation in a second function `g`, provided `g` takes distinct values there.  Written without
denominators the interpolant is

`T(X) = ∑ₐ F(a • y) ∏_{b ≠ a} (X - g (b • y))`,

whose value at `X = g y` is `F y` times `∏_{b ≠ 1} (g y - g (b • y))` — every other summand carries
the factor belonging to `b = 1`, which vanishes there.  That product is the derivative of the orbit
polynomial of `g` at `g y`, so the interpolation identity reads

`T(g y) = F y · P'(g y)`,  where `P` is the orbit polynomial of `g`.

The point of the interpolant is that it does not depend on which point of the fibre is used to
write it down: moving the point along its orbit permutes the summands and the factors of each
product.  So its coefficients are functions of the base point alone, and they are analytic there
whenever `F` and `g` are holomorphic — which exhibits `F` as a rational expression in `g` and the
base coordinate, the analytic form of the primitive element theorem.

## Main definitions

* `Rigidity.RET.interpPoly` — the interpolation polynomial of `F` in `g` along the orbit of a
  point.

## Main results

* `Rigidity.RET.interpPoly_smul` — the interpolant is constant along a fibre.
* `Rigidity.RET.eval_interpPoly_eq_mul` — the interpolation identity `T(g y) = F y · P'(g y)`.
* `Rigidity.RET.natDegree_interpPoly_lt` — the interpolant has degree less than the order of the
  group.
* `Rigidity.RET.exists_analytic_interpPoly_coeff` — its coefficients are analytic functions of the
  base point.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

section Defs

variable {Y : Type*} {g F : Y → ℂ} {H : Type*} [Group H] [Fintype H] [DecidableEq H]
  [MulAction H Y]

omit [DecidableEq H] in
/-- **The orbit polynomial as a product over the group.** -/
theorem orbitPoly_eq_prod (y : Y) :
    orbitPoly H g y = ∏ a : H, (X - C (g (a • y))) := by
  rw [orbitPoly, orbitValues, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

/-- **The interpolation polynomial of `F` in `g` along the orbit of a point**: the Lagrange
interpolant of the values of `F` on the orbit at the values of `g` there, cleared of its
denominators. -/
def interpPoly (H : Type*) [Group H] [Fintype H] [DecidableEq H] [MulAction H Y]
    (g F : Y → ℂ) (y : Y) : ℂ[X] :=
  ∑ a : H, C (F (a • y)) * ∏ b ∈ Finset.univ.erase a, (X - C (g (b • y)))

/-- **The interpolant has degree less than the order of the group**: each summand is a product of
one factor fewer than there are group elements. -/
theorem natDegree_interpPoly_lt (y : Y) :
    (interpPoly H g F y).natDegree < Fintype.card H := by
  have hcard : 1 ≤ Fintype.card H := Fintype.card_pos
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun a _ => ?_)
    (show Fintype.card H - 1 < Fintype.card H by omega)
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans (le_of_eq ?_)
  calc ∑ b ∈ Finset.univ.erase a, (X - C (g (b • y))).natDegree
      = ∑ _b ∈ Finset.univ.erase a, 1 :=
        Finset.sum_congr rfl fun b _ => natDegree_X_sub_C _
    _ = (Finset.univ.erase a).card := by simp
    _ = Fintype.card H - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]

/-- **The interpolant does not depend on the point of the fibre it is written at**: moving the
point along its orbit permutes the summands and, inside each of them, the factors. -/
theorem interpPoly_smul (c : H) (y : Y) :
    interpPoly H g F (c • y) = interpPoly H g F y := by
  refine Fintype.sum_equiv (Equiv.mulRight c) _ _ fun a => ?_
  have h1 : a • c • y = (a * c) • y := (mul_smul a c y).symm
  rw [h1]
  simp only [Equiv.coe_mulRight]
  congr 1
  refine Finset.prod_equiv (Equiv.mulRight c) (fun b => ?_) (fun b _ => ?_)
  · simp [Finset.mem_erase]
  · simp only [Equiv.coe_mulRight]
    rw [mul_smul]

/-- **The interpolation identity**: at the value of `g` the interpolant returns the value of `F`,
times the product of the differences of `g` from its values elsewhere on the orbit. -/
theorem eval_interpPoly (y : Y) :
    (interpPoly H g F y).eval (g y)
      = F y * ∏ b ∈ Finset.univ.erase (1 : H), (g y - g (b • y)) := by
  rw [interpPoly, eval_finset_sum, Finset.sum_eq_single (1 : H)]
  · simp [eval_prod]
  · intro a _ ha
    have h1 : (1 : H) ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨Ne.symm ha, Finset.mem_univ 1⟩
    rw [eval_mul, eval_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero h1 ?_)
    simp
  · intro h
    exact absurd (Finset.mem_univ (1 : H)) h

/-- **The derivative of the orbit polynomial at the value of the function** is the product of the
differences of that value from the other values on the orbit. -/
theorem eval_derivative_orbitPoly (y : Y) :
    (derivative (orbitPoly H g y)).eval (g y)
      = ∏ b ∈ Finset.univ.erase (1 : H), (g y - g (b • y)) := by
  rw [orbitPoly_eq_prod, derivative_prod_finset, eval_finset_sum, Finset.sum_eq_single (1 : H)]
  · simp [eval_prod]
  · intro a _ ha
    have h1 : (1 : H) ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨Ne.symm ha, Finset.mem_univ 1⟩
    rw [eval_mul, eval_prod]
    refine mul_eq_zero_of_left (Finset.prod_eq_zero h1 ?_) _
    simp
  · intro h
    exact absurd (Finset.mem_univ (1 : H)) h

/-- **The interpolation identity, in terms of the orbit polynomial**: the interpolant at the value
of `g` is the value of `F` times the derivative of the orbit polynomial there. -/
theorem eval_interpPoly_eq_mul (y : Y) :
    (interpPoly H g F y).eval (g y)
      = F y * (derivative (orbitPoly H g y)).eval (g y) := by
  rw [eval_interpPoly, eval_derivative_orbitPoly]

end Defs

section Analytic

variable {Y : Type*} [TopologicalSpace Y] {f g F : Y → ℂ}
variable {H : Type*} [Group H] [Fintype H] [DecidableEq H] [MulAction H Y]
  [ContinuousConstSMul H Y]

omit [Fintype H] [DecidableEq H] in
/-- **A holomorphic function stays holomorphic when read at the translate of the point by a group
element**, provided the group acts over the base. -/
theorem isHolo_comp_smul (hover : ∀ (a : H) (y : Y), f (a • y) = f y) (hF : IsHolo f F) (a : H) :
    IsHolo f fun y => F (a • y) := by
  intro y
  have hp : ∀ y' : Y, f ((Homeomorph.smul a : Y ≃ₜ Y) y') = f y' := by
    intro y'; simpa using hover a y'
  have := IsHoloAt.comp_homeomorph (f := f) (g := F) (y := y)
    (perm := (Homeomorph.smul a : Y ≃ₜ Y)) hp (hF _)
  simpa using this

/-- **The interpolant has holomorphic coefficients**: it is assembled from the values of `F` and
`g` along the orbit, all of them holomorphic. -/
theorem holoCoeffs_interpPoly (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y) (hg : IsHolo f g) (hF : IsHolo f F) :
    HoloCoeffs f (interpPoly H g F) := by
  show HoloCoeffs f fun y =>
    ∑ a : H, C (F (a • y)) * ∏ b ∈ Finset.univ.erase a, (X - C (g (b • y)))
  refine holoCoeffs_finset_sum hf _ fun a _ => ?_
  refine (holoCoeffs_C hf (isHolo_comp_smul hover hF a)).mul hf ?_
  exact holoCoeffs_finset_prod hf _ fun b _ =>
    (holoCoeffs_const hf X).sub (holoCoeffs_C hf (isHolo_comp_smul hover hg b))

/-- **Each coefficient of the interpolant is an analytic function of the base point.** -/
theorem exists_analytic_interpPoly_coeff (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (hF : IsHolo f F) (k : ℕ) :
    ∃ c : ℂ → ℂ, (∀ y, (interpPoly H g F y).coeff k = c (f y)) ∧ ∀ y, AnalyticAt ℂ c (f y) := by
  refine exists_analytic_of_isHolo_of_invariant hf (holoCoeffs_interpPoly hf hover hg hF k) ?_
  intro y y' hyy
  obtain ⟨b, rfl⟩ := htrans y y' hyy
  rw [interpPoly_smul]

end Analytic

end Rigidity.RET

end

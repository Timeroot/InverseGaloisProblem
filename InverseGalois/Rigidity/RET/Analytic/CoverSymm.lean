/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.CoverHolo

/-!
# The equation satisfied by a holomorphic function on a covering

A group of symmetries of a space lying over the plane, permuting each fibre simply transitively,
turns a holomorphic function on the total space into an algebraic function of the base: the
values the function takes on a fibre are the roots of a monic polynomial whose coefficients are
the elementary symmetric functions of those values, and those are functions of the base point
alone — they do not change when the fibre is traversed.  Being holomorphic upstairs and constant
on fibres, they are analytic downstairs.

This is the step that converts a covering into an equation.  Nothing here is specific to coverings
of the punctured plane; the hypotheses are that the projection is a local homeomorphism, that the
group acts over the base by homeomorphisms, and that each fibre is one orbit.

## Main definitions

* `Rigidity.RET.orbitValues` — the multiset of values a function takes on an orbit.
* `Rigidity.RET.orbitPoly` — the monic polynomial whose roots, with multiplicity, are those values.

## Main results

* `Rigidity.RET.eval_orbitPoly_self` — the function is a root of its own orbit polynomial.
* `Rigidity.RET.isHolo_esymm` — the elementary symmetric functions of the values on a fibre are
  holomorphic.
* `Rigidity.RET.exists_analytic_orbitPoly_coeff` — each coefficient of the orbit polynomial is an
  analytic function of the base point.
* `Rigidity.RET.exists_monic_analytic_of_isHolo` — a holomorphic function on the total space
  satisfies a monic equation of degree the order of the group, with coefficients analytic on the
  base.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

section Defs

variable {Y : Type*} {g : Y → ℂ} {H : Type*} [Group H] [Fintype H] [MulAction H Y]

/-- **The values a function takes on an orbit**, as a multiset with one entry per group element. -/
def orbitValues (H : Type*) [Group H] [Fintype H] [MulAction H Y] (g : Y → ℂ) (y : Y) :
    Multiset ℂ :=
  (Finset.univ : Finset H).val.map fun a => g (a • y)

/-- **The monic polynomial whose roots, with multiplicity, are the values on an orbit.** -/
def orbitPoly (H : Type*) [Group H] [Fintype H] [MulAction H Y] (g : Y → ℂ) (y : Y) : ℂ[X] :=
  ((orbitValues H g y).map fun r => X - C r).prod

theorem card_orbitValues (y : Y) :
    Multiset.card (orbitValues H g y) = Fintype.card H := by
  simp [orbitValues]

/-- The value at the point itself is one of the values on its orbit. -/
theorem mem_orbitValues (y : Y) : g y ∈ orbitValues H g y :=
  Multiset.mem_map.2 ⟨1, by simp, by simp⟩

/-- **The values on an orbit do not change along the orbit**: moving the point by a group element
permutes the group, and so permutes the entries of the multiset. -/
theorem orbitValues_smul (b : H) (y : Y) : orbitValues H g (b • y) = orbitValues H g y := by
  show Multiset.map (fun a : H => g (a • (b • y))) Finset.univ.val
      = Multiset.map (fun a : H => g (a • y)) Finset.univ.val
  rw [show (fun a : H => g (a • (b • y))) = (fun a : H => g (a • y)) ∘ (Equiv.mulRight b) from
      funext fun a => by simp [mul_smul], ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem monic_orbitPoly (y : Y) : (orbitPoly H g y).Monic :=
  monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r

theorem natDegree_orbitPoly (y : Y) :
    (orbitPoly H g y).natDegree = Fintype.card H := by
  rw [orbitPoly, natDegree_multiset_prod_X_sub_C_eq_card, card_orbitValues]

/-- **A function is a root of its own orbit polynomial.** -/
theorem eval_orbitPoly_self (y : Y) : (orbitPoly H g y).eval (g y) = 0 := by
  rw [orbitPoly, eval_multiset_prod, Multiset.map_map]
  refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨g y, mem_orbitValues y, ?_⟩)
  simp

/-- **The orbit polynomial, written out from its coefficients.** -/
theorem orbitPoly_eq_add_sum (y : Y) :
    orbitPoly H g y = X ^ Fintype.card H
      + ∑ k ∈ Finset.range (Fintype.card H), C ((orbitPoly H g y).coeff k) * X ^ k := by
  have hN : (orbitPoly H g y).natDegree = Fintype.card H := natDegree_orbitPoly (H := H) y
  have hc : (orbitPoly H g y).coeff (Fintype.card H) = 1 := by
    rw [← hN]; exact (monic_orbitPoly (H := H) y).coeff_natDegree
  conv_lhs => rw [(orbitPoly H g y).as_sum_range' (Fintype.card H + 1) (by rw [hN]; omega)]
  rw [Finset.sum_range_succ, hc]
  simp [C_mul_X_pow_eq_monomial, monomial_one_right_eq_X_pow, add_comm]

end Defs

section Analytic

variable {Y : Type*} [TopologicalSpace Y] {f g : Y → ℂ}
variable {H : Type*} [Group H] [Fintype H] [MulAction H Y] [ContinuousConstSMul H Y]

/-- **The elementary symmetric functions of the values on a fibre are holomorphic.** -/
theorem isHolo_esymm (hf : IsLocalHomeomorph f) (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (hg : IsHolo f g) (k : ℕ) : IsHolo f fun y => (orbitValues H g y).esymm k := by
  intro y
  have hstep : ∀ a : H, IsHoloAt f (fun y => g (a • y)) y := by
    intro a
    have hp : ∀ y' : Y, f ((Homeomorph.smul a : Y ≃ₜ Y) y') = f y' := by
      intro y'; simpa using hover a y'
    have := IsHoloAt.comp_homeomorph (f := f) (g := g) (y := y)
      (perm := (Homeomorph.smul a : Y ≃ₜ Y)) hp (hg _)
    simpa using this
  have hrw : (fun y : Y => (orbitValues H g y).esymm k)
      = fun y : Y => ∑ t ∈ (Finset.univ : Finset H).powersetCard k, ∏ a ∈ t, g (a • y) :=
    funext fun y' => Finset.esymm_map_val (fun a : H => g (a • y')) Finset.univ k
  rw [hrw]
  exact isHoloAt_finset_sum hf _ fun t _ => isHoloAt_finset_prod hf t fun a _ => hstep a

/-- **The elementary symmetric functions of the values on a fibre are analytic functions of the
base point.** -/
theorem exists_analytic_esymm (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (k : ℕ) :
    ∃ c : ℂ → ℂ, (∀ y, (orbitValues H g y).esymm k = c (f y)) ∧ ∀ y, AnalyticAt ℂ c (f y) := by
  refine exists_analytic_of_isHolo_of_invariant hf (isHolo_esymm hf hover hg k) ?_
  intro y y' hyy
  obtain ⟨b, rfl⟩ := htrans y y' hyy
  rw [orbitValues_smul]

/-- **Each coefficient of the orbit polynomial is an analytic function of the base point.** -/
theorem exists_analytic_orbitPoly_coeff (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (k : ℕ) :
    ∃ c : ℂ → ℂ, (∀ y, (orbitPoly H g y).coeff k = c (f y)) ∧ ∀ y, AnalyticAt ℂ c (f y) := by
  by_cases hk : k ≤ Fintype.card H
  · obtain ⟨c, hc, hac⟩ := exists_analytic_esymm hf hover htrans hg (Fintype.card H - k)
    refine ⟨fun w => (-1) ^ (Fintype.card H - k) * c w, fun y => ?_, fun y => ?_⟩
    · rw [orbitPoly, Multiset.prod_X_sub_C_coeff _ (by rwa [card_orbitValues]),
        card_orbitValues, hc]
    · exact analyticAt_const.mul (hac y)
  · refine ⟨fun _ => 0, fun y => ?_, fun _ => analyticAt_const⟩
    refine coeff_eq_zero_of_natDegree_lt ?_
    rw [natDegree_orbitPoly]
    omega

/-- **A holomorphic function on the total space is algebraic over the base.**

If a finite group acts on the total space over the base with each fibre a single orbit, then a
holomorphic function satisfies a monic equation of degree the order of the group whose
coefficients are analytic functions of the base point. -/
theorem exists_monic_analytic_of_isHolo (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) :
    ∃ c : ℕ → ℂ → ℂ, (∀ k y, AnalyticAt ℂ (c k) (f y)) ∧
      ∀ y, g y ^ Fintype.card H
        + ∑ k ∈ Finset.range (Fintype.card H), c k (f y) * g y ^ k = 0 := by
  choose c hc hac using fun k => exists_analytic_orbitPoly_coeff hf hover htrans hg k
  refine ⟨c, fun k y => hac k y, fun y => ?_⟩
  have hzero : (orbitPoly H g y).eval (g y) = 0 := eval_orbitPoly_self y
  rw [orbitPoly_eq_add_sum y] at hzero
  simpa [hc, eval_finset_sum] using hzero

end Analytic

end Rigidity.RET

end

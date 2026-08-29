/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Shifting

/-!
# The order of the group annihilates the complete cohomology

In degree zero the complete cohomology is the invariants modulo the norms, and on the invariants
the norm is multiplication by the order of the group; in degree minus one it is the classes in the
coinvariants killed by the norm, and the class of the norm of a vector is the order of the group
times the class of the vector.  Both of the middle groups are therefore annihilated by the order
of the group.

Dimension shifting carries that statement to every other degree: the complete cohomology of a
representation in a positive degree is the complete cohomology of its shift one degree lower, and
in a degree below minus one it is the complete cohomology of its coshift one degree higher.  Two
inductions, one upwards from degree zero and one downwards from degree minus one, therefore give
the annihilation in every integer degree.

## Main results

* `InverseGalois.CFT.Tate.card_nsmul_eq_zero_tateModule`: **the order of the group annihilates the
  complete cohomology in every integer degree.**

## Tags

Tate cohomology, dimension shifting, annihilator, finite group
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **The order of the group annihilates the complete cohomology in a degree at least zero.** -/
theorem card_nsmul_eq_zero_tateModule_ofNat (m : ℕ) :
    ∀ (A : Rep k G) (x : tateModule A (m : ℤ)), Nat.card G • x = 0 := by
  induction m with
  | zero => intro A x; exact card_nsmul_eq_zero_H0 A.ρ x
  | succ m ih =>
    intro A x
    refine (tateShiftEquiv A (m : ℤ)).symm.injective ?_
    rw [map_nsmul, map_zero]
    exact ih (shiftObj A) ((tateShiftEquiv A (m : ℤ)).symm x)

/-- **The order of the group annihilates the complete cohomology in a degree below zero.** -/
theorem card_nsmul_eq_zero_tateModule_negSucc (m : ℕ) :
    ∀ (A : Rep k G) (x : tateModule A (Int.negSucc m)), Nat.card G • x = 0 := by
  induction m with
  | zero => intro A x; exact card_nsmul_eq_zero_Hm1 A.ρ x
  | succ m ih =>
    intro A x
    refine (tateCoshiftEquiv A (Int.negSucc (m + 1))).injective ?_
    rw [map_nsmul, map_zero]
    exact ih (coshiftObj A) (tateCoshiftEquiv A (Int.negSucc (m + 1)) x)

/-- **The order of the group annihilates the complete cohomology in every integer degree.** -/
theorem card_nsmul_eq_zero_tateModule (A : Rep k G) (n : ℤ) (x : tateModule A n) :
    Nat.card G • x = 0 := by
  match n, x with
  | .ofNat m, x => exact card_nsmul_eq_zero_tateModule_ofNat m A x
  | .negSucc m, x => exact card_nsmul_eq_zero_tateModule_negSucc m A x

end

end InverseGalois.CFT.Tate

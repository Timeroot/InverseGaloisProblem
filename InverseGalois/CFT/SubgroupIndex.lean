/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Splitting a relative index along a third subgroup

Let `B ≤ A` be subgroups of a commutative group and let `C` be a third subgroup.  The index of `B`
in `A` factors as the index of `B ⊔ C` in `A ⊔ C` times the index of `B ⊓ C` in `A ⊓ C`.

The proof inserts the intermediate subgroup `A ⊓ (B ⊔ C)` between `B` and `A`.  Its index in `A` is
the index of `B ⊔ C` in `A`, which is the index of `B ⊔ C` in `A ⊔ C` because adjoining a subgroup
to itself changes nothing; and the modular law identifies it with `B ⊔ (A ⊓ C)`, whose index over
`B` is the index of `B ⊓ C` in `A ⊓ C` for the same reason.

This is the counting identity behind the computation of the index of the group of `S`-ideles that
are norms, where `A` and `B` are groups of ideles and `C` cuts out a condition at a set of places.

## Main results

* `InverseGalois.CFT.relIndex_sup_mul_relIndex_inf`: **the index of `B` in `A` is the product of
  the index of `B ⊔ C` in `A ⊔ C` and the index of `B ⊓ C` in `A ⊓ C`.**
* `InverseGalois.CFT.relIndex_sup_dvd`: in particular each of the two factors divides the index.

## Tags

subgroup, index, modular law, second isomorphism theorem
-/

namespace InverseGalois.CFT

variable {G : Type*} [AddCommGroup G] {A B C : AddSubgroup G}

/-- The index in `A` of the subgroup it cuts out of `B ⊔ C` is the index of `B ⊔ C` in `A ⊔ C`. -/
theorem relIndex_inf_sup (h : B ≤ A) :
    (A ⊓ (B ⊔ C)).relIndex A = (B ⊔ C).relIndex (A ⊔ C) := by
  have hsup : A ⊔ (B ⊔ C) = A ⊔ C := by rw [← sup_assoc, sup_eq_left.mpr h]
  rw [inf_comm, AddSubgroup.inf_relIndex_right, ← AddSubgroup.relIndex_sup_right A (B ⊔ C), hsup]

/-- The index over `B` of the subgroup `A` cuts out of `B ⊔ C` is the index of `B ⊓ C` in
`A ⊓ C`. -/
theorem relIndex_sup_inf (h : B ≤ A) :
    B.relIndex (A ⊓ (B ⊔ C)) = (B ⊓ C).relIndex (A ⊓ C) := by
  have hmod : A ⊓ (B ⊔ C) = B ⊔ (C ⊓ A) := by rw [inf_comm]; exact sup_inf_assoc_of_le C h
  have hinf : B ⊓ (A ⊓ C) = B ⊓ C := by rw [← inf_assoc, inf_eq_left.mpr h]
  rw [hmod, AddSubgroup.relIndex_sup_left, inf_comm C A, ← AddSubgroup.inf_relIndex_right B (A ⊓ C),
    hinf]

/-- **The index of `B` in `A` splits along a third subgroup `C`**: it is the product of the index
of `B ⊔ C` in `A ⊔ C` and the index of `B ⊓ C` in `A ⊓ C`. -/
theorem relIndex_sup_mul_relIndex_inf (h : B ≤ A) :
    (B ⊔ C).relIndex (A ⊔ C) * (B ⊓ C).relIndex (A ⊓ C) = B.relIndex A := by
  rw [← relIndex_inf_sup (C := C) h, ← relIndex_sup_inf (C := C) h, mul_comm]
  exact AddSubgroup.relIndex_mul_relIndex B (A ⊓ (B ⊔ C)) A (le_inf h le_sup_left) inf_le_left

/-- Each of the two factors divides the index of `B` in `A`. -/
theorem relIndex_sup_dvd (h : B ≤ A) : (B ⊔ C).relIndex (A ⊔ C) ∣ B.relIndex A :=
  Dvd.intro _ (relIndex_sup_mul_relIndex_inf h)

/-- Each of the two factors divides the index of `B` in `A`. -/
theorem relIndex_inf_dvd (h : B ≤ A) : (B ⊓ C).relIndex (A ⊓ C) ∣ B.relIndex A :=
  Dvd.intro_left _ (relIndex_sup_mul_relIndex_inf h)

end InverseGalois.CFT

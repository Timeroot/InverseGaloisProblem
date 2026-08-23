/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Finite
import InverseGalois.CFT.Tate.Herbrand
import InverseGalois.CFT.Tate.PermLattice
import InverseGalois.CFT.Tate.Trivial

/-!
# The augmentation sublattice

An equivariant surjection of a lattice onto the integers with trivial action -- for the lattice of
a permuted basis, the sum of the coordinates -- has a kernel, the *augmentation sublattice*, which
is again stable under the action.  The short exact sequence it sits in has the integers with
trivial action as its quotient, whose Herbrand quotient is `n`, so the Herbrand quotient of the
augmentation sublattice is that of the whole lattice divided by `n`.

This is the shape in which the unit lattice of a Galois extension is met.  Its real representation
is the trace-zero part of the permutation representation on the infinite places, that is, the real
representation of the augmentation sublattice of the permutation lattice, and by
`InverseGalois.CFT.herbrand_eq_of_real_intertwine` the Herbrand quotient may be computed there.

## Main definitions

* `InverseGalois.CFT.kerAut`: the restriction of an automorphism to the kernel of an invariant
  homomorphism.
* `InverseGalois.CFT.kerTateSES`: the short exact sequence cut out by an invariant surjection onto
  a module with trivial action.
* `InverseGalois.CFT.sumHom`: the sum of the coordinates of a point of a lattice with a
  distinguished basis.

## Main results

* `InverseGalois.CFT.kerAut_pow_eq_one`: the restricted automorphism inherits the order.
* `InverseGalois.CFT.herbrand_kerAut_mul`: **the Herbrand quotient of the kernel of an invariant
  surjection onto the integers is that of the lattice divided by `n`.**
* `InverseGalois.CFT.herbrand_kerAut_sumHom_mul`: the same for the sum of the coordinates of a
  permuted basis.

## Tags

Tate cohomology, Herbrand quotient, augmentation, trace zero, unit lattice
-/

namespace InverseGalois.CFT

variable {A C : Type*} [AddCommGroup A] [AddCommGroup C] {n : ℕ}

/-! ### The restriction to the kernel of an invariant homomorphism -/

/-- **The restriction of an automorphism to the kernel of an invariant homomorphism.** -/
def kerAut (σ : A ≃+ A) (π : A →+ C) (h : ∀ a, π (σ a) = π a) : π.ker ≃+ π.ker where
  toFun x := ⟨σ x, by
    rw [AddMonoidHom.mem_ker, h]
    exact AddMonoidHom.mem_ker.mp x.2⟩
  invFun x := ⟨σ.symm x, by
    have hx := h (σ.symm x)
    rw [σ.apply_symm_apply] at hx
    rw [AddMonoidHom.mem_ker, ← hx]
    exact AddMonoidHom.mem_ker.mp x.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_add' x y := Subtype.ext (σ.map_add x y)

variable (σ : A ≃+ A) (π : A →+ C) (h : ∀ a, π (σ a) = π a)

@[simp]
theorem coe_kerAut_apply (x : π.ker) : ((kerAut σ π h x : π.ker) : A) = σ x := rfl

/-- The powers of the restriction are the restrictions of the powers. -/
theorem coe_pow_kerAut_apply (k : ℕ) (x : π.ker) :
    ((((kerAut σ π h) ^ k) x : π.ker) : A) = (σ ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, coe_kerAut_apply, ih, ← pow_succ_apply]

variable {σ π h}

/-- **The restricted automorphism inherits the order of the automorphism.** -/
theorem kerAut_pow_eq_one (hσ : σ ^ n = 1) : (kerAut σ π h) ^ n = 1 :=
  AddEquiv.ext fun x => Subtype.ext (by rw [coe_pow_kerAut_apply, hσ]; rfl)

/-! ### The short exact sequence -/

/-- **The short exact sequence cut out by an invariant surjection** onto a module with trivial
action. -/
def kerTateSES (hσ : σ ^ n = 1) (hsurj : Function.Surjective π) : TateSES n π.ker A C where
  σA := kerAut σ π h
  σB := σ
  σC := 1
  hσA := kerAut_pow_eq_one hσ
  hσB := hσ
  hσC := one_pow n
  f := π.ker.subtype
  g := π
  hf _ := rfl
  hg := h
  finj _ _ hab := Subtype.ext hab
  gsurj := hsurj
  range_eq_ker := AddSubgroup.range_subtype _

@[simp]
theorem kerTateSES_σA (hσ : σ ^ n = 1) (hsurj : Function.Surjective π) :
    (kerTateSES (h := h) hσ hsurj).σA = kerAut σ π h := rfl

@[simp]
theorem kerTateSES_σB (hσ : σ ^ n = 1) (hsurj : Function.Surjective π) :
    (kerTateSES (h := h) hσ hsurj).σB = σ := rfl

@[simp]
theorem kerTateSES_σC (hσ : σ ^ n = 1) (hsurj : Function.Surjective π) :
    (kerTateSES (h := h) hσ hsurj).σC = (1 : C ≃+ C) := rfl

/-! ### The Herbrand quotient of the kernel -/

/-- The kernel of a homomorphism out of a lattice is again a lattice. -/
instance instModuleFiniteKer [Module.Finite ℤ A] : Module.Finite ℤ π.ker :=
  Module.Finite.of_injective (AddSubgroup.subtype _).toIntLinearMap Subtype.val_injective

/-- **The Herbrand quotient of the kernel of an invariant surjection onto the integers is that of
the lattice divided by the order of the group.** -/
theorem herbrand_kerAut_mul {π : A →+ ℤ} {h : ∀ a, π (σ a) = π a} [Module.Finite ℤ A] (hn : n ≠ 0)
    (hσ : σ ^ n = 1) (hsurj : Function.Surjective π) :
    herbrand (kerAut σ π h) n * n = herbrand σ n := by
  haveI : NeZero n := ⟨hn⟩
  have hmul := (kerTateSES (h := h) hσ hsurj).herbrand_mul
  rw [kerTateSES_σA, kerTateSES_σB, kerTateSES_σC, herbrand_int n hn] at hmul
  exact hmul

/-! ### The sum of the coordinates -/

variable (X : Type*) [Fintype X]

/-- **The sum of the coordinates** of a point of a lattice with a distinguished basis. -/
def sumHom : (X → ℤ) →+ ℤ where
  toFun f := ∑ x, f x
  map_zero' := Finset.sum_const_zero
  map_add' _ _ := Finset.sum_add_distrib

@[simp]
theorem sumHom_apply (f : X → ℤ) : sumHom X f = ∑ x, f x := rfl

variable {X}

/-- A permutation of the basis preserves the sum of the coordinates. -/
theorem sumHom_permLatticeAut (p : Equiv.Perm X) (f : X → ℤ) :
    sumHom X (permLatticeAut p f) = sumHom X f :=
  Fintype.sum_equiv p _ _ fun _ => rfl

/-- The sum of the coordinates is onto as soon as there is a coordinate. -/
theorem sumHom_surjective [Nonempty X] : Function.Surjective (sumHom X) := by
  classical
  intro m
  refine ⟨fun x => if x = Classical.arbitrary X then m else 0, ?_⟩
  simp

/-- **The Herbrand quotient of the augmentation sublattice of a permuted basis** is that of the
whole lattice divided by the order of the group. -/
theorem herbrand_kerAut_sumHom_mul [Nonempty X] {p : Equiv.Perm X} (hn : n ≠ 0)
    (hp : (permLatticeAut p) ^ n = 1) :
    herbrand (kerAut (permLatticeAut p) (sumHom X) (sumHom_permLatticeAut p)) n * n
      = herbrand (permLatticeAut p) n :=
  herbrand_kerAut_mul hn hp sumHom_surjective

end InverseGalois.CFT

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.RealHerbrand

/-!
# Comparing two lattices inside one real vector space

`InverseGalois.CFT.herbrand_eq_of_real_intertwine` asks for a real matrix intertwining the two
integer matrices of the action.  In practice the two lattices are met inside one and the same real
vector space, each with a basis that becomes a basis of that space, and the two actions are induced
by one and the same real endomorphism.  The intertwiner is then the change of basis matrix, and the
comparison of Herbrand quotients needs nothing further.

This is exactly the situation of the unit lattice of a number field: the free lattice on the
infinite places and the units modulo torsion both sit inside the space of real valued functions on
the infinite places, the first by the coordinates and the second by the logarithmic embedding, and
the Galois group acts on both by permuting the places.

## Main results

* `InverseGalois.CFT.toMatrix_eq_autMatrix`: the matrix of the real endomorphism in the real basis
  is the matrix of the automorphism in the lattice basis.
* `InverseGalois.CFT.herbrand_eq_of_real_basis`: **two lattices with bases spanning one real vector
  space, on which the actions are induced by one endomorphism, have the same Herbrand quotient.**

## Tags

Tate cohomology, Herbrand quotient, lattice, representation, change of basis
-/

namespace InverseGalois.CFT

open Module (Basis)

variable {A B W : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup W] [Module ℝ W]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The matrix of the induced endomorphism -/

/-- **The matrix of the real endomorphism in the real basis is the matrix of the automorphism in
the lattice basis**, as soon as the embedding carries one basis to the other and intertwines the
two actions. -/
theorem toMatrix_eq_autMatrix (bA : Basis ι ℤ A) (fA : Basis ι ℝ W) {σA : A ≃+ A} (eA : A →+ W)
    (hfA : ∀ i, fA i = eA (bA i)) {T : W →ₗ[ℝ] W} (hT : ∀ a, eA (σA a) = T (eA a)) :
    LinearMap.toMatrix fA fA T = (autMatrix bA σA).map (Int.cast) := by
  have hval : ∀ j, T (fA j) = ∑ i, ((bA.repr (σA (bA j)) i : ℤ) : ℝ) • fA i := by
    intro j
    rw [hfA j, ← hT]
    conv_lhs => rw [← bA.sum_repr (σA (bA j))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfA i, AddMonoidHom.map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
  ext i j
  rw [Matrix.map_apply, autMatrix, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hval j,
    fA.repr_sum_self]
  rfl

/-! ### The comparison of the Herbrand quotients -/

/-- **Two lattices with bases spanning one real vector space, on which the actions are induced by
one and the same endomorphism, have the same Herbrand quotient.** -/
theorem herbrand_eq_of_real_basis [Module.Free ℤ A] [Module.Finite ℤ A] [Module.Free ℤ B]
    [Module.Finite ℤ B] {σA : A ≃+ A} {σB : B ≃+ B} {n : ℕ} (hn : n ≠ 0) (hσA : σA ^ n = 1)
    (hσB : σB ^ n = 1) (bA : Basis ι ℤ A) (bB : Basis ι ℤ B) (fA fB : Basis ι ℝ W)
    (T : W →ₗ[ℝ] W) (eA : A →+ W) (eB : B →+ W) (hTA : ∀ a, eA (σA a) = T (eA a))
    (hTB : ∀ b, eB (σB b) = T (eB b)) (hfA : ∀ i, fA i = eA (bA i))
    (hfB : ∀ i, fB i = eB (bB i)) :
    herbrand σA n = herbrand σB n := by
  have hone : LinearMap.toMatrix fB fA LinearMap.id * LinearMap.toMatrix fA fB LinearMap.id
      = 1 := by
    rw [← LinearMap.toMatrix_comp fA fB fA, LinearMap.id_comp, LinearMap.toMatrix_id]
  have hdet : (LinearMap.toMatrix fA fB (LinearMap.id : W →ₗ[ℝ] W)).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hone
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
    exact one_ne_zero this.symm
  refine herbrand_eq_of_real_intertwine bA bB hn hσA hσB _ hdet ?_
  rw [← toMatrix_eq_autMatrix bA fA eA hfA hTA, ← toMatrix_eq_autMatrix bB fB eB hfB hTB,
    ← LinearMap.toMatrix_comp fA fA fB, ← LinearMap.toMatrix_comp fA fB fB,
    LinearMap.id_comp, LinearMap.comp_id]

end InverseGalois.CFT

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Finite
import InverseGalois.CFT.Tate.Lattice
import InverseGalois.CFT.Tate.RealForm

/-!
# The Herbrand quotient depends only on the real representation

Two lattices carrying an action of the same cyclic group whose real representations are isomorphic
have the same Herbrand quotient.  In coordinates the hypothesis is a single real matrix of nonzero
determinant intertwining the two integer matrices of the action, and by
`InverseGalois.CFT.exists_intMatrix_intertwine` such a matrix produces an integer one, which is an
injection of one lattice into the other of the same rank and therefore leaves the Herbrand quotient
unchanged.

This is the invariance that makes the Herbrand quotient computable in arithmetic.  The unit lattice
of a Galois extension is not given by any explicit basis, but its real representation is: the
logarithmic embedding identifies it with the trace-zero part of the permutation representation on
the infinite places.  The quotient may therefore be computed in the permutation model, where the
group acts by permuting coordinates.

## Main definitions

* `InverseGalois.CFT.autMatrix`: the matrix of an additive automorphism of a lattice in a basis.
* `InverseGalois.CFT.latticeHom`: the homomorphism of lattices attached to an integer matrix.

## Main results

* `InverseGalois.CFT.autMatrix_pow`: the matrix of a power is the power of the matrix.
* `InverseGalois.CFT.latticeHom_equivariant`: an intertwining matrix gives an equivariant
  homomorphism.
* `InverseGalois.CFT.latticeHom_injective`: a matrix of nonzero determinant gives an injective
  homomorphism.
* `InverseGalois.CFT.herbrand_eq_of_real_intertwine`: **two lattices with isomorphic real
  representations have the same Herbrand quotient.**

## Tags

Tate cohomology, Herbrand quotient, lattice, representation
-/

namespace InverseGalois.CFT

open Matrix
open Module (Basis)

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The matrix of an automorphism -/

/-- **The matrix of an additive automorphism of a lattice** in a basis. -/
noncomputable def autMatrix (b : Basis ι ℤ A) (σ : A ≃+ A) : Matrix ι ι ℤ :=
  LinearMap.toMatrix b b (σ : A →+ A).toIntLinearMap

theorem autMatrix_one (b : Basis ι ℤ A) : autMatrix b (1 : A ≃+ A) = 1 := by
  have h : ((1 : A ≃+ A) : A →+ A).toIntLinearMap = LinearMap.id := rfl
  rw [autMatrix, h, LinearMap.toMatrix_id]

theorem autMatrix_mul (b : Basis ι ℤ A) (σ τ : A ≃+ A) :
    autMatrix b (σ * τ) = autMatrix b σ * autMatrix b τ := by
  have h : ((σ * τ : A ≃+ A) : A →+ A).toIntLinearMap
      = (σ : A →+ A).toIntLinearMap ∘ₗ (τ : A →+ A).toIntLinearMap := rfl
  rw [autMatrix, h, LinearMap.toMatrix_comp b b b, autMatrix, autMatrix]

/-- **The matrix of a power is the power of the matrix.** -/
theorem autMatrix_pow (b : Basis ι ℤ A) (σ : A ≃+ A) (k : ℕ) :
    autMatrix b (σ ^ k) = autMatrix b σ ^ k := by
  induction k with
  | zero => simpa using autMatrix_one b
  | succ k ih => rw [pow_succ, autMatrix_mul, ih, ← pow_succ]

theorem autMatrix_inv_mul (b : Basis ι ℤ A) (σ : A ≃+ A) :
    autMatrix b σ⁻¹ * autMatrix b σ = 1 := by
  rw [← autMatrix_mul, inv_mul_cancel, autMatrix_one]

theorem autMatrix_mul_inv (b : Basis ι ℤ A) (σ : A ≃+ A) :
    autMatrix b σ * autMatrix b σ⁻¹ = 1 := by
  rw [← autMatrix_mul, mul_inv_cancel, autMatrix_one]

/-! ### The homomorphism attached to a matrix -/

/-- **The homomorphism of lattices attached to an integer matrix** and a pair of bases. -/
noncomputable def latticeHom (bA : Basis ι ℤ A) (bB : Basis ι ℤ B) (W : Matrix ι ι ℤ) : A →+ B :=
  (Matrix.toLin bA bB W).toAddMonoidHom

theorem latticeHom_apply (bA : Basis ι ℤ A) (bB : Basis ι ℤ B) (W : Matrix ι ι ℤ) (a : A) :
    latticeHom bA bB W a = Matrix.toLin bA bB W a := rfl

/-- **An intertwining matrix gives an equivariant homomorphism.** -/
theorem latticeHom_equivariant (bA : Basis ι ℤ A) (bB : Basis ι ℤ B) {σA : A ≃+ A} {σB : B ≃+ B}
    {W : Matrix ι ι ℤ} (hW : W * autMatrix bA σA = autMatrix bB σB * W) (a : A) :
    latticeHom bA bB W (σA a) = σB (latticeHom bA bB W a) := by
  have hmap : (Matrix.toLin bA bB W) ∘ₗ (σA : A →+ A).toIntLinearMap
      = (σB : B →+ B).toIntLinearMap ∘ₗ (Matrix.toLin bA bB W) := by
    apply (LinearMap.toMatrix bA bB).injective
    rw [LinearMap.toMatrix_comp bA bA bB, LinearMap.toMatrix_comp bA bB bB,
      LinearMap.toMatrix_toLin, ← autMatrix, ← autMatrix, hW]
  exact LinearMap.congr_fun hmap a

/-- **A matrix of nonzero determinant gives an injective homomorphism.** -/
theorem latticeHom_injective [Module.Free ℤ A] (bA : Basis ι ℤ A) (bB : Basis ι ℤ B)
    {W : Matrix ι ι ℤ} (hW : W.det ≠ 0) : Function.Injective (latticeHom bA bB W) := by
  have hcomp : (Matrix.toLin bB bA W.adjugate) ∘ₗ (Matrix.toLin bA bB W)
      = W.det • (LinearMap.id : A →ₗ[ℤ] A) := by
    rw [← Matrix.toLin_mul bA bB bA, Matrix.adjugate_mul, map_smul, Matrix.toLin_one]
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  have hz : (Matrix.toLin bA bB W) a = 0 := ha
  have hval := LinearMap.congr_fun hcomp a
  rw [LinearMap.comp_apply, hz, map_zero] at hval
  have h : W.det • a = 0 := by simpa using hval.symm
  exact (smul_eq_zero.1 h).resolve_left hW

/-! ### Invariance of the Herbrand quotient -/

/-- **Two lattices whose real representations are isomorphic have the same Herbrand quotient.** -/
theorem herbrand_eq_of_real_intertwine [Module.Free ℤ A] [Module.Finite ℤ A] [Module.Free ℤ B]
    [Module.Finite ℤ B] (bA : Basis ι ℤ A) (bB : Basis ι ℤ B) {σA : A ≃+ A} {σB : B ≃+ B} {n : ℕ}
    (hn : n ≠ 0) (hσA : σA ^ n = 1) (hσB : σB ^ n = 1) (Φ : Matrix ι ι ℝ) (hdet : Φ.det ≠ 0)
    (hΦ : Φ * (autMatrix bA σA).map Int.cast = (autMatrix bB σB).map Int.cast * Φ) :
    herbrand σA n = herbrand σB n := by
  haveI : NeZero n := ⟨hn⟩
  have hSA : autMatrix bA σA ^ n = 1 := by rw [← autMatrix_pow, hσA, autMatrix_one]
  have hSB : autMatrix bB σB ^ n = 1 := by rw [← autMatrix_pow, hσB, autMatrix_one]
  obtain ⟨W, hWeq, hWdet⟩ := exists_intMatrix_intertwine hn hSA hSB (autMatrix_inv_mul bB σB)
    (autMatrix_mul_inv bB σB) Φ hΦ hdet
  refine herbrand_eq_of_injective_of_finrank_eq hσA hσB (latticeHom bA bB W)
    (latticeHom_equivariant bA bB hWeq) (latticeHom_injective bA bB hWdet) ?_
  rw [Module.finrank_eq_card_basis bA, Module.finrank_eq_card_basis bB]

end InverseGalois.CFT

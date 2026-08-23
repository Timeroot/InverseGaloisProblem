import Mathlib
import InverseGalois.CFT.Brauer.TensorSimple
import InverseGalois.CFT.Brauer.Opposite

/-!
# The Brauer group of a field is an abelian group

Let `K` be a field. `Mathlib` defines `CSA K`, the finite-dimensional central simple `K`-algebras,
the relation `IsBrauerEquivalent` on them, and the quotient `BrauerGroup K`. This file equips
`BrauerGroup K` with its group structure: the product of the classes of `A` and `B` is the class
of `A ⊗[K] B`, the identity is the class of `K` itself, and the inverse of the class of `A` is the
class of the opposite algebra `Aᵐᵒᵖ`.

The three inputs are the tensor product of central simple algebras (`CSA.tensor`, from
`InverseGalois.CFT.Brauer.TensorSimple`), the identification `A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Matrix n n K`
(`InverseGalois.CFT.exists_algEquiv_matrix_tensorOp`, from `InverseGalois.CFT.Brauer.Opposite`),
and the Kronecker product `Matrix n n A ⊗[K] Matrix m m B ≃ₐ[K] Matrix (n * m) (n * m) (A ⊗[K] B)`,
which makes the tensor product descend to the quotient.

Since the identity element is represented by `K` itself, which lives in the universe of `K`, the
group structure is stated for `BrauerGroup.{u, u} K`; the auxiliary constructions are polymorphic
in the universe of the carrier.

## Main definitions

* `CSA.op`: the opposite algebra of a finite-dimensional central simple algebra.
* `CSA.one`: the field `K`, viewed as a finite-dimensional central simple `K`-algebra.
* `CSA.matrix`: a matrix algebra over `K`, viewed as a finite-dimensional central simple algebra.
* `BrauerGroup.instCommGroup`: the abelian group structure on `BrauerGroup K`.

## Main results

* `matrix_tensor`: the Kronecker identification of a tensor product of matrix algebras.
* `IsBrauerEquivalent.tensor`: Brauer equivalence is a congruence for `CSA.tensor`.
* `IsBrauerEquivalent.op`: Brauer equivalence is a congruence for `CSA.op`.
* `BrauerGroup.mk_mul`, `BrauerGroup.mk_one`, `BrauerGroup.mk_inv`, `BrauerGroup.mk_eq_one_iff`,
  `BrauerGroup.mk_matrix`: the elementary API of the group structure.

## Tags

Brauer group, central simple algebra
-/

universe u v

open scoped TensorProduct

attribute [instance] Brauer.CSA_Setoid

variable {K : Type u} [Field K]

/-! ### Building blocks -/

/-- The opposite algebra of a finite-dimensional central simple `K`-algebra, again as a
finite-dimensional central simple `K`-algebra. -/
def CSA.op (A : CSA.{u, v} K) : CSA.{u, v} K where
  toAlgCat := AlgCat.of K Aᵐᵒᵖ

@[simp]
theorem CSA.coe_op (A : CSA.{u, v} K) : (CSA.op A : Type v) = Aᵐᵒᵖ := rfl

/-- The field `K` itself, viewed as a finite-dimensional central simple `K`-algebra. Its class is
the identity of the Brauer group of `K`. -/
def CSA.one (K : Type u) [Field K] : CSA.{u, u} K where
  toAlgCat := AlgCat.of K K

@[simp]
theorem CSA.coe_one : (CSA.one K : Type u) = K := rfl

/-- The algebra of `n × n` matrices over `K`, viewed as a finite-dimensional central simple
`K`-algebra. -/
def CSA.matrix (K : Type u) [Field K] (n : ℕ) [NeZero n] : CSA.{u, u} K where
  toAlgCat := AlgCat.of K (Matrix (Fin n) (Fin n) K)

@[simp]
theorem CSA.coe_matrix (n : ℕ) [NeZero n] :
    (CSA.matrix K n : Type u) = Matrix (Fin n) (Fin n) K := rfl

/-- Transporting a matrix algebra to the opposite algebra: `Mₙ(Aᵐᵒᵖ)` is the opposite of `Mₙ(A)`,
the isomorphism being transposition. -/
def matrixOpAlgEquiv (K : Type u) [Field K] (n : Type*) [Fintype n] [DecidableEq n]
    (A : Type v) [Ring A] [Algebra K A] : Matrix n n Aᵐᵒᵖ ≃ₐ[K] (Matrix n n A)ᵐᵒᵖ :=
  (matrixEquivTensor n K Aᵐᵒᵖ).trans <|
    (Algebra.TensorProduct.congr AlgEquiv.refl (Matrix.transposeAlgEquiv n K K)).trans <|
      (Algebra.TensorProduct.opAlgEquiv K K A (Matrix n n K)).trans
        (AlgEquiv.op (matrixEquivTensor n K A).symm)

/-- A Kronecker product of matrix algebras: `Mₙ(A) ⊗ Mₘ(B) ≃ M_{nm}(A ⊗ B)`. -/
theorem matrix_tensor (A B : CSA.{u, v} K) (n m : ℕ) :
    Nonempty (Matrix (Fin n) (Fin n) A ⊗[K] Matrix (Fin m) (Fin m) B ≃ₐ[K]
      Matrix (Fin (n * m)) (Fin (n * m)) (A ⊗[K] B)) :=
  ⟨(Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin m) K K A B).trans
    (Matrix.reindexAlgEquiv K _ finProdFinEquiv)⟩

/-! ### Brauer equivalence is a congruence -/

namespace IsBrauerEquivalent

/-- Isomorphic central simple algebras are Brauer equivalent. -/
theorem of_algEquiv {A B : CSA.{u, v} K} (e : A ≃ₐ[K] B) : IsBrauerEquivalent A B :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

/-- An algebra isomorphic to a nonempty matrix algebra over `B` is Brauer equivalent to `B`. -/
theorem of_algEquiv_matrix {A B : CSA.{u, v} K} {n : ℕ} (hn : n ≠ 0)
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) B) : IsBrauerEquivalent A B :=
  ⟨1, n, one_ne_zero, hn, ⟨e.mapMatrix.trans <| (Matrix.compAlgEquiv (Fin 1) (Fin n) B K).trans <|
    Matrix.reindexAlgEquiv K B (Equiv.uniqueProd (Fin n) (Fin 1))⟩⟩

/-- The tensor product of central simple algebras respects Brauer equivalence. -/
theorem tensor {A A' B B' : CSA.{u, v} K} (hA : IsBrauerEquivalent A A')
    (hB : IsBrauerEquivalent B B') : IsBrauerEquivalent (CSA.tensor A B) (CSA.tensor A' B') := by
  obtain ⟨n, n', hn, hn', ⟨eA⟩⟩ := hA
  obtain ⟨m, m', hm, hm', ⟨eB⟩⟩ := hB
  obtain ⟨e₁⟩ := matrix_tensor A B n m
  obtain ⟨e₂⟩ := matrix_tensor A' B' n' m'
  exact ⟨n * m, n' * m', Nat.mul_ne_zero hn hm, Nat.mul_ne_zero hn' hm',
    ⟨e₁.symm.trans <| (Algebra.TensorProduct.congr eA eB).trans e₂⟩⟩

/-- Passing to the opposite algebra respects Brauer equivalence. -/
theorem op {A B : CSA.{u, v} K} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (CSA.op A) (CSA.op B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm, ⟨(matrixOpAlgEquiv K (Fin n) A).trans <|
    (AlgEquiv.op e).trans (matrixOpAlgEquiv K (Fin m) B).symm⟩⟩

end IsBrauerEquivalent

/-- The opposite algebra splits a central simple algebra: `Aᵐᵒᵖ ⊗[K] A` is Brauer equivalent
to `K`. -/
theorem CSA.op_tensor_self (A : CSA.{u, u} K) :
    IsBrauerEquivalent (CSA.tensor (CSA.op A) A) (CSA.one K) := by
  refine IsBrauerEquivalent.of_algEquiv_matrix (n := Module.finrank K A) ?_ ?_
  · exact Module.finrank_pos.ne'
  · exact (Algebra.TensorProduct.comm K _ _).trans
      (InverseGalois.CFT.tensorOpEquivMatrix K (Module.finBasis K A))

/-! ### The group structure -/

namespace BrauerGroup

/-- The multiplication of the Brauer group, induced by the tensor product of algebras. -/
noncomputable def mul : BrauerGroup.{u, u} K → BrauerGroup.{u, u} K → BrauerGroup.{u, u} K :=
  Quotient.map₂ CSA.tensor fun _ _ hA _ _ hB => IsBrauerEquivalent.tensor hA hB

/-- The inversion of the Brauer group, induced by passage to the opposite algebra. -/
noncomputable def inv : BrauerGroup.{u, u} K → BrauerGroup.{u, u} K :=
  Quotient.map CSA.op fun _ _ h => IsBrauerEquivalent.op h

/-- The Brauer group of a field is an abelian group: the product of the classes of `A` and `B` is
the class of `A ⊗[K] B`, the identity is the class of `K`, and the inverse of the class of `A` is
the class of `Aᵐᵒᵖ`. -/
noncomputable instance instCommGroup : CommGroup (BrauerGroup.{u, u} K) where
  mul := mul
  one := ⟦CSA.one K⟧
  inv := inv
  mul_assoc := by
    refine Quotient.ind fun A => Quotient.ind fun B => Quotient.ind fun C => ?_
    exact Quotient.sound (IsBrauerEquivalent.of_algEquiv (Algebra.TensorProduct.assoc K K K A B C))
  one_mul := by
    refine Quotient.ind fun A => ?_
    exact Quotient.sound (IsBrauerEquivalent.of_algEquiv (Algebra.TensorProduct.lid K A))
  mul_one := by
    refine Quotient.ind fun A => ?_
    exact Quotient.sound (IsBrauerEquivalent.of_algEquiv (Algebra.TensorProduct.rid K K A))
  mul_comm := by
    refine Quotient.ind fun A => Quotient.ind fun B => ?_
    exact Quotient.sound (IsBrauerEquivalent.of_algEquiv (Algebra.TensorProduct.comm K A B))
  inv_mul_cancel := by
    refine Quotient.ind fun A => ?_
    exact Quotient.sound (CSA.op_tensor_self A)

@[simp]
theorem mk_mul (A B : CSA.{u, u} K) :
    (⟦A⟧ * ⟦B⟧ : BrauerGroup K) = ⟦CSA.tensor A B⟧ := rfl

@[simp]
theorem mk_one : (1 : BrauerGroup.{u, u} K) = ⟦CSA.one K⟧ := rfl

@[simp]
theorem mk_inv (A : CSA.{u, u} K) : (⟦A⟧ : BrauerGroup K)⁻¹ = ⟦CSA.op A⟧ := rfl

/-- A central simple algebra is trivial in the Brauer group exactly when it is Brauer equivalent
to the base field, that is, when some matrix algebra over it is a matrix algebra over `K`. -/
theorem mk_eq_one_iff (A : CSA.{u, u} K) :
    (⟦A⟧ : BrauerGroup K) = 1 ↔
      ∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧
        Nonempty (Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) K) := by
  rw [mk_one, Quotient.eq]
  rfl

/-- An algebra isomorphic to a nonempty matrix algebra over `K` is trivial in the Brauer group. -/
theorem mk_eq_one_of_algEquiv_matrix {A : CSA.{u, u} K} {n : ℕ} (hn : n ≠ 0)
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) K) : (⟦A⟧ : BrauerGroup K) = 1 :=
  Quotient.sound (IsBrauerEquivalent.of_algEquiv_matrix (B := CSA.one K) hn e)

@[simp]
theorem mk_matrix (n : ℕ) [NeZero n] : (⟦CSA.matrix K n⟧ : BrauerGroup K) = 1 :=
  mk_eq_one_of_algEquiv_matrix (NeZero.ne n) AlgEquiv.refl

end BrauerGroup

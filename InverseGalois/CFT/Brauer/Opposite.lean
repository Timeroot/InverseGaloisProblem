import Mathlib
import InverseGalois.CFT.Brauer.TensorSimple

/-!
# The opposite algebra splits a central simple algebra

Let `K` be a field and `A` a finite-dimensional central simple `K`-algebra. This file identifies
the tensor product `A ⊗[K] Aᵐᵒᵖ` with the endomorphism algebra `Module.End K A`, and hence with a
matrix algebra over `K`. This is the statement that `Aᵐᵒᵖ` represents the inverse of the class of
`A` in the Brauer group of `K`.

The map is the classical one, `a ⊗ₜ op b ↦ (x ↦ a * x * b)`; it is `Mathlib`'s
`AlgHom.mulLeftRight`, here specialised to a field and named `InverseGalois.CFT.tensorOpToEnd`.
Since `Aᵐᵒᵖ` is again central simple, the source is a simple ring by
`IsSimpleRing.tensorProduct_of_isCentral`, so the map is injective; both sides have `K`-dimension
`(finrank K A) ^ 2`, so it is bijective.

## Main results

* `InverseGalois.CFT.tensorOpToEnd`: the canonical map `A ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A`.
* `InverseGalois.CFT.tensorOpEquivEnd`: for `A` a finite-dimensional central simple `K`-algebra,
  the canonical map is an isomorphism.
* `InverseGalois.CFT.tensorOpEquivMatrix`: the induced isomorphism onto a matrix algebra
  attached to a choice of `K`-basis of `A`.
* `InverseGalois.CFT.exists_algEquiv_matrix_tensorOp`: `A ⊗[K] Aᵐᵒᵖ` is isomorphic to a matrix
  algebra `Matrix (Fin n) (Fin n) K`.
-/

universe u v

open scoped TensorProduct

open Module

namespace InverseGalois.CFT

variable (K : Type u) (A : Type v) [Field K] [Ring A] [Algebra K A]

/-- The canonical `K`-algebra homomorphism `A ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A` sending
`a ⊗ₜ op b` to the map `x ↦ a * x * b`. -/
def tensorOpToEnd : A ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A :=
  AlgHom.mulLeftRight K A

@[simp]
theorem tensorOpToEnd_tmul (a b : A) (x : A) :
    tensorOpToEnd K A (a ⊗ₜ[K] MulOpposite.op b) x = a * x * b :=
  AlgHom.mulLeftRight_apply K A a (MulOpposite.op b) x

@[simp]
theorem tensorOpToEnd_tmul' (a : A) (b : Aᵐᵒᵖ) (x : A) :
    tensorOpToEnd K A (a ⊗ₜ[K] b) x = a * x * b.unop :=
  AlgHom.mulLeftRight_apply K A a b x

section FiniteDimensional

variable [FiniteDimensional K A]

/-- Both `A ⊗[K] Aᵐᵒᵖ` and `Module.End K A` have `K`-dimension `(finrank K A) ^ 2`. -/
theorem finrank_tensorOp_eq_finrank_end :
    finrank K (A ⊗[K] Aᵐᵒᵖ) = finrank K (Module.End K A) := by
  rw [Module.finrank_tensorProduct, MulOpposite.finrank, Module.finrank_linearMap]

variable [Algebra.IsCentral K A] [IsSimpleRing A]

omit [FiniteDimensional K A] in
/-- A `K`-algebra map out of the simple ring `A ⊗[K] Aᵐᵒᵖ` is injective. -/
theorem tensorOpToEnd_injective : Function.Injective (tensorOpToEnd K A) := by
  haveI : IsSimpleRing (A ⊗[K] Aᵐᵒᵖ) := IsSimpleRing.tensorProduct_of_isCentral
  exact RingHom.injective (tensorOpToEnd K A).toRingHom

theorem tensorOpToEnd_bijective : Function.Bijective (tensorOpToEnd K A) := by
  refine ⟨tensorOpToEnd_injective K A, ?_⟩
  have hinj : Function.Injective ((tensorOpToEnd K A).toLinearMap) := tensorOpToEnd_injective K A
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_tensorOp_eq_finrank_end K A)).mp hinj

/-- For a finite-dimensional central simple `K`-algebra `A`, the tensor product of `A` with its
opposite algebra is the endomorphism algebra of `A` as a `K`-vector space. -/
noncomputable def tensorOpEquivEnd : A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A :=
  AlgEquiv.ofBijective (tensorOpToEnd K A) (tensorOpToEnd_bijective K A)

@[simp]
theorem tensorOpEquivEnd_apply (x : A ⊗[K] Aᵐᵒᵖ) :
    tensorOpEquivEnd K A x = tensorOpToEnd K A x :=
  rfl

@[simp]
theorem tensorOpEquivEnd_tmul (a b : A) (x : A) :
    tensorOpEquivEnd K A (a ⊗ₜ[K] MulOpposite.op b) x = a * x * b :=
  tensorOpToEnd_tmul K A a b x

variable {A} in
/-- Relative to a choice of `K`-basis of `A`, the algebra `A ⊗[K] Aᵐᵒᵖ` is a matrix algebra
over `K`. -/
noncomputable def tensorOpEquivMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K A) : A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Matrix ι ι K :=
  (tensorOpEquivEnd K A).trans (algEquivMatrix b)

/-- The tensor product of a finite-dimensional central simple `K`-algebra with its opposite
algebra is a matrix algebra over `K`. -/
theorem exists_algEquiv_matrix_tensorOp :
    ∃ n : ℕ, Nonempty (A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  classical
  exact ⟨finrank K A, ⟨tensorOpEquivMatrix K (Module.finBasis K A)⟩⟩

end FiniteDimensional

end InverseGalois.CFT

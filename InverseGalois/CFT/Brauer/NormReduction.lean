/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The norm of a product, and the norm modulo a maximal ideal

The norm of an element of a finite product of algebras is the product of the norms of its
components.  Multiplying together the elements which agree with the given one in a single
coordinate and are one elsewhere recovers the element, so it is enough to treat one such factor,
and multiplication by it is the multiplication by its single coordinate on that factor and the
identity on the others; the determinant of a map which splits as a product of two is the product of
the determinants.

The norm of an element of an algebra which is free of finite rank over the base reduces modulo a
maximal ideal of the base to the norm of the reduction, provided the reduction of the algebra has
the same dimension over the residue field.  A basis of the algebra reduces to a spanning family of
the reduction, which is then a basis by the count, the coefficients of the reduction in it are the
reductions of the coefficients, so the matrix of multiplication is the reduction of the matrix of
multiplication, and the determinant commutes with a ring homomorphism.

## Main results

* `InverseGalois.CFT.norm_pi_eq_prod`: **the norm of an element of a finite product of algebras is
  the product of the norms of its components.**
* `InverseGalois.CFT.quotientBasis`: the basis of the reduction of an algebra modulo a maximal
  ideal of the base induced by a basis of the algebra.
* `InverseGalois.CFT.mk_norm_eq_norm_mk`: **the norm of an element reduces modulo a maximal ideal
  of the base to the norm of its reduction.**

## Tags

norm, determinant, basis, quotient, maximal ideal, residue field, product of algebras
-/

namespace InverseGalois.CFT

open Module Submodule

/-! ### The norm of an element of a finite product -/

section Product

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Type*)
  [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
  [∀ i, Module.Finite R (A i)]

/-- **A finite product of algebras splits off any one of its factors.**  This is the linear form of
the corresponding equivalence of types. -/
def piSplitLinearEquiv (i : ι) : (∀ j, A j) ≃ₗ[R] A i × (∀ j : {j // j ≠ i}, A j) :=
  { Equiv.piSplitAt i A with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- **The norm of an element which is one outside a single coordinate is the norm of that
coordinate.**  Multiplication by such an element is multiplication by the coordinate on the
corresponding factor and the identity on the complementary product. -/
theorem norm_update_one (i : ι) (y : A i) :
    Algebra.norm R (Function.update (1 : ∀ j, A j) i y) = Algebra.norm R y := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  set e : (∀ j, A j) ≃ₗ[R] A i × (∀ j : {j // j ≠ i}, A j) := piSplitLinearEquiv A i with he
  have key : ((e : (∀ j, A j) →ₗ[R] A i × (∀ j : {j // j ≠ i}, A j)) ∘ₗ
      (Algebra.lmul R (∀ j, A j) (Function.update (1 : ∀ j, A j) i y)) ∘ₗ
      ((e.symm : A i × (∀ j : {j // j ≠ i}, A j) →ₗ[R] (∀ j, A j))))
      = LinearMap.prodMap (Algebra.lmul R (A i) y) LinearMap.id := by
    refine LinearMap.ext fun p => ?_
    obtain ⟨a, f⟩ := p
    refine Prod.ext ?_ ?_
    · show (Function.update (1 : ∀ j, A j) i y * _) i = y * a
      simp [he, piSplitLinearEquiv, Equiv.piSplitAt]
    · funext j
      show (Function.update (1 : ∀ j, A j) i y * _) (j : ι) = f j
      rw [Pi.mul_apply, Function.update_of_ne j.2]
      simp [he, piSplitLinearEquiv, Equiv.piSplitAt, j.2]
  rw [← LinearMap.det_conj _ e, key, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

/-- An element of a finite product is the product of the elements which agree with it in a single
coordinate and are one elsewhere. -/
theorem prod_update_one (x : ∀ i, A i) : ∏ i, Function.update (1 : ∀ j, A j) i (x i) = x := by
  funext j
  rw [Finset.prod_apply,
    Finset.prod_eq_single j (fun b _ hb => Function.update_of_ne (Ne.symm hb) _ _) (by simp)]
  exact Function.update_self ..

/-- **The norm of an element of a finite product of algebras is the product of the norms of its
components.** -/
theorem norm_pi_eq_prod (x : ∀ i, A i) : Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  conv_lhs => rw [← prod_update_one A x]
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => norm_update_one A i (x i)

end Product

/-! ### A basis of the reduction modulo a maximal ideal -/

section Quotient

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsMaximal]

attribute [local instance] Ideal.Quotient.field

omit [p.IsMaximal] in
/-- **A spanning family of an algebra reduces to a spanning family of the reduction of the algebra
modulo an ideal of the base.** -/
theorem span_map_quotient_eq_top (s : Set S) (hs : Submodule.span R s = ⊤) :
    Submodule.span (R ⧸ p) ((Ideal.Quotient.mk (Ideal.map (algebraMap R S) p)) '' s) = ⊤ := by
  set f : S →ₗ[R] S ⧸ Ideal.map (algebraMap R S) p :=
    (IsScalarTower.toAlgHom R S (S ⧸ Ideal.map (algebraMap R S) p)).toLinearMap
  have hfc : ⇑f = ⇑(Ideal.Quotient.mk (Ideal.map (algebraMap R S) p)) := rfl
  have H : (Submodule.span (R ⧸ p)
        ((Ideal.Quotient.mk (I := Ideal.map (algebraMap R S) p)) '' s)).restrictScalars R
      = (Submodule.span R s).map f := by
    rw [Submodule.map_span, ← Submodule.restrictScalars_span R (R ⧸ p)
      Ideal.Quotient.mk_surjective, hfc]
  rwa [hs, Submodule.map_top, LinearMap.range_eq_top.mpr (hfc ▸ Ideal.Quotient.mk_surjective),
    Submodule.restrictScalars_eq_top_iff] at H

variable {ι : Type*} [Fintype ι]

/-- **The basis of the reduction of an algebra modulo a maximal ideal of the base induced by a
basis of the algebra**, available whenever the reduction has the dimension the count predicts. -/
noncomputable def quotientBasis (b : Basis ι R S)
    (h : Fintype.card ι = finrank (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p)) :
    Basis ι (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p) :=
  basisOfTopLeSpanOfCardEqFinrank (Ideal.Quotient.mk _ ∘ b)
    (by
      rw [Set.range_comp]
      exact (span_map_quotient_eq_top p _ b.span_eq).ge)
    h

omit [p.IsMaximal] in
/-- The induced basis of the reduction consists of the reductions of the members of the basis. -/
theorem quotientBasis_apply (b : Basis ι R S)
    (h : Fintype.card ι = finrank (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p)) (i : ι) :
    quotientBasis p b h i = Ideal.Quotient.mk _ (b i) := by
  delta quotientBasis
  rw [coe_basisOfTopLeSpanOfCardEqFinrank, Function.comp_apply]

omit [p.IsMaximal] in
/-- The coefficients of a reduction in the induced basis are the reductions of the coefficients. -/
theorem quotientBasis_repr (b : Basis ι R S)
    (h : Fintype.card ι = finrank (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p)) (x : S) (i : ι) :
    (quotientBasis p b h).repr (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk p (b.repr x i) := by
  refine congr_fun (g := Ideal.Quotient.mk p ∘ b.repr x) ?_ i
  apply (Finsupp.linearEquivFunOnFinite (R ⧸ p) _ _).symm.injective
  apply (quotientBasis p b h).repr.symm.injective
  simp only [Finsupp.linearEquivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply (R ⧸ p),
    Fintype.linearCombination_apply]
  simp only [Function.comp_apply, quotientBasis_apply,
    Ideal.Quotient.mk_smul_mk_quotient_map_quotient, ← Algebra.smul_def]
  rw [← map_sum, Basis.sum_repr b x]

variable [DecidableEq ι]

omit [p.IsMaximal] in
/-- The matrix of multiplication in the induced basis is the reduction of the matrix of
multiplication in the given basis. -/
theorem leftMulMatrix_quotientBasis (b : Basis ι R S)
    (h : Fintype.card ι = finrank (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p)) (a : S) :
    Algebra.leftMulMatrix (quotientBasis p b h) (Ideal.Quotient.mk _ a)
      = (Algebra.leftMulMatrix b a).map (Ideal.Quotient.mk p) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    quotientBasis_apply, ← map_mul, quotientBasis_repr]

omit [p.IsMaximal] in
/-- **The norm of an element reduces modulo a maximal ideal of the base to the norm of its
reduction**, whenever the reduction of the algebra has the dimension the rank predicts. -/
theorem mk_norm_eq_norm_mk (b : Basis ι R S)
    (h : Fintype.card ι = finrank (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p)) (a : S) :
    Ideal.Quotient.mk p (Algebra.norm R a)
      = Algebra.norm (R ⧸ p) (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p) a) := by
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (quotientBasis p b h),
    leftMulMatrix_quotientBasis, RingHom.map_det, RingHom.mapMatrix_apply]

end Quotient

end InverseGalois.CFT

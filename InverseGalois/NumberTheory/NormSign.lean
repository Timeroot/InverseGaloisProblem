/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The sign of the norm of an element of a number field

The norm of an element of a number field down to the rationals is the product of its images under
all the complex embeddings, and those embeddings are grouped into infinite places: a real place is
defined by a single embedding, a complex place by an embedding and its conjugate.  The factor
contributed by a complex place is therefore a product of a complex number with its conjugate, a
positive real number, while the factor contributed by a real place is the image of the element
under the associated real embedding.

Consequently the norm is, up to a positive factor, the product of the real embeddings of the
element, and in particular the two have the same sign.  This is the archimedean half of the
product formula, kept as an identity of real numbers rather than of absolute values, and it is
what compares the invariants at the infinite places of a number field with the invariant at the
single infinite place of the rationals.

## Main results

* `InverseGalois.NumberTheory.norm_eq_prod_embedding_of_isReal_mul_prod_normSq`: **the norm of an
  element of a number field is the product of its real embeddings times the product of the squared
  absolute values of its complex ones.**
* `InverseGalois.NumberTheory.norm_mul_prod_embedding_of_isReal_pos`: **the norm of a nonzero
  element and the product of its real embeddings have the same sign.**
* `InverseGalois.NumberTheory.norm_mul_prod_pos`: the same sign comparison for a product taken over
  all the infinite places of a quantity that is trivial at the complex ones.

## Tags

number field, infinite place, real embedding, norm, sign, product formula
-/

open Complex NumberField

open scoped ComplexConjugate

namespace InverseGalois.NumberTheory

/-! ### The complex embeddings above a single infinite place -/

section Fibre

variable {k : Type*} [Field k] [NumberField k] [DecidableEq (InfinitePlace k)]

/-- **The complex embeddings defining a given infinite place are the chosen one and its
conjugate.** -/
theorem filter_mk_eq_pair [DecidableEq (k →+* ℂ)] (w : InfinitePlace k) :
    Finset.univ.filter (fun φ : k →+* ℂ => InfinitePlace.mk φ = w)
      = {InfinitePlace.embedding w,
          ComplexEmbedding.conjugate (InfinitePlace.embedding w)} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  have key : InfinitePlace.mk φ = w ↔ InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
    rw [InfinitePlace.mk_embedding]
  rw [key, InfinitePlace.mk_eq_iff, (ComplexEmbedding.involutive_conjugate k).eq_iff]

/-- The images of an element under the complex embeddings defining a real place multiply out to
its image under the associated real embedding, that place being defined by that embedding
alone. -/
theorem prod_filter_mk_of_isReal {w : InfinitePlace k} (hw : w.IsReal) (x : k) :
    ∏ φ ∈ Finset.univ.filter (fun φ : k →+* ℂ => InfinitePlace.mk φ = w), φ x
      = ((InfinitePlace.embedding_of_isReal hw x : ℝ) : ℂ) := by
  classical
  rw [filter_mk_eq_pair w, InfinitePlace.conjugate_embedding_eq_of_isReal hw,
    Finset.insert_eq_self.mpr (Finset.mem_singleton_self _), Finset.prod_singleton,
    InfinitePlace.embedding_of_isReal_apply hw]

/-- The images of an element under the complex embeddings defining a complex place multiply out to
the squared absolute value of its image under the chosen one, the two embeddings defining that
place being conjugate to one another and distinct. -/
theorem prod_filter_mk_of_isComplex {w : InfinitePlace k} (hw : w.IsComplex) (x : k) :
    ∏ φ ∈ Finset.univ.filter (fun φ : k →+* ℂ => InfinitePlace.mk φ = w), φ x
      = ((Complex.normSq (InfinitePlace.embedding w x) : ℝ) : ℂ) := by
  classical
  have hne : InfinitePlace.embedding w
      ≠ ComplexEmbedding.conjugate (InfinitePlace.embedding w) := by
    intro h
    exact InfinitePlace.isComplex_iff.mp hw (ComplexEmbedding.isReal_iff.mpr h.symm)
  rw [filter_mk_eq_pair w, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq,
    Complex.mul_conj]

end Fibre

/-! ### The norm as a product over the infinite places -/

section NormSign

variable {k : Type*} [Field k] [NumberField k]

open scoped Classical in
/-- **The norm of an element of a number field, read as a complex number, is the product of its
real embeddings times the product of the squared absolute values of its complex ones.**  The norm
is the product over all complex embeddings, and those are grouped into the infinite places, each
real place contributing one embedding and each complex place a conjugate pair. -/
theorem algebraMap_norm_eq_prod_embedding_of_isReal_mul_prod_normSq (x : k) :
    algebraMap ℚ ℂ (Algebra.norm ℚ x)
      = (∏ w : {w : InfinitePlace k // w.IsReal},
            ((InfinitePlace.embedding_of_isReal w.2 x : ℝ) : ℂ))
        * ∏ w : {w : InfinitePlace k // w.IsComplex},
            ((Complex.normSq (InfinitePlace.embedding w.1 x) : ℝ) : ℂ) := by
  classical
  have hequiv : ∏ σ : k →ₐ[ℚ] ℂ, σ x = ∏ φ : k →+* ℂ, φ x :=
    (Fintype.prod_equiv RingHom.equivRatAlgHom (fun φ : k →+* ℂ => φ x)
      (fun σ : k →ₐ[ℚ] ℂ => σ x) fun _ => by simp [RingHom.equivRatAlgHom_apply]).symm
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x, hequiv,
    ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : k →+* ℂ => φ x),
    InfinitePlace.prod_eq_prod_mul_prod]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => prod_filter_mk_of_isReal w.2 x
  · exact Finset.prod_congr rfl fun w _ => prod_filter_mk_of_isComplex w.2 x

open scoped Classical in
/-- **The norm of an element of a number field is the product of its real embeddings times the
product of the squared absolute values of its complex ones.** -/
theorem norm_eq_prod_embedding_of_isReal_mul_prod_normSq (x : k) :
    ((Algebra.norm ℚ x : ℚ) : ℝ)
      = (∏ w : {w : InfinitePlace k // w.IsReal}, InfinitePlace.embedding_of_isReal w.2 x)
        * ∏ w : {w : InfinitePlace k // w.IsComplex},
            Complex.normSq (InfinitePlace.embedding w.1 x) := by
  have h := algebraMap_norm_eq_prod_embedding_of_isReal_mul_prod_normSq x
  rw [eq_ratCast (algebraMap ℚ ℂ), ← Complex.ofReal_prod, ← Complex.ofReal_prod,
    ← Complex.ofReal_mul] at h
  exact_mod_cast h

/-! ### The sign of the norm -/

open scoped Classical in
/-- **The norm of a nonzero element of a number field and the product of its real embeddings have
the same sign**, the complex places contributing a positive factor to the norm. -/
theorem norm_mul_prod_embedding_of_isReal_pos {x : k} (hx : x ≠ 0) :
    0 < ((Algebra.norm ℚ x : ℚ) : ℝ)
      * ∏ w : {w : InfinitePlace k // w.IsReal}, InfinitePlace.embedding_of_isReal w.2 x := by
  have hPne : (∏ w : {w : InfinitePlace k // w.IsReal},
      InfinitePlace.embedding_of_isReal w.2 x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ => (map_ne_zero _).mpr hx
  have hC : 0 < ∏ w : {w : InfinitePlace k // w.IsComplex},
      Complex.normSq (InfinitePlace.embedding w.1 x) :=
    Finset.prod_pos fun w _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hx)
  rw [norm_eq_prod_embedding_of_isReal_mul_prod_normSq x,
    show ∀ P C : ℝ, P * C * P = P ^ 2 * C from fun P C => by ring]
  exact mul_pos ((sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hPne))) hC

/-- **The norm of a nonzero element of a number field has the sign of the product over all infinite
places of a quantity which is its real embedding at a real place and one at a complex place.**  The
complex places drop out of the product, and what is left is the product of the real embeddings. -/
theorem norm_mul_prod_pos {x : k} (hx : x ≠ 0) {f : InfinitePlace k → ℝ}
    (hfr : ∀ (u : InfinitePlace k) (hu : u.IsReal),
      f u = InfinitePlace.embedding_of_isReal hu x)
    (hfc : ∀ u : InfinitePlace k, u.IsComplex → f u = 1) :
    0 < ((Algebra.norm ℚ x : ℚ) : ℝ) * ∏ u : InfinitePlace k, f u := by
  classical
  have hcomplex : (∏ w : {w : InfinitePlace k // w.IsComplex}, f w.1) = 1 :=
    Finset.prod_eq_one fun w _ => hfc w.1 w.2
  have hreal : (∏ w : {w : InfinitePlace k // w.IsReal}, f w.1)
      = ∏ w : {w : InfinitePlace k // w.IsReal}, InfinitePlace.embedding_of_isReal w.2 x :=
    Finset.prod_congr rfl fun w _ => hfr w.1 w.2
  rw [InfinitePlace.prod_eq_prod_mul_prod f, hcomplex, hreal, mul_one]
  exact norm_mul_prod_embedding_of_isReal_pos hx

end NormSign

end InverseGalois.NumberTheory

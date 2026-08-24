/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.PlaceComap

/-!
# The local degree of an extension of number fields

A prime of a number field lies over a prime of a subfield, and the completion at the prime above is
an algebra over the completion at the prime below.  This file shows that this algebra is a finite
extension, of degree at most the degree of the global extension.

The argument is soft.  A finite spanning set of the extension over the base spans, over the
completion of the base, a subspace of the completion of the extension.  That subspace is finite
dimensional, hence closed, and it contains the image of the extension, which is dense.  So it is
everything.

## Main definitions

* `InverseGalois.CFT.instAlgebraAdicCompletion`: the completion at a prime is an algebra over the
  completion at the prime below.
* `InverseGalois.CFT.toAdicCompletion`: the inclusion of a number field into its completion at a
  prime, as a ring homomorphism.

## Main results

* `InverseGalois.CFT.span_image_coe_eq_top`: **the image of a spanning set spans the completion**
  over the completion of the base.
* `InverseGalois.CFT.finiteDimensional_adicCompletion`: **the completion at a prime is a finite
  extension of the completion at the prime below.**
* `InverseGalois.CFT.finrank_adicCompletion_le`: **the local degree is at most the global degree.**

## Tags

number field, completion, local degree, finite extension
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Module

section LocalDegree

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

open scoped Valued in
/-- The completion of a number field at a finite place is a nontrivially normed field. -/
noncomputable instance instNontriviallyNormedFieldAdicCompletion (F : Type*) [Field F]
    [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : NontriviallyNormedField (v.adicCompletion F) :=
  Valued.toNontriviallyNormedField

/-- **The completion at a prime is an algebra over the completion at the prime below.** -/
noncomputable instance instAlgebraAdicCompletion (w : HeightOneSpectrum (𝓞 K)) :
    Algebra ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) :=
  (adicCompletionComap (𝓞 k) w).toAlgebra

variable (k) in
/-- The structure map of the completion at a prime over the completion at the prime below is the
map induced by the inclusion of the base field. -/
theorem algebraMap_adicCompletion (w : HeightOneSpectrum (𝓞 K)) :
    algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
      = adicCompletionComap (𝓞 k) w := rfl

/-- The completion at a prime is a topological algebra over the completion at the prime below. -/
instance instContinuousSMulAdicCompletion (w : HeightOneSpectrum (𝓞 K)) :
    ContinuousSMul ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) where
  continuous_smul := by
    have h : Continuous fun p : (primeUnder (𝓞 k) w).adicCompletion k × w.adicCompletion K =>
        adicCompletionComap (𝓞 k) w p.1 * p.2 :=
      ((continuous_adicCompletionComap (𝓞 k) w).comp continuous_fst).mul continuous_snd
    simpa only [Algebra.smul_def, algebraMap_adicCompletion] using h

/-- The inclusion of a number field into its completion at a prime. -/
noncomputable def toAdicCompletion (w : HeightOneSpectrum (𝓞 K)) : K →+* w.adicCompletion K :=
  (UniformSpace.Completion.coeRingHom).comp (WithVal.equiv (w.valuation K)).symm.toRingHom

@[simp]
theorem toAdicCompletion_apply (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    toAdicCompletion w x = ((x : WithVal (w.valuation K)) : w.adicCompletion K) := rfl

variable (k) in
/-- Scaling by the base field before completing is scaling by the completion of the base
afterwards. -/
theorem toAdicCompletion_smul (w : HeightOneSpectrum (𝓞 K)) (c : k) (x : K) :
    toAdicCompletion w (c • x)
      = ((c : WithVal ((primeUnder (𝓞 k) w).valuation k)) :
          (primeUnder (𝓞 k) w).adicCompletion k) • toAdicCompletion w x := by
  rw [Algebra.smul_def, Algebra.smul_def, algebraMap_adicCompletion, adicCompletionComap_coe,
    map_mul]
  rfl

/-- The image of the extension is dense in its completion. -/
theorem denseRange_toAdicCompletion (w : HeightOneSpectrum (𝓞 K)) :
    DenseRange (toAdicCompletion w) :=
  UniformSpace.Completion.denseRange_coe (α := WithVal (w.valuation K))

variable (k) in
/-- **The image of a spanning set of the extension spans the completion at a prime** over the
completion at the prime below: the span is finite dimensional, hence closed, and it contains a
dense set. -/
theorem span_image_coe_eq_top (w : HeightOneSpectrum (𝓞 K)) {s : Set K} (hs : s.Finite)
    (hspan : Submodule.span k s = ⊤) :
    Submodule.span ((primeUnder (𝓞 k) w).adicCompletion k) (toAdicCompletion w '' s) = ⊤ := by
  set S := Submodule.span ((primeUnder (𝓞 k) w).adicCompletion k) (toAdicCompletion w '' s)
    with hS
  have hfd : FiniteDimensional ((primeUnder (𝓞 k) w).adicCompletion k) S :=
    hS ▸ FiniteDimensional.span_of_finite _ (hs.image _)
  have hclosed : IsClosed (S : Set (w.adicCompletion K)) := S.closed_of_finiteDimensional
  have hmem : ∀ x : K, toAdicCompletion w x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span k s := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simpa only [map_zero] using S.zero_mem
    | add a b _ _ ha hb => simpa only [map_add] using S.add_mem ha hb
    | smul c a _ ha =>
      rw [toAdicCompletion_smul]
      exact S.smul_mem _ ha
  have huniv : (S : Set (w.adicCompletion K)) = Set.univ := by
    rw [← hclosed.closure_eq]
    refine (Dense.mono ?_ (denseRange_toAdicCompletion w)).closure_eq
    rintro _ ⟨x, rfl⟩
    exact hmem x
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  have hx : x ∈ (S : Set (w.adicCompletion K)) := huniv ▸ Set.mem_univ x
  exact hx

variable (k) in
/-- **The completion of a number field at a prime is a finite extension of the completion of a
subfield at the prime below.** -/
instance finiteDimensional_adicCompletion (w : HeightOneSpectrum (𝓞 K)) :
    FiniteDimensional ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) := by
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule k K).FG)
  haveI hfd : FiniteDimensional ((primeUnder (𝓞 k) w).adicCompletion k)
      (Submodule.span ((primeUnder (𝓞 k) w).adicCompletion k)
        (toAdicCompletion w '' (t : Set K))) :=
    FiniteDimensional.span_of_finite _ (t.finite_toSet.image _)
  rw [span_image_coe_eq_top k w t.finite_toSet ht] at hfd
  exact Module.Finite.equiv Submodule.topEquiv

variable (k) in
/-- **The local degree is at most the global degree**: over the completion at the prime below, the
completion at a prime has degree at most the degree of the extension. -/
theorem finrank_adicCompletion_le (w : HeightOneSpectrum (𝓞 K)) :
    finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) ≤ finrank k K := by
  classical
  let b := finBasis k K
  let t : Finset (w.adicCompletion K) := Finset.univ.image fun i => toAdicCompletion w (b i)
  have hcoe : (t : Set (w.adicCompletion K)) = toAdicCompletion w '' Set.range b := by
    simp only [t, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact Set.range_comp _ _
  have htop : Submodule.span ((primeUnder (𝓞 k) w).adicCompletion k)
      (t : Set (w.adicCompletion K)) = ⊤ := by
    rw [hcoe]
    exact span_image_coe_eq_top k w (Set.finite_range b) b.span_eq
  have hle := finrank_span_le_card (R := (primeUnder (𝓞 k) w).adicCompletion k)
    (t : Set (w.adicCompletion K))
  rw [htop, finrank_top, Finset.toFinset_coe] at hle
  exact hle.trans (Finset.card_image_le.trans (by simp))

end LocalDegree

end InverseGalois.CFT

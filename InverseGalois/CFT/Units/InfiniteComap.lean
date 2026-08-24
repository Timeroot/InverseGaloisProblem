/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.InfiniteAction

/-!
# The completion at an infinite place over the completion below

An infinite place of an extension of number fields restricts to an infinite place of the base, and
the absolute value of an element of the base at the place above is literally its absolute value at
the place below.  The inclusion of the base into the extension is therefore an exact isometry for
the two metrics, with no ramification index intervening, and it extends to an isometric embedding
of the completion of the base at the place below into the completion of the extension at the place
above.

The completion of the extension is then an algebra over the completion of the base, and it is a
finite extension: a finite spanning set of the extension over the base spans, over the completion
of the base, a subspace of the completion of the extension which is finite dimensional, hence
closed, and which contains the dense image of the extension.

## Main definitions

* `InverseGalois.CFT.withAbsComap`: the inclusion of the base field into the extension, read as a
  map of normed fields.
* `InverseGalois.CFT.infiniteCompletionComap`: **the induced map on completions**, from the
  completion of the base at the place below to the completion of the extension at the place above.
* `InverseGalois.CFT.instAlgebraInfiniteCompletion`: the completion at an infinite place is an
  algebra over the completion at the place below.

## Main results

* `InverseGalois.CFT.norm_infiniteCompletionComap`: **the map on completions is an isometry.**
* `InverseGalois.CFT.span_image_algebraMap_infiniteCompletion_eq_top`: **the image of a spanning
  set spans the completion** over the completion of the base.
* `InverseGalois.CFT.finiteDimensional_infiniteCompletion`: **the completion at an infinite place
  is a finite extension of the completion at the place below.**
* `InverseGalois.CFT.finrank_infiniteCompletion_le`: **the local degree is at most the global
  degree.**

## Tags

number field, infinite place, completion, local degree, finite extension
-/

namespace InverseGalois.CFT

open Module NumberField NumberField.InfinitePlace

/-! ### The inclusion of the base field as a map of normed fields -/

section WithAbs

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (w : InfinitePlace K)

variable (k) in
/-- **The inclusion of the base field into the extension, read as a map from the base field with
the metric of the place below to the extension with the metric of the place above.** -/
def withAbsComap : WithAbs (w.comap (algebraMap k K)).1 →+* WithAbs w.1 := algebraMap k K

variable (k) in
@[simp]
theorem withAbsComap_apply (x : WithAbs (w.comap (algebraMap k K)).1) :
    WithAbs.equiv w.1 (withAbsComap k w x)
      = algebraMap k K (WithAbs.equiv (w.comap (algebraMap k K)).1 x) := rfl

variable (k) in
/-- **The inclusion of the base field preserves absolute values exactly**: the place below is by
definition the restriction of the place above. -/
@[simp]
theorem norm_withAbsComap (x : WithAbs (w.comap (algebraMap k K)).1) :
    ‖withAbsComap k w x‖ = ‖x‖ := by
  rw [WithAbs.norm_eq_abv, WithAbs.norm_eq_abv]
  rfl

variable (k) in
/-- The inclusion of the base field into the extension is an isometry for the metrics of the two
places. -/
theorem isometry_withAbsComap : Isometry (withAbsComap k w) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_withAbsComap k w)

end WithAbs

/-! ### The induced map on the completions -/

section Completion

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (w : InfinitePlace K)

variable (k) in
/-- **The map induced on the completions** by the inclusion of the base field into the extension:
the completion of the base at the place below maps to the completion of the extension at the place
above. -/
noncomputable def infiniteCompletionComap :
    (w.comap (algebraMap k K)).Completion →+* w.Completion :=
  UniformSpace.Completion.mapRingHom (withAbsComap k w) (isometry_withAbsComap k w).continuous

variable (k) in
/-- The map induced on the completions extends the inclusion of the base field. -/
@[simp]
theorem infiniteCompletionComap_coe (x : WithAbs (w.comap (algebraMap k K)).1) :
    infiniteCompletionComap k w (x : (w.comap (algebraMap k K)).Completion)
      = ((withAbsComap k w x : WithAbs w.1) : w.Completion) :=
  UniformSpace.Completion.mapRingHom_coe (isometry_withAbsComap k w).continuous x

variable (k) in
/-- **The map induced on the completions is continuous**, being the extension by continuity of a
continuous map. -/
theorem continuous_infiniteCompletionComap :
    Continuous (infiniteCompletionComap k w) :=
  UniformSpace.Completion.continuous_map

variable (k) in
/-- **The map induced on the completions is an isometry**: the two sides are continuous and agree
on the dense image of the base field. -/
@[simp]
theorem norm_infiniteCompletionComap (z : (w.comap (algebraMap k K)).Completion) :
    ‖infiniteCompletionComap k w z‖ = ‖z‖ := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq (continuous_norm.comp (continuous_infiniteCompletionComap k w))
      continuous_norm
  · intro x
    rw [infiniteCompletionComap_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe, norm_withAbsComap]

variable (k) in
/-- The map induced on the completions is injective, the completion of the base being a field. -/
theorem infiniteCompletionComap_injective :
    Function.Injective (infiniteCompletionComap k w) :=
  (infiniteCompletionComap k w).injective

end Completion

/-! ### The algebra structure on the completion above -/

section AlgebraStructure

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (w : InfinitePlace K)

/-- Multiplying by a fixed element of the base field is uniformly continuous for the metric of an
infinite place of the extension. -/
instance instUniformContinuousConstSMulWithAbs :
    UniformContinuousConstSMul k (WithAbs w.1) := by
  refine ⟨fun c => ?_⟩
  simp_rw [Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul (WithAbs w.1)).uniformContinuous_const_smul _

/-- The completion of a field at an infinite place is a nontrivially normed field: the absolute
value of two is two, because the place is archimedean. -/
noncomputable instance instNontriviallyNormedFieldInfiniteCompletion {F : Type*} [Field F]
    (v : InfinitePlace F) : NontriviallyNormedField v.Completion :=
  { (inferInstance : NormedField v.Completion) with
    non_trivial := by
      refine ⟨2, ?_⟩
      have h : ‖Completion.extensionEmbedding v 2‖ = ‖(2 : v.Completion)‖ :=
        (AddMonoidHomClass.isometry_iff_norm _).mp (Completion.isometry_extensionEmbedding v) 2
      rw [map_ofNat] at h
      rw [← h]
      norm_num }

/-- **The completion at an infinite place is an algebra over the completion at the place
below.** -/
noncomputable instance instAlgebraInfiniteCompletion :
    Algebra (w.comap (algebraMap k K)).Completion w.Completion :=
  (infiniteCompletionComap k w).toAlgebra

variable (k) in
/-- The structure map of the completion at an infinite place over the completion at the place below
is the map induced by the inclusion of the base field. -/
theorem algebraMap_infiniteCompletion :
    algebraMap (w.comap (algebraMap k K)).Completion w.Completion = infiniteCompletionComap k w :=
  rfl

/-- The completion at an infinite place is a topological algebra over the completion at the place
below. -/
instance instContinuousSMulInfiniteCompletion :
    ContinuousSMul (w.comap (algebraMap k K)).Completion w.Completion where
  continuous_smul := by
    have h : Continuous fun p : (w.comap (algebraMap k K)).Completion × w.Completion =>
        infiniteCompletionComap k w p.1 * p.2 :=
      ((continuous_infiniteCompletionComap k w).comp continuous_fst).mul continuous_snd
    simpa only [Algebra.smul_def, algebraMap_infiniteCompletion] using h

/-- The tower of the base field, the completion of the base and the completion of the
extension. -/
instance instIsScalarTowerBaseInfiniteCompletion :
    IsScalarTower k (w.comap (algebraMap k K)).Completion w.Completion :=
  IsScalarTower.of_algebraMap_eq fun c => (infiniteCompletionComap_coe k w c).symm

/-- The tower of the base field, the extension and the completion of the extension. -/
instance instIsScalarTowerFieldInfiniteCompletion : IsScalarTower k K w.Completion :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The image of the extension is dense in its completion at an infinite place. -/
theorem denseRange_algebraMap_infiniteCompletion :
    DenseRange (algebraMap K w.Completion) :=
  UniformSpace.Completion.denseRange_coe (α := WithAbs w.1)

variable (k) in
/-- Scaling by the base field before completing is scaling by the completion of the base
afterwards. -/
theorem algebraMap_infiniteCompletion_smul (c : k) (x : K) :
    algebraMap K w.Completion (c • x)
      = (algebraMap k (w.comap (algebraMap k K)).Completion c) • algebraMap K w.Completion x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

end AlgebraStructure

/-! ### The completion above is a finite extension of the completion below -/

section LocalDegree

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (w : InfinitePlace K)

variable (k) in
omit [NumberField k] [NumberField K] in
/-- **The image of a spanning set of the extension spans the completion at an infinite place** over
the completion at the place below: the span is finite dimensional, hence closed, and it contains a
dense set. -/
theorem span_image_algebraMap_infiniteCompletion_eq_top {s : Set K} (hs : s.Finite)
    (hspan : Submodule.span k s = ⊤) :
    Submodule.span (w.comap (algebraMap k K)).Completion (algebraMap K w.Completion '' s) = ⊤ := by
  set S := Submodule.span (w.comap (algebraMap k K)).Completion (algebraMap K w.Completion '' s)
    with hS
  have hfd : FiniteDimensional (w.comap (algebraMap k K)).Completion S :=
    hS ▸ FiniteDimensional.span_of_finite _ (hs.image _)
  have hclosed : IsClosed (S : Set w.Completion) := S.closed_of_finiteDimensional
  have hmem : ∀ x : K, algebraMap K w.Completion x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span k s := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simpa only [map_zero] using S.zero_mem
    | add a b _ _ ha hb => simpa only [map_add] using S.add_mem ha hb
    | smul c a _ ha =>
      rw [algebraMap_infiniteCompletion_smul k w]
      exact S.smul_mem _ ha
  have huniv : (S : Set w.Completion) = Set.univ := by
    rw [← hclosed.closure_eq]
    refine (Dense.mono ?_ (denseRange_algebraMap_infiniteCompletion w)).closure_eq
    rintro _ ⟨x, rfl⟩
    exact hmem x
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  have hx : x ∈ (S : Set w.Completion) := huniv ▸ Set.mem_univ x
  exact hx

variable (k) in
/-- **The completion of a number field at an infinite place is a finite extension of the completion
of a subfield at the place below.** -/
instance finiteDimensional_infiniteCompletion :
    FiniteDimensional (w.comap (algebraMap k K)).Completion w.Completion := by
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule k K).FG)
  haveI hfd : FiniteDimensional (w.comap (algebraMap k K)).Completion
      (Submodule.span (w.comap (algebraMap k K)).Completion
        (algebraMap K w.Completion '' (t : Set K))) :=
    FiniteDimensional.span_of_finite _ (t.finite_toSet.image _)
  rw [span_image_algebraMap_infiniteCompletion_eq_top k w t.finite_toSet ht] at hfd
  exact Module.Finite.equiv Submodule.topEquiv

variable (k) in
/-- **The local degree is at most the global degree**: over the completion at the place below, the
completion at an infinite place has degree at most the degree of the extension. -/
theorem finrank_infiniteCompletion_le :
    finrank (w.comap (algebraMap k K)).Completion w.Completion ≤ finrank k K := by
  classical
  let b := finBasis k K
  let t : Finset w.Completion := Finset.univ.image fun i => algebraMap K w.Completion (b i)
  have hcoe : (t : Set w.Completion) = algebraMap K w.Completion '' Set.range b := by
    simp only [t, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact Set.range_comp _ _
  have htop : Submodule.span (w.comap (algebraMap k K)).Completion (t : Set w.Completion) = ⊤ := by
    rw [hcoe]
    exact span_image_algebraMap_infiniteCompletion_eq_top k w (Set.finite_range b) b.span_eq
  have hle := finrank_span_le_card (R := (w.comap (algebraMap k K)).Completion)
    (t : Set w.Completion)
  rw [htop, finrank_top, Finset.toFinset_coe] at hle
  exact hle.trans (Finset.card_image_le.trans (by simp))

end LocalDegree

end InverseGalois.CFT

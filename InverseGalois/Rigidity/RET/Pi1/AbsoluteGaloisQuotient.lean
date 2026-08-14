/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.BaseTransport
import InverseGalois.Rigidity.RET.Existence

/-!
# Galois groups over a field are the finite continuous quotients of its absolute Galois group

For a field `K` with separable closure `Ω`, a finite group `G` occurs as `Gal(L/K)` for some finite
Galois extension `L/K` **iff** there is a continuous surjection `Gal(Ω/K) ↠ G` onto `G` with its
discrete topology.  This is the fundamental theorem of infinite Galois theory in existential form,
and it is the field-theoretic shadow of the étale statement "`G` is a finite quotient of the étale
fundamental group of `Spec K`".

Applied to `K = ℚ̄(T)` it rewrites the target of the Riemann Existence Theorem
(`IsGeometricGaloisCover`) as a statement about a single profinite group, the absolute Galois group
of the geometric function field — the shape link **A** of `Pi1/GAGA_DREAM.md` asks for.

## Main definitions / results

* `Rigidity.RET.IsGaloisGroupOver K G` — `G` is the Galois group of some finite Galois extension of
  `K`; `IsGeometricGaloisCover` is this predicate for `K = ℚ̄(T)`.
* `Rigidity.RET.isGaloisGroupOver_of_continuousSurjective` — a continuous surjection
  `Gal(Ω/K) ↠ G` produces the finite Galois extension (its fixed field).
* `Rigidity.RET.exists_continuousSurjective_of_isGaloisGroupOver` — conversely, restriction along an
  embedding of `L` into `Ω` gives a continuous surjection.
* `Rigidity.RET.isGaloisGroupOver_iff_continuousSurjective` — the two directions assembled.
* `Rigidity.RET.isGeometricGaloisCover_iff_absoluteGalois` — the specialization to `ℚ̄(T)`.
* `Rigidity.RET.IsGaloisGroupOver.of_ringEquiv` — being a Galois group over `K` depends on `K`
  only up to isomorphism.
* `Rigidity.RET.IsGaloisGroupOver.of_surjective`, `Rigidity.RET.IsGeometricGaloisCover.of_surjective`
  — both predicates are closed under quotients of the group.
-/

namespace Rigidity.RET

open IntermediateField

/-- **`G` is a Galois group over `K`**: there is a finite Galois extension `L / K` with
`Gal(L/K) ≃* G`.  For `K = ℚ̄(T)` this is `IsGeometricGaloisCover`. -/
def IsGaloisGroupOver (K : Type) [Field K] (G : Type*) [Group G] : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (_ : IsGalois K L),
    Nonempty ((L ≃ₐ[K] L) ≃* G)

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- **From a continuous finite quotient of `Gal(Ω/K)` to a finite Galois extension.**

The kernel of a continuous surjection onto a finite discrete group is an open — hence closed —
normal subgroup; its fixed field is a finite Galois extension of `K` whose Galois group is the
quotient by the kernel, i.e. `G`. -/
theorem isGaloisGroupOver_of_continuousSurjective
    (f : (Ω ≃ₐ[K] Ω) →* G) (hcont : Continuous f) (hsurj : Function.Surjective f) :
    IsGaloisGroupOver K G := by
  have hker_open : IsOpen ((f.ker : Subgroup (Ω ≃ₐ[K] Ω)) : Set (Ω ≃ₐ[K] Ω)) :=
    (isOpen_discrete ({1} : Set G)).preimage hcont
  have hker_closed : IsClosed ((f.ker : Subgroup (Ω ≃ₐ[K] Ω)) : Set (Ω ≃ₐ[K] Ω)) :=
    Subgroup.isClosed_of_isOpen _ hker_open
  let H : ClosedSubgroup (Ω ≃ₐ[K] Ω) := ⟨f.ker, hker_closed⟩
  haveI : H.toSubgroup.Normal := f.normal_ker
  have hfix : (fixedField H.toSubgroup).fixingSubgroup = f.ker :=
    InfiniteGalois.fixingSubgroup_fixedField H
  haveI hfin : FiniteDimensional K (fixedField H.toSubgroup) := by
    refine (InfiniteGalois.isOpen_iff_finite (fixedField H.toSubgroup)).mp ?_
    rw [hfix]
    exact hker_open
  haveI hgal : IsGalois K (fixedField H.toSubgroup) :=
    (InfiniteGalois.normal_iff_isGalois (fixedField H.toSubgroup)).mp (by rw [hfix]; infer_instance)
  exact ⟨fixedField H.toSubgroup, inferInstance, inferInstance, hfin, hgal,
    ⟨(InfiniteGalois.normalAutEquivQuotient H).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩⟩

omit [DiscreteTopology G] in
/-- **From a finite Galois extension to a continuous finite quotient of `Gal(Ω/K)`.**

Embed `L` into the algebraically closed `Ω`; the image is a normal intermediate field, and
restriction `Gal(Ω/K) → Gal(L/K)` is a continuous surjection. -/
theorem exists_continuousSurjective_of_isGaloisGroupOver [IsAlgClosed Ω]
    (h : IsGaloisGroupOver K G) :
    ∃ f : (Ω ≃ₐ[K] Ω) →* G, Continuous f ∧ Function.Surjective f := by
  obtain ⟨L, _, _, hfd, hgal, ⟨e⟩⟩ := h
  haveI := hfd
  haveI := hgal
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let ψ : L →ₐ[K] Ω := IsAlgClosed.lift
  let E : IntermediateField K Ω := ψ.fieldRange
  let hLE : L ≃ₐ[K] E := AlgEquiv.ofInjectiveField ψ
  haveI : Normal K E := Normal.of_algEquiv hLE
  haveI : FiniteDimensional K E := hLE.toLinearEquiv.finiteDimensional
  refine ⟨(e.toMonoidHom.comp (AlgEquiv.autCongr hLE).symm.toMonoidHom).comp
      (AlgEquiv.restrictNormalHom E), ?_, ?_⟩
  · simp only [MonoidHom.coe_comp]
    exact continuous_of_discreteTopology.comp (InfiniteGalois.restrictNormalHom_continuous E)
  · exact e.surjective.comp
      ((AlgEquiv.autCongr hLE).symm.surjective.comp (AlgEquiv.restrictNormalHom_surjective Ω))

/-- **The finite Galois extensions of `K` are the finite continuous quotients of `Gal(Ω/K)`.**

The existential form of the fundamental theorem of infinite Galois theory: a finite group `G` is a
Galois group over `K` iff the absolute Galois group of `K` surjects continuously onto it. -/
theorem isGaloisGroupOver_iff_continuousSurjective [IsAlgClosed Ω] :
    IsGaloisGroupOver K G ↔
      ∃ f : (Ω ≃ₐ[K] Ω) →* G, Continuous f ∧ Function.Surjective f :=
  ⟨exists_continuousSurjective_of_isGaloisGroupOver,
    fun ⟨f, hc, hs⟩ => isGaloisGroupOver_of_continuousSurjective f hc hs⟩

/-- `IsGeometricGaloisCover` is `IsGaloisGroupOver` for the geometric function field `ℚ̄(T)`. -/
theorem isGeometricGaloisCover_iff_isGaloisGroupOver (G : Type) [Group G] :
    IsGeometricGaloisCover G ↔ IsGaloisGroupOver GeomFunctionField G :=
  Iff.rfl

/-- **The Riemann Existence target as a statement about one profinite group.**

A finite group is realized by a geometric Galois cover of `ℙ¹_ℚ̄` exactly when the absolute Galois
group of `ℚ̄(T)` — the étale fundamental group of the generic point of `ℙ¹_ℚ̄` — surjects
continuously onto it.  This is link **A** of `Pi1/GAGA_DREAM.md` at the level of the full
fundamental group: the algebraic side of the Riemann Existence comparison, with no geometry left in
it beyond the field `ℚ̄(T)` itself. -/
theorem isGeometricGaloisCover_iff_absoluteGalois
    (G : Type) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] :
    IsGeometricGaloisCover G ↔
      ∃ f : (AlgebraicClosure GeomFunctionField ≃ₐ[GeomFunctionField]
              AlgebraicClosure GeomFunctionField) →* G,
        Continuous f ∧ Function.Surjective f :=
  isGaloisGroupOver_iff_continuousSurjective

section Finite

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/-- **A quotient of the Galois group of a finite Galois extension is again a Galois group.**

Any surjection `Gal(E/F) ↠ G` realizes `G` as the Galois group of the fixed field of its kernel:
in the finite-dimensional case the Krull topology is discrete, so no continuity hypothesis is
needed. -/
theorem isGaloisGroupOver_of_surjective [FiniteDimensional F E] [IsGalois F E]
    {G : Type} [Group G] (f : (E ≃ₐ[F] E) →* G) (hsurj : Function.Surjective f) :
    IsGaloisGroupOver F G := by
  letI : TopologicalSpace G := ⊥
  haveI : DiscreteTopology G := ⟨rfl⟩
  exact isGaloisGroupOver_of_continuousSurjective f continuous_of_discreteTopology hsurj

end Finite

/-- **Being a Galois group over `K` depends on `K` only up to isomorphism.**

An isomorphism `e : F ≃+* K` makes any Galois extension `L / F` into a Galois extension `L / K`,
by letting `K` act through `e⁻¹`; the tower `F → K → L` it creates has an isomorphism at the bottom,
so all of finiteness, normality, separability and the automorphism group are carried across. -/
theorem IsGaloisGroupOver.of_ringEquiv {F K : Type} [Field F] [Field K] {G : Type*} [Group G]
    (e : F ≃+* K) (h : IsGaloisGroupOver F G) : IsGaloisGroupOver K G := by
  obtain ⟨L, _, _, _, _, ⟨φ⟩⟩ := h
  letI : Algebra K L := ((algebraMap F L).comp (e.symm : K →+* F)).toAlgebra
  letI : Algebra F K := (e : F →+* K).toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra]
  have hsurj : Function.Surjective (algebraMap F K) := by
    simpa [RingHom.algebraMap_toAlgebra] using e.surjective
  haveI : FiniteDimensional K L := Module.Finite.right F K L
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois F K L
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(autCongrOfSurjective hsurj).trans φ⟩⟩

/-- **Galois groups over a fixed field are closed under quotients.**

If `G` is the Galois group of a finite Galois extension of `K` and `G ↠ H`, then so is `H`: take
the fixed field of the kernel. -/
theorem IsGaloisGroupOver.of_surjective {K : Type} [Field K] {G H : Type} [Group G] [Group H]
    (h : IsGaloisGroupOver K G) (f : G →* H) (hf : Function.Surjective f) :
    IsGaloisGroupOver K H := by
  obtain ⟨L, _, _, _, _, ⟨e⟩⟩ := h
  exact isGaloisGroupOver_of_surjective (f.comp e.toMonoidHom) (hf.comp e.surjective)

/-- **Geometric Galois covers of the line are closed under quotients of the covering group.**

A quotient of a group realized by a finite Galois extension of `ℚ̄(T)` is realized by the
subextension fixed by the kernel. -/
theorem IsGeometricGaloisCover.of_surjective {G H : Type} [Group G] [Group H]
    (h : IsGeometricGaloisCover G) (f : G →* H) (hf : Function.Surjective f) :
    IsGeometricGaloisCover H :=
  IsGaloisGroupOver.of_surjective h f hf

end Rigidity.RET

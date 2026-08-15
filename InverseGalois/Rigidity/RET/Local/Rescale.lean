/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Local.PuiseuxRoot

/-!
# Rotating the local coordinate of a Puiseux embedding

A Puiseux embedding of index `e` at a point `s` writes the coordinate of the line as `s + u ^ e`.
That expression is unchanged when the local coordinate is rotated by an `e`-th root of unity, so
rotating `u` is a symmetry of the embedding *relative to the line*: it moves the embedding of the
function field of the cover without moving the embedding of the rational function field.

This file sets up the rotation and records what it does.  Rescaling a formal power series by a
non-zero scalar is a ring automorphism which preserves the constant coefficient, hence the order of
vanishing, hence the place cut out by the embedding; and it fixes the image of the Kummer
substitution as soon as the scalar is an `e`-th root of unity.  Consequently a deck transformation
which the embedding turns into a rotation stabilizes the place of the cover the embedding cuts out,
and therefore lies in the inertia group there — the residue field of a geometric place is
algebraically closed, so the decomposition group is the inertia group.

## Main definitions

* `Rigidity.RET.laurentRescale` — rescaling the local coordinate, on formal Laurent series.

## Main results

* `Rigidity.RET.rescale_kummerSubst` — a root of unity of order dividing the index fixes the image
  of the Kummer substitution.
* `Rigidity.RET.PuiseuxEmbedding.hom_algebraMap_ratFunc` — a Puiseux embedding restricts to the
  Kummer substitution on the whole rational function field.
* `Rigidity.RET.PuiseuxEmbedding.mem_geomInertia_of_rescale` — a deck transformation that the
  embedding turns into a rotation lies in the inertia group of the place it cuts out.
* `Rigidity.RET.PuiseuxEmbedding.exists_deck_rescale` — every admissible rotation is realized by a
  deck transformation.
* `Rigidity.RET.LineCover.exists_isInertiaAt_of_puiseux` — a Puiseux embedding of index `e` at a
  point produces an inertia element there for every `e`-th root of unity.
-/

open Polynomial GeomAKLB
open scoped Pointwise

noncomputable section

namespace Rigidity.RET

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB GeomAKLB.instTorsionFree

/-! ### Rescaling formal series -/

section Series

variable {K : Type} [Field K]

theorem constantCoeff_rescale (a : K) (f : PowerSeries K) :
    PowerSeries.constantCoeff (PowerSeries.rescale a f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale, pow_zero, one_mul]

/-- Rescaling does not change the order of vanishing at the origin. -/
theorem X_dvd_rescale_iff (a : K) (f : PowerSeries K) :
    (PowerSeries.X : PowerSeries K) ∣ PowerSeries.rescale a f ↔ (PowerSeries.X : PowerSeries K) ∣ f
    := by
  rw [PowerSeries.X_dvd_iff, PowerSeries.X_dvd_iff, constantCoeff_rescale]

theorem rescale_C (a x : K) : PowerSeries.rescale a (PowerSeries.C x) = PowerSeries.C x := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl, pow_zero, one_mul]
  · rw [if_neg hn, mul_zero]

/-- **Rescaling the local coordinate**, on formal Laurent series.  It is the unique extension to
the fraction field of the rescaling of formal power series. -/
def laurentRescale {ζ : K} (hζ : ζ ≠ 0) : LaurentSeries K →+* LaurentSeries K :=
  IsFractionRing.lift (A := PowerSeries K)
    (g := (algebraMap (PowerSeries K) (LaurentSeries K)).comp (PowerSeries.rescale ζ))
    ((IsFractionRing.injective (PowerSeries K) (LaurentSeries K)).comp
      (PowerSeries.rescale_injective hζ))

@[simp] theorem laurentRescale_algebraMap {ζ : K} (hζ : ζ ≠ 0) (f : PowerSeries K) :
    laurentRescale hζ (algebraMap (PowerSeries K) (LaurentSeries K) f)
      = algebraMap (PowerSeries K) (LaurentSeries K) (PowerSeries.rescale ζ f) :=
  IsFractionRing.lift_algebraMap _ f

end Series

/-! ### Rotations fix the Kummer substitution -/

section Kummer

variable {K : Type} [Field K] [Algebra k K]

/-- **A root of unity whose order divides the index fixes the image of the Kummer
substitution**: the coordinate of the line is `s + u ^ e`, which does not see a rotation of `u` by
such a root of unity. -/
theorem rescale_kummerSubst {ζ : K} {e : ℕ} (hζ : ζ ^ e = 1) (s : k) (p : Polynomial k) :
    PowerSeries.rescale ζ (kummerSubst K s e p) = kummerSubst K s e p := by
  have h : (PowerSeries.rescale ζ).comp (kummerSubst K s e) = kummerSubst K s e := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [RingHom.comp_apply, kummerSubst_C, rescale_C]
    · rw [RingHom.comp_apply, kummerSubst_X, map_add, rescale_C, map_pow, PowerSeries.rescale_X,
        mul_pow, ← map_pow, hζ, map_one, one_mul]
  exact congrArg (fun f => f p) h

theorem laurentRescale_kummerLift {ζ : K} (hζ0 : ζ ≠ 0) {e : ℕ} (hζ : ζ ^ e = 1) (s : k)
    (he : 0 < e) (x : RatFunc k) :
    laurentRescale hζ0 (kummerLift K s he x) = kummerLift K s he x := by
  have h : (laurentRescale hζ0).comp (kummerLift K s he) = kummerLift K s he := by
    refine IsFractionRing.ringHom_ext (A := Polynomial k) fun p => ?_
    rw [RingHom.comp_apply, kummerLift_algebraMap, laurentRescale_algebraMap,
      rescale_kummerSubst hζ]
  exact congrArg (fun f => f x) h

end Kummer

/-! ### Simple extensions -/

/-- **Every element of a simple algebraic extension is a polynomial in the generator.** -/
theorem exists_aeval_eq_of_adjoin_eq_top {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] {α : Ω}
    (hα : IsIntegral (RatFunc k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤) (x : Ω) :
    ∃ p : Polynomial (RatFunc k), aeval α p = x := by
  have h : (⊤ : IntermediateField (RatFunc k) Ω).toSubalgebra
      = Algebra.adjoin (RatFunc k) {α} := by
    rw [← hgen]
    exact IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hα.isAlgebraic
  have hx : x ∈ (⊤ : IntermediateField (RatFunc k) Ω).toSubalgebra := by
    rw [IntermediateField.top_toSubalgebra]; trivial
  rw [h, Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx
  exact hx

/-! ### Puiseux embeddings and rotations -/

namespace PuiseuxEmbedding

variable {K : Type} [Field K] [Algebra k K]
  {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [Algebra (Polynomial k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω]
  {s : k} {e : ℕ}

/-- **A Puiseux embedding restricts to the Kummer substitution on the whole rational function
field**, not only on the coordinate ring: both are ring homomorphisms out of a fraction field
agreeing on the coordinate ring. -/
theorem hom_algebraMap_ratFunc (ψ : PuiseuxEmbedding Ω K s e) (x : RatFunc k) :
    ψ.hom (algebraMap (RatFunc k) Ω x) = kummerLift K s ψ.index_pos x := by
  have h : ψ.hom.comp (algebraMap (RatFunc k) Ω) = kummerLift K s ψ.index_pos := by
    refine IsFractionRing.ringHom_ext (A := Polynomial k) fun p => ?_
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ψ.compat, kummerLift_algebraMap]
  exact congrArg (fun f => f x) h

section Galois

variable [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω]

omit [FiniteDimensional (RatFunc k) Ω] in
/-- A deck transformation that the embedding turns into a rotation rescales the power series
attached to every element of the integral model. -/
theorem psHom_smul_of_rescale (ψ : PuiseuxEmbedding Ω K s e) {ζ : K} (hζ0 : ζ ≠ 0)
    {σ : Ω ≃ₐ[RatFunc k] Ω} (h : ∀ x : Ω, ψ.hom (σ x) = laurentRescale hζ0 (ψ.hom x))
    (x : Bring Ω) : ψ.psHom (σ • x) = PowerSeries.rescale ζ (ψ.psHom x) := by
  refine injective_algebraMap ?_
  rw [algebraMap_psHom, coe_smul_geom, h, ← algebraMap_psHom, laurentRescale_algebraMap]

omit [FiniteDimensional (RatFunc k) Ω] in
theorem smul_mem_place_iff (ψ : PuiseuxEmbedding Ω K s e) {ζ : K} (hζ0 : ζ ≠ 0)
    {σ : Ω ≃ₐ[RatFunc k] Ω} (h : ∀ x : Ω, ψ.hom (σ x) = laurentRescale hζ0 (ψ.hom x))
    (x : Bring Ω) : σ • x ∈ ψ.place ↔ x ∈ ψ.place := by
  rw [place, Ideal.mem_comap, Ideal.mem_comap, ψ.psHom_smul_of_rescale hζ0 h,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton, X_dvd_rescale_iff]

omit [FiniteDimensional (RatFunc k) Ω] in
/-- **A deck transformation that the embedding turns into a rotation stabilizes the place the
embedding cuts out.** -/
theorem smul_place (ψ : PuiseuxEmbedding Ω K s e) {ζ : K} (hζ0 : ζ ≠ 0)
    {σ : Ω ≃ₐ[RatFunc k] Ω} (h : ∀ x : Ω, ψ.hom (σ x) = laurentRescale hζ0 (ψ.hom x)) :
    σ • ψ.place = ψ.place := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hx := ψ.smul_mem_place_iff hζ0 h (σ⁻¹ • x)
  rw [smul_inv_smul] at hx
  exact hx.symm

/-- **A deck transformation that the embedding turns into a rotation lies in the inertia group of
the place the embedding cuts out.**

Stabilizing a geometric place is the same as lying in its inertia group, because the residue field
there is algebraically closed. -/
theorem mem_geomInertia_of_rescale (ψ : PuiseuxEmbedding Ω K s e) {ζ : K} (hζ0 : ζ ≠ 0)
    {σ : Ω ≃ₐ[RatFunc k] Ω} (h : ∀ x : Ω, ψ.hom (σ x) = laurentRescale hζ0 (ψ.hom x)) :
    σ ∈ geomInertia Ω ψ.place := by
  haveI := ψ.place_isMaximal
  haveI := ψ.place_liesOver
  rw [geomInertia_eq_stabilizer s ψ.place]
  exact ψ.smul_place hζ0 h


/-! ### Realizing a rotation by a deck transformation -/

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] in
/-- The embedding turns a polynomial expression in an element into the same polynomial expression
in its image, read through the Kummer substitution. -/
theorem hom_aeval (ψ : PuiseuxEmbedding Ω K s e) (y : Ω) (p : Polynomial (RatFunc k)) :
    ψ.hom (aeval y p) = eval₂ (kummerLift K s ψ.index_pos) (ψ.hom y) p := by
  rw [aeval_def, hom_eval₂, show ψ.hom.comp (algebraMap (RatFunc k) Ω)
    = kummerLift K s ψ.index_pos from RingHom.ext ψ.hom_algebraMap_ratFunc]

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] in
/-- **The intertwining identity need only be checked on a primitive element.**  Both sides are
ring homomorphisms which restrict to the Kummer substitution on the rational function field, and
every element of the cover is a polynomial expression in the primitive element. -/
theorem intertwine_of_apply_eq (ψ : PuiseuxEmbedding Ω K s e) {ζ : K} (hζ0 : ζ ≠ 0)
    (hζ : ζ ^ e = 1) {α : Ω} (hα : IsIntegral (RatFunc k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤) {σ : Ω ≃ₐ[RatFunc k] Ω}
    (h : ψ.hom (σ α) = laurentRescale hζ0 (ψ.hom α)) (x : Ω) :
    ψ.hom (σ x) = laurentRescale hζ0 (ψ.hom x) := by
  obtain ⟨p, rfl⟩ := exists_aeval_eq_of_adjoin_eq_top hα hgen x
  have hcomp : (laurentRescale hζ0).comp (kummerLift K s ψ.index_pos)
      = kummerLift K s ψ.index_pos :=
    RingHom.ext (laurentRescale_kummerLift hζ0 hζ s ψ.index_pos)
  have hσ : σ (aeval α p) = aeval (σ α) p := (Polynomial.aeval_algHom_apply σ α p).symm
  rw [hσ, ψ.hom_aeval, h, ψ.hom_aeval, hom_eval₂, hcomp]

/-- **Every rotation of the local coordinate by a root of unity of order dividing the index is
realized by a deck transformation.**

Rotating the local coordinate carries the embedding of a primitive element to another root of its
equation over the Kummer coordinate ring.  The conjugates of the primitive element supply as many
distinct roots of that equation as its degree, so they are all of them, and the rotated embedding
is the embedding of one of them. -/
theorem exists_deck_rescale (ψ : PuiseuxEmbedding Ω K s e) {ζ : K} (hζ0 : ζ ≠ 0) (hζ : ζ ^ e = 1)
    {α : Ω} (hα : IsIntegral (RatFunc k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤) :
    ∃ σ : Ω ≃ₐ[RatFunc k] Ω, ∀ x : Ω, ψ.hom (σ x) = laurentRescale hζ0 (ψ.hom x) := by
  classical
  set q : Polynomial (LaurentSeries K) :=
    (minpoly (RatFunc k) α).map (kummerLift K s ψ.index_pos) with hqdef
  have hmonic : (minpoly (RatFunc k) α).Monic := minpoly.monic hα
  have hqmonic : q.Monic := hmonic.map _
  have hqdeg : q.natDegree = (minpoly (RatFunc k) α).natDegree := hmonic.natDegree_map _
  -- the embeddings of the conjugates of `α` are roots of the equation
  have hconj : ∀ σ : Ω ≃ₐ[RatFunc k] Ω, q.eval (ψ.hom (σ α)) = 0 := by
    intro σ
    rw [hqdef, eval_map, ← ψ.hom_aeval, Polynomial.aeval_algHom_apply σ α _, minpoly.aeval,
      map_zero, map_zero]
  -- and they are pairwise distinct
  have hinj : Function.Injective fun σ : Ω ≃ₐ[RatFunc k] Ω => ψ.hom (σ α) := by
    intro σ τ hστ
    have hα' : σ α = τ α := ψ.hom.injective hστ
    refine AlgEquiv.ext fun x => ?_
    obtain ⟨p, rfl⟩ := exists_aeval_eq_of_adjoin_eq_top hα hgen x
    rw [← Polynomial.aeval_algHom_apply σ α p, ← Polynomial.aeval_algHom_apply τ α p, hα']
  -- the rotated embedding of `α` is a root of the same equation
  have hrot : q.eval (laurentRescale hζ0 (ψ.hom α)) = 0 := by
    have hcomp : (laurentRescale hζ0).comp (kummerLift K s ψ.index_pos)
        = kummerLift K s ψ.index_pos :=
      RingHom.ext (laurentRescale_kummerLift hζ0 hζ s ψ.index_pos)
    have h0 : q.eval (ψ.hom α) = 0 := by
      have := hconj 1
      rwa [show ((1 : Ω ≃ₐ[RatFunc k] Ω) α) = α from rfl] at this
    rw [hqdef, eval_map] at h0 ⊢
    have h1 := congrArg (laurentRescale hζ0) h0
    rwa [hom_eval₂, hcomp, map_zero] at h1
  -- counting: the conjugates exhaust the roots
  set T : Finset (LaurentSeries K) :=
    Finset.image (fun σ : Ω ≃ₐ[RatFunc k] Ω => ψ.hom (σ α)) Finset.univ with hTdef
  have hTcard : T.card = q.natDegree := by
    rw [hTdef, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank (RatFunc k) Ω, hqdeg,
      ← IntermediateField.adjoin.finrank hα, hgen, IntermediateField.finrank_top']
  have hsub : T ⊆ q.roots.toFinset := by
    intro y hy
    rw [hTdef, Finset.mem_image] at hy
    obtain ⟨σ, -, rfl⟩ := hy
    exact Multiset.mem_toFinset.mpr ((mem_roots hqmonic.ne_zero).mpr (hconj σ))
  have hle : q.roots.toFinset.card ≤ T.card := by
    rw [hTcard]
    exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' q)
  have hTeq : T = q.roots.toFinset := Finset.eq_of_subset_of_card_le hsub hle
  have hmem : laurentRescale hζ0 (ψ.hom α) ∈ T := by
    rw [hTeq]
    exact Multiset.mem_toFinset.mpr ((mem_roots hqmonic.ne_zero).mpr hrot)
  rw [hTdef, Finset.mem_image] at hmem
  obtain ⟨σ, -, hσ⟩ := hmem
  exact ⟨σ, ψ.intertwine_of_apply_eq hζ0 hζ hα hgen hσ⟩

end Galois

end PuiseuxEmbedding

/-! ### Rotations as inertia of a cover of the line -/

namespace LineCover

variable {K : Type} [Field K] [Algebra k K] (L : LineCover) {s : k} {e : ℕ}

/-- **A deck transformation of a cover of the line that a Puiseux embedding turns into a rotation
is an inertia element at the point.** -/
theorem isInertiaAt_of_rescale (ψ : PuiseuxEmbedding L.M K s e) {ζ : K} (hζ0 : ζ ≠ 0)
    {σ : L.deck} (h : ∀ x : L.M, ψ.hom (σ x) = laurentRescale hζ0 (ψ.hom x)) :
    L.IsInertiaAt s σ :=
  ⟨ψ.place, ψ.place_isMaximal, ψ.place_liesOver, ψ.mem_geomInertia_of_rescale hζ0 h⟩

/-- **A Puiseux embedding produces an inertia element at the point for every root of unity of
order dividing its index.** -/
theorem exists_isInertiaAt_of_puiseux (ψ : PuiseuxEmbedding L.M K s e) {ζ : K} (hζ0 : ζ ≠ 0)
    (hζ : ζ ^ e = 1) {α : L.M} (hα : IsIntegral (RatFunc k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤) :
    ∃ σ : L.deck, L.IsInertiaAt s σ ∧ ∀ x : L.M, ψ.hom (σ x) = laurentRescale hζ0 (ψ.hom x) := by
  obtain ⟨σ, hσ⟩ := ψ.exists_deck_rescale hζ0 hζ hα hgen
  exact ⟨σ, L.isInertiaAt_of_rescale ψ hζ0 hσ, hσ⟩

end LineCover

end Rigidity.RET

end

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# From trivial inertia to an unramified integral model

Ramification of a cover at a place is visible in two languages.  The Galois-theoretic one records
it as an inertia group: the deck transformations fixing a place of the cover and acting trivially
on its residue field.  The commutative-algebra one records it as a failure of the ring of integral
elements to be unramified over the base ring, that is, as a non-vanishing module of relative
differentials.  This file identifies the two, in the direction needed to differentiate along a
cover: a cover with no non-trivial inertia anywhere over the base has an unramified integral model.

Both languages measure the same integer.  For a Galois extension of Dedekind domains with separable
residue extensions the order of the inertia group at a place is the ramification index there, and a
place of ramification index one is unramified in the sense of differentials.  Over the generic
point there is nothing to check: the extension of fraction fields is separable, and a separable
extension of fields is unramified.  Since every point of the spectrum is either the generic one or
a place, and unramifiedness may be checked point by point, the two conditions agree.

The base is taken to be an algebra over a field of characteristic zero, which makes every residue
extension separable and so discharges the hypothesis of the comparison between inertia and the
ramification index.

## Main results

* `Rigidity.RET.isUnramifiedAt_of_inertia_eq_bot` — a place with trivial inertia is unramified.
* `Rigidity.RET.isUnramifiedAt_bot` — the generic point of an integral model is unramified when the
  fraction field is.
* `Rigidity.RET.formallyUnramified_integralClosure` — a cover with no non-trivial inertia over any
  place has an unramified integral model.
-/

open Polynomial nonZeroDivisors

noncomputable section


namespace Rigidity.RET

/-! ## Trivial inertia at a place means the place is unramified -/

/-- **A place with trivial inertia is unramified.**  The order of the inertia group at a place of a
Galois extension of Dedekind domains is the ramification index there, and ramification index one is
unramifiedness. -/
theorem isUnramifiedAt_of_inertia_eq_bot {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B] [IsGaloisGroup G A B] [Finite G]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.EssFiniteType A B] [Algebra.IsIntegral A B]
    (p : Ideal A) (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver p] (hQ : Q ≠ ⊥)
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ Q)]
    (h : ∀ σ : G, σ ∈ Ideal.inertia G Q → σ = 1) :
    Algebra.IsUnramifiedAt A Q := by
  have hpe : p = Q.under A := Ideal.LiesOver.over
  subst hpe
  have hp : Q.under A ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hQ
  have hbot : Ideal.inertia G Q = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    simpa using h σ hσ
  have hcard : Nat.card (Ideal.inertia G Q) = 1 := Subgroup.card_eq_one.2 hbot
  have he : Ideal.ramificationIdx (algebraMap A B) (Q.under A) Q = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under A) Q G,
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := G) (Q.under A) hp Q, hcard]
  rw [Algebra.isUnramifiedAt_iff_map_eq A (Q.under A) Q]
  exact ⟨inferInstance, (Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff hQ
    Ideal.map_comap_le).1 he⟩

/-- **The generic point of an integral model is unramified when the fraction field is.**  The
localization at the zero ideal is the fraction field. -/
theorem isUnramifiedAt_bot {A B L : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing L]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L] [IsFractionRing B L]
    [Algebra.FormallyUnramified A L] : Algebra.IsUnramifiedAt A (⊥ : Ideal B) := by
  have : IsLocalization B⁰ (Localization.AtPrime (⊥ : Ideal B)) := by
    convert (inferInstanceAs
      (IsLocalization (⊥ : Ideal B).primeCompl (Localization.AtPrime (⊥ : Ideal B))))
    ext; simp [Ideal.primeCompl]
  exact (Algebra.FormallyUnramified.iff_of_equiv (A := L)
    ((IsLocalization.algEquiv B⁰ _ _).restrictScalars A)).mp inferInstance

/-! ## The integral model of an unbranched cover -/

section Model

attribute [local instance] Ideal.Quotient.field

set_option synthInstance.maxHeartbeats 200000 in
/-- **The residue extension at a place is separable** when the base is an algebra over a field of
characteristic zero: the base residue field is then of characteristic zero, hence perfect. -/
theorem residue_isSeparable_of_charZero (k : Type*) {A B : Type*} [Field k] [CharZero k]
    [CommRing A] [Algebra k A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (p : Ideal A) [p.IsMaximal] (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver p] :
    Algebra.IsSeparable (A ⧸ p) (B ⧸ Q) := by
  haveI : Q.IsPrime := ‹Q.IsMaximal›.isPrime
  haveI : CharZero (A ⧸ p) := charZero_of_injective_algebraMap (algebraMap k (A ⧸ p)).injective
  infer_instance

/-- The function field of a cover is unramified over the base: it is separable over the fraction
field of the base, which is a localization of the base. -/
theorem formallyUnramified_of_fractionRing (A K F : Type*) [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field F] [Algebra K F] [Algebra.IsSeparable K F]
    [Algebra.EssFiniteType K F] [Algebra A F] [IsScalarTower A K F] :
    Algebra.FormallyUnramified A F := by
  haveI : Algebra.FormallyUnramified A K :=
    Algebra.FormallyUnramified.of_isLocalization (Rₘ := K) A⁰
  haveI : Algebra.FormallyUnramified K F :=
    (Algebra.FormallyUnramified.iff_isSeparable K F).2 inferInstance
  exact Algebra.FormallyUnramified.comp A K F

/-- **The Galois group of a cover acts on its integral model.** -/
scoped instance instModelMSA (A K F : Type*) [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field F] [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [Algebra.IsAlgebraic K F] : MulSemiringAction (F ≃ₐ[K] F) ↥(integralClosure A F) :=
  IsIntegralClosure.MulSemiringAction A K F ↥(integralClosure A F)

variable {A K F : Type*} [CommRing A] [IsDedekindDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field F] [Algebra K F]
  [FiniteDimensional K F] [IsGalois K F] [Algebra A F] [IsScalarTower A K F]

/-- **A cover with no non-trivial inertia over any place has an unramified integral model.**
Unramifiedness is checked point by point on the model: the generic point is unramified because the
extension of function fields is separable, and every other point of the model is a place, where the
inertia group is trivial by hypothesis. -/
theorem formallyUnramified_integralClosure (k : Type*) [Field k] [CharZero k] [Algebra k A]
    (h : ∀ Q : Ideal ↥(integralClosure A F), Q.IsMaximal →
      ∀ σ : F ≃ₐ[K] F, σ ∈ Ideal.inertia (F ≃ₐ[K] F) Q → σ = 1) :
    Algebra.FormallyUnramified A ↥(integralClosure A F) := by
  haveI : IsFractionRing ↥(integralClosure A F) F :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K F ↥(integralClosure A F)
  haveI : IsDedekindDomain ↥(integralClosure A F) := integralClosure.isDedekindDomain A K F
  haveI : Module.Finite A ↥(integralClosure A F) :=
    IsIntegralClosure.finite A K F ↥(integralClosure A F)
  haveI : IsGaloisGroup (F ≃ₐ[K] F) A ↥(integralClosure A F) :=
    IsGaloisGroup.of_isFractionRing (F ≃ₐ[K] F) A ↥(integralClosure A F) K F
  haveI : FaithfulSMul A ↥(integralClosure A F) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have hAL : Function.Injective (algebraMap A F) := by
      rw [IsScalarTower.algebraMap_eq A K F]
      exact (algebraMap K F).injective.comp (IsFractionRing.injective A K)
    intro x y hxy
    apply hAL
    rw [IsScalarTower.algebraMap_apply A ↥(integralClosure A F) F,
      IsScalarTower.algebraMap_apply A ↥(integralClosure A F) F, hxy]
  rw [← Algebra.unramifiedLocus_eq_univ_iff]
  refine Set.eq_univ_of_forall fun P => ?_
  obtain ⟨Q, hQp⟩ := P
  show Algebra.IsUnramifiedAt A Q
  rcases eq_or_ne Q ⊥ with rfl | hbot
  · haveI := formallyUnramified_of_fractionRing A K F
    exact isUnramifiedAt_bot (L := F)
  · haveI : Q.IsMaximal := hQp.isMaximal hbot
    haveI : (Q.under A).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
    haveI := residue_isSeparable_of_charZero k (A := A) (Q.under A) Q
    exact isUnramifiedAt_of_inertia_eq_bot (Q.under A) Q hbot (h Q inferInstance)

end Model

end Rigidity.RET

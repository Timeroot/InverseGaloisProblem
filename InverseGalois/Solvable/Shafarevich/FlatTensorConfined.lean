/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.NamedRadicandClass
import InverseGalois.CFT.PoitouTate.RadicandPlaces
import InverseGalois.Solvable.Shafarevich.FlatTensorStep
import InverseGalois.Solvable.Shafarevich.FlatTensorVal

/-!
# The invariant tensor read as a choice of places

The tensor the flat step asks the arithmetic for is an invariant element of the units of a level
tensored with a target killed by the exponent, of prescribed order at finitely many named places,
a local power at a prescribed finite set of places, and with its remaining ramification confined to
the named orbits and to places completely decomposed in a bigger level.

The descent through the units answers all of that at once, provided the set of places whose orders
are read is chosen well: the orders are prescribed because the vector of orders is onto, and the
invariance costs one obstruction class, the class of a radicand whose divisor is already invariant
measuring how far it is from being invariant itself.  Enlarging the set of places that are read
enlarges the units the correction may be made in, and the confinement clause leaves the orders at
completely decomposed places free, so the places added may be taken there.

So the whole demand collapses to a single statement about the choice of a finite set of places:
the vector of orders on it is onto, and every invariant divisor of confined units with coefficients
in the target is the divisor of an invariant one.  This file records that statement and the
reduction to it.

## Main definitions

* `InverseGalois.Shafarevich.decomposedPlaces`: the places of a level lying below only primes
  completely decomposed in a bigger level.
* `InverseGalois.Shafarevich.allowedPlaces`: the places the radicand is allowed to have order prime
  to the exponent at.
* `InverseGalois.Shafarevich.HasConfinedRadicandPlaces`: **a finite stable set of places can be
  found, containing the named ones, on which the vector of orders of the confined units is onto and
  over which a confined radicand with invariant divisor may be corrected to an invariant one.**
* `Shafarevich.ConfinedRadicandPlacesEP`: that demand, made of every level.

## Main results

* `InverseGalois.Shafarevich.prod_pow_placeValue_val_eq_of_confinedTensorVal`: prescribing the
  valuation of a presented radicand of confined units prescribes the product of powers the flat
  step asks for.
* `InverseGalois.Shafarevich.hasInvariantUnitTensor_of_confinedRadicandPlaces`: **the choice of
  places buys the invariant tensor.**
* `Shafarevich.invariantUnitTensorEP_of_confinedRadicandPlacesEP`: the same, level by level.

## Tags

Shafarevich's theorem, embedding problem, S-unit, group cohomology, Chebotarev, invariant tensor
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT CategoryTheory IsDedekindDomain MulAction NumberField Rigidity.RET
  TensorProduct groupCohomology

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### The places the ramification is confined to -/

section Places

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **The places of a level lying below only primes completely decomposed in a bigger level.** -/
def decomposedPlaces (K E : IntermediateField k Ω) [NumberField ↥K] :
    Set (HeightOneSpectrum (𝓞 ↥K)) :=
  {v | ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
    stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup}

/-- **The places the radicand is allowed to have order prime to the exponent at**: the named ones,
and those every translate of which lies below only primes completely decomposed in the bigger
level. -/
def allowedPlaces (K E : IntermediateField k Ω) [NumberField ↥K]
    (Xs₀ : Set (HeightOneSpectrum (𝓞 ↥K))) : Set (HeightOneSpectrum (𝓞 ↥K)) :=
  Xs₀ ∪ stableCore k ↥K (decomposedPlaces K E)

theorem mem_allowedPlaces {K E : IntermediateField k Ω} [NumberField ↥K]
    {Xs₀ : Set (HeightOneSpectrum (𝓞 ↥K))} {v : HeightOneSpectrum (𝓞 ↥K)} :
    v ∈ allowedPlaces K E Xs₀ ↔
      v ∈ Xs₀ ∨ v ∈ stableCore k ↥K (decomposedPlaces K E) := Iff.rfl

/-- The places the ramification is allowed at form a stable set. -/
instance isGaloisStablePlaces_allowedPlaces (K E : IntermediateField k Ω) [NumberField ↥K]
    (Xs₀ : Set (HeightOneSpectrum (𝓞 ↥K))) [IsGaloisStablePlaces k ↥K Xs₀] :
    IsGaloisStablePlaces k ↥K (allowedPlaces K E Xs₀) :=
  isGaloisStablePlaces_union Xs₀ (stableCore k ↥K (decomposedPlaces K E))

end Places

/-! ### The demand made of the choice of places -/

section Demand

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **A finite stable set of places can be found, containing the named ones, on which the vector of
orders of the confined units is onto and over which a confined radicand with invariant divisor may
be corrected to an invariant one.**

The units the descent is run in are those which are local powers at a prescribed finite stable set
of places and whose order is divisible by the exponent outside the places the ramification is
allowed at — the named places, and those lying below only primes completely decomposed in a bigger
level.  Two things are asked of the set of places whose orders are read: that every system of
orders on it is realised by such a unit, and that a radicand whose divisor is already invariant
carries no obstruction, so that it may be corrected to an invariant radicand with the same divisor.
The second is what an invariant radicand costs, and it is bought by putting more completely
decomposed places into the set: the correction is made in the units the enlarged set brings in. -/
def HasConfinedRadicandPlaces (ℓ : ℕ) (K : IntermediateField k Ω) [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ (Tz Xs₀ : Set (HeightOneSpectrum (𝓞 ↥K))) [IsGaloisStablePlaces k ↥K Tz]
        [IsGaloisStablePlaces k ↥K Xs₀],
      Tz.Finite → Xs₀.Finite → Disjoint Xs₀ Tz →
      ∀ (C : Type) [CommGroup C] [MulDistribMulAction Gal(↥K/k) C], (∀ c : C, c ^ ℓ = 1) →
        ∃ (Xs : Set (HeightOneSpectrum (𝓞 ↥K))) (_ : Finite ↥Xs) (_ : DecidableEq ↥Xs)
          (_ : IsGaloisStablePlaces k ↥K Xs) (_ : Xs₀ ⊆ Xs)
          (hsurj : Function.Surjective (confinedOrd ℓ Tz (allowedPlaces K E Xs₀) Xs)),
          ∀ (t : Additive ↥(confinedUnits ↥K ℓ Tz (allowedPlaces K E Xs₀)) ⊗[ℤ] Additive C)
            (ht : ∀ σ : Gal(↥K/k),
              tensorVal C (confinedOrd ℓ Tz (allowedPlaces K E Xs₀) Xs) (σ • t)
                = tensorVal C (confinedOrd ℓ Tz (allowedPlaces K E Xs₀) Xs) t),
            tensorInvariantClass C (confinedOrd ℓ Tz (allowedPlaces K E Xs₀) Xs)
              (confinedSUnits ℓ Tz (allowedPlaces K E Xs₀) Xs) hsurj
              (mem_confinedSUnits_iff ℓ Tz (allowedPlaces K E Xs₀) Xs) ht = 0

end Demand

/-! ### The valuation of a presented radicand of confined units -/

section Val

variable {ℓ : ℕ} [NeZero ℓ] {K : Type} [Field K] [NumberField K]
variable (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K))) [Finite ↥Xs] [DecidableEq ↥Xs]
variable (C : Type) [CommGroup C]

/-- **Prescribing the valuation of a presented radicand of confined units prescribes the product of
powers the flat step asks for**, the value of a unit at a place being minus its order there. -/
theorem prod_pow_placeValue_val_eq_of_confinedTensorVal {S : Type*} [Fintype S]
    (hexp : ∀ c : C, c ^ ℓ = 1) (z : S → ↥(confinedUnits K ℓ Tz Y)) (b : S → C) (y : ↥Xs) (V : C)
    (hs : tensorVal C (confinedOrd ℓ Tz Y Xs)
      (∑ q, Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (b q)) y = Additive.ofMul V) :
    ∏ q, b q ^ ((placeValue (y : HeightOneSpectrum (𝓞 K)) ((z q : Kˣ)) : ZMod ℓ)).val = V⁻¹ := by
  rw [tensorVal_sum_tmul C (confinedOrd ℓ Tz Y Xs) z b y] at hs
  have hs' : ∏ q, b q ^ (confinedOrd ℓ Tz Y Xs (Additive.ofMul (z q)) y) = V :=
    Additive.ofMul.injective hs
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hs', ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun q _ => ?_
  have hord : confinedOrd ℓ Tz Y Xs (Additive.ofMul (z q)) y
      = -placeValue (y : HeightOneSpectrum (𝓞 K)) ((z q : Kˣ)) := by
    rw [confinedOrd_apply, placeValue_eq_neg_ord, neg_neg]
    rfl
  rw [hord, ← zpow_eq_pow_val (hexp (b q)), zpow_neg, mul_inv_cancel]

end Val

/-! ### The reduction -/

section Bridge

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **The choice of places buys the invariant tensor.**

The two finite sets a prescription arrives with — the named places and the places a local power is
asked for at — are replaced by their hulls, which are stable and still finite, and the named places
still lie in distinct orbits and still avoid the enlarged set of local conditions, because what was
asked of them was asked of their whole orbits.  The places the ramification is allowed at are the
hull of the named ones together with the completely decomposed ones, so the confinement clause is
exactly the statement that the radicand lies in the group of confined units.

The descent then produces a single invariant radicand of confined units whose order at each named
place is the prescribed value inverted — the value of a unit at a place being minus its order — and
whose order vanishes away from the named orbits.  Presenting it along the named basis of the target
turns it into the family of units the step asks for, its invariance is the invariance of the
descended tensor because the inclusion of the confined units is equivariant, and its four clauses
are read off one by one. -/
theorem hasInvariantUnitTensor_of_confinedRadicandPlaces {ℓ : ℕ} [NeZero ℓ]
    {K : IntermediateField k Ω} [NumberField ↥K] [FiniteDimensional k ↥K]
    (h : HasConfinedRadicandPlaces ℓ K) : HasInvariantUnitTensor ℓ K := by
  classical
  intro E hEfin hEgal hKE M _ _ hexp T _ b hspan hindep ι _ w V hdist hstab Tz hwTz _ _
  -- the stable hulls of the two finite sets of places
  have hTzsfin : (stableHull k ↥K (Tz : Set (HeightOneSpectrum (𝓞 ↥K)))).Finite :=
    stableHull_finite Tz.finite_toSet
  have hXs₀fin : (stableHull k ↥K (Set.range w)).Finite :=
    stableHull_finite (Set.finite_range w)
  have hdisj0 : Disjoint (stableHull k ↥K (Set.range w))
      (stableHull k ↥K (Tz : Set (HeightOneSpectrum (𝓞 ↥K)))) := by
    refine Set.disjoint_left.2 fun v hv1 hv2 => ?_
    obtain ⟨σ, ν, hν⟩ := hv1
    obtain ⟨τ, hτ⟩ := hv2
    refine hwTz ν (τ * σ⁻¹) ?_
    rw [mul_smul, hν, inv_smul_smul]
    exact Finset.mem_coe.1 hτ
  obtain ⟨Xs, hXsfin, hXsdec, hXsstab, hXs₀Xs, hsurj, hδ⟩ :=
    h E hEfin hEgal hKE (stableHull k ↥K (Tz : Set (HeightOneSpectrum (𝓞 ↥K))))
      (stableHull k ↥K (Set.range w)) hTzsfin hXs₀fin hdisj0 M hexp
  have hwmem : ∀ μ : ι, w μ ∈ Xs := fun μ =>
    hXs₀Xs (subset_stableHull k ↥K (Set.range w) ⟨μ, rfl⟩)
  -- the prescribed values, read at the named places of the enlarged set
  have hV' : ∀ μ : ι, ∀ s ∈ stabilizer Gal(↥K/k) (⟨w μ, hwmem μ⟩ : ↥Xs),
      s • (V μ)⁻¹ = (V μ)⁻¹ := by
    intro μ s hs
    have hsw : s • w μ = w μ := congrArg Subtype.val (mem_stabilizer_iff.1 hs)
    rw [smul_inv', hstab μ s hsw]
  have hdisj' : ∀ μ ν : ι, μ ≠ ν →
      (⟨w μ, hwmem μ⟩ : ↥Xs) ∉ orbit Gal(↥K/k) (⟨w ν, hwmem ν⟩ : ↥Xs) := by
    intro μ ν hμν hmem
    obtain ⟨σ, hσ⟩ := hmem
    exact hdist ν μ (Ne.symm hμν) σ (congrArg Subtype.val hσ)
  obtain ⟨s, hsinv, hsval, -⟩ :=
    exists_invariant_confinedTensorVal_eq_of_named_of_class (k := k) ℓ
      (stableHull k ↥K (Tz : Set (HeightOneSpectrum (𝓞 ↥K))))
      (allowedPlaces K E (stableHull k ↥K (Set.range w))) Xs hsurj hδ
      (fun μ => (⟨w μ, hwmem μ⟩ : ↥Xs)) (fun μ => (V μ)⁻¹) hV' hdisj'
  obtain ⟨z₀, hz₀⟩ := exists_forall_sum_tmul_eq b hspan s
  rw [hz₀] at hsval
  refine ⟨fun q => ((z₀ q : (↥K)ˣ)), fun σ => ?_, fun μ => ?_, fun q v hv => ?_,
    fun v hv => ?_⟩
  · -- the invariance survives the inclusion of the confined units
    have hsum : (∑ q, Additive.ofMul ((z₀ q : (↥K)ˣ)) ⊗ₜ[ℤ] Additive.ofMul (b q))
        = tensorSubIncl M
            (confinedUnits ↥K ℓ (stableHull k ↥K (Tz : Set (HeightOneSpectrum (𝓞 ↥K))))
              (allowedPlaces K E (stableHull k ↥K (Set.range w)))) s := by
      rw [hz₀, map_sum]
      exact Finset.sum_congr rfl fun q _ => (tensorSubIncl_tmul M _ (z₀ q) (b q)).symm
    rw [hsum, ← tensorSubIncl_smul, hsinv σ]
  · -- the order at a named place is the prescribed value
    have hval := prod_pow_placeValue_val_eq_of_confinedTensorVal
      (stableHull k ↥K (Tz : Set (HeightOneSpectrum (𝓞 ↥K))))
      (allowedPlaces K E (stableHull k ↥K (Set.range w))) Xs M hexp z₀ b
      (⟨w μ, hwmem μ⟩ : ↥Xs) ((V μ)⁻¹) (hsval μ)
    rwa [inv_inv] at hval
  · -- the radicand is a local power where it was asked to be
    exact MonoidHom.mem_ker.1
      ((z₀ q).2.1 v (subset_stableHull k ↥K (Tz : Set (HeightOneSpectrum (𝓞 ↥K)))
        (Finset.mem_coe.2 hv)))
  · -- and its remaining ramification is confined
    obtain ⟨q, hq⟩ := hv
    have hmem : v ∈ allowedPlaces K E (stableHull k ↥K (Set.range w)) := by
      by_contra hcon
      refine hq ?_
      rw [placeValue_eq_neg_ord]
      exact dvd_neg.2 ((z₀ q).2.2 v hcon)
    rcases mem_allowedPlaces.1 hmem with hmem | hmem
    · obtain ⟨σ, ν, hν⟩ := hmem
      exact Or.inl ⟨ν, σ⁻¹, by rw [hν, inv_smul_smul]⟩
    · exact Or.inr (stableCore_subset k ↥K (decomposedPlaces K E) hmem)

end Bridge

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

/-! ### The demand, made of every level -/

/-- **Every finite Galois level of a number field inside an algebraic closure admits a choice of
places good enough to carry the invariant tensor.**

For every finite stable set of places a local power is asked at, every finite stable set of named
places avoiding it, and every target killed by the exponent, a finite stable set of places
containing the named ones is asked for on which the vector of orders of the confined units is onto
and over which a confined radicand with invariant divisor may be corrected to an invariant one with
the same divisor. -/
def ConfinedRadicandPlacesEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K],
      HasConfinedRadicandPlaces ℓ K

/-- **The choice of places buys the invariant tensor of units, level by level.** -/
theorem invariantUnitTensorEP_of_confinedRadicandPlacesEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : ConfinedRadicandPlacesEP ℓ) : InvariantUnitTensorEP ℓ := by
  intro k Ω _ _ _ _ _ _ K _ _ _ _
  exact hasInvariantUnitTensor_of_confinedRadicandPlaces (h k Ω K)

/-- **The step of the ladder over an odd prime, in exchange for a choice of places and a level
reaching every place** — the arithmetic of the climb resting on the choice of a finite set of
places of a number field. -/
theorem genericLevelStepEPRoots_of_confinedRadicandPlacesEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (hreach : FlatReachableEP ℓ) (h : ConfinedRadicandPlacesEP ℓ) :
    GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_invariantUnitTensorEP ℓ hodd hreach
    (invariantUnitTensorEP_of_confinedRadicandPlacesEP ℓ h)

end Shafarevich

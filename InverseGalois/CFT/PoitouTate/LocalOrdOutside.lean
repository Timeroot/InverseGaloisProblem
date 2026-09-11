/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.LocalOrdPlace
import InverseGalois.CFT.Units.OrdFinsupp
import InverseGalois.CFT.Profinite.KummerAction
import InverseGalois.CFT.Profinite.KummerFinite

/-!
# The dictionary for the vector of orders outside a stable set of places

The dictionary at a place is a statement about an abstract set of places and an abstract vector of
valuations.  Here both are made concrete: the places are the primes of the subextension outside a
finite set carried into itself by the Galois group, and the vector is the vector of orders at
those primes.

The Galois group of the base acts on those primes through its quotient by the subgroup fixing the
subextension, an automorphism acting by its restriction, and the vector of orders is equivariant
for that action.  Each prime outside the set is the place of its own dictionary, so **every prime
outside a stable set has the dictionary**, for any family of subgroups containing the decomposition
subgroups at the primes of the whole extension.

## Main definitions

* `InverseGalois.CFT.outsidePlacesQuotientAction`: **the action of the quotient by the subgroup
  fixing a normal subextension on the primes outside a stable set.**

## Main results

* `InverseGalois.CFT.ordFinsupp_quotient_smul`: **the vector of orders is equivariant** for that
  action.
* `InverseGalois.CFT.hasLocalOrdHom_ordFinsupp`: **every prime outside a stable set has the
  dictionary**, the vector of valuations being the vector of orders.

## Tags

number field, height one prime, order, Galois action, Kummer theory, decomposition group
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET
open groupCohomology TensorProduct

/-! ### The action of the quotient on the primes outside the set -/

section Action

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable (K : IntermediateField k Ω) [NumberField ↥K] [Normal k ↥K]
variable (T : Set (HeightOneSpectrum (𝓞 ↥K))) [IsGaloisStablePlaces k ↥K T]

/-- **The action of the quotient by the subgroup fixing a normal subextension on the primes
outside a stable set**, an automorphism acting by its restriction to the subextension. -/
noncomputable instance outsidePlacesQuotientAction :
    MulAction (Gal(Ω/k) ⧸ K.fixingSubgroup)
      {v : HeightOneSpectrum (𝓞 ↥K) // v ∉ T} :=
  MulAction.compHom _ (quotientFixingSubgroupEquiv K).toMonoidHom

/-- The quotient acts on the primes outside the set through the Galois group of the
subextension. -/
theorem outsidePlacesQuotient_smul (ρ : Gal(Ω/k) ⧸ K.fixingSubgroup)
    (y : {v : HeightOneSpectrum (𝓞 ↥K) // v ∉ T}) :
    ρ • y = quotientFixingSubgroupEquiv K ρ • y := rfl

/-- The class of an automorphism acts on the primes outside the set by its restriction to the
subextension. -/
theorem outsidePlacesQuotient_smul_mk (σ : Gal(Ω/k))
    (y : {v : HeightOneSpectrum (𝓞 ↥K) // v ∉ T}) :
    (QuotientGroup.mk σ : Gal(Ω/k) ⧸ K.fixingSubgroup) • y
      = AlgEquiv.restrictNormalHom (↥K) σ • y := rfl

/-- **The vector of orders at the primes outside a stable set is equivariant** for the action of
the quotient by the subgroup fixing the subextension. -/
theorem ordFinsupp_quotient_smul (ρ : Gal(Ω/k) ⧸ K.fixingSubgroup) (a : (↥K)ˣ)
    (y : {v : HeightOneSpectrum (𝓞 ↥K) // v ∉ T}) :
    ordFinsupp T (Additive.ofMul (ρ • a)) y = ordFinsupp T (Additive.ofMul a) (ρ⁻¹ • y) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective ρ
  have h1 : (QuotientGroup.mk σ : Gal(Ω/k) ⧸ K.fixingSubgroup) • a
      = AlgEquiv.restrictNormalHom (↥K) σ • a := by
    rw [quotientMk_smul K.fixingSubgroup ((↥K)ˣ) σ a, restrictUnits_smul]
  have h2 : Additive.ofMul (AlgEquiv.restrictNormalHom (↥K) σ • a)
      = globalUnitsAut (AlgEquiv.restrictNormalHom (↥K) σ) (Additive.ofMul a) :=
    Additive.toMul.injective (toMul_globalUnitsAut _ _).symm
  have h3 : ((QuotientGroup.mk σ : Gal(Ω/k) ⧸ K.fixingSubgroup)⁻¹ • y)
      = (AlgEquiv.restrictNormalHom (↥K) σ)⁻¹ • y := by
    rw [outsidePlacesQuotient_smul, map_inv, quotientFixingSubgroupEquiv_mk]
  rw [h1, h2, h3, ordFinsupp_globalUnitsAut]

end Action

/-! ### The dictionary at a prime outside the set -/

section Dict

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω} [NumberField ↥K] [Normal k ↥K]
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M] {ι : M →* (↥K)ˣ}
variable {p d : ℕ} [Fact p.Prime] [NeZero p] [IsCyclic M] [MulDistribMulAction Gal(Ω/k) M]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (h : IsKummerData ↥K Ω M ι p)
variable (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivE : ∀ (y : ↥K.fixingSubgroup) (e : E), y • e = e)
variable {J : Type} [Fintype J] [DecidableEq J] (α : E ≃* (J → M)) (hEp : ∀ e : E, e ^ p = 1)
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
variable [ActsTrivially K.fixingSubgroup (M →* E)]
variable (T : Set (HeightOneSpectrum (𝓞 ↥K))) [IsGaloisStablePlaces k ↥K T]
variable [DecidableEq {v : HeightOneSpectrum (𝓞 ↥K) // v ∉ T}]
variable (eM : Additive (M →* E) ≃+ (Fin d → ZMod p))
variable (hroot : ∀ y : Ωˣ, ∃ z : Ωˣ, z ^ p = y)

include eM hroot hfix in
/-- **Every prime outside a stable set has the dictionary**, the vector of valuations being the
vector of orders at the primes outside that set: the prime is its own place, the order there is the
coordinate of the vector at it, and the quotient by the subgroup fixing the subextension fixes the
coordinate exactly when its restriction fixes the prime. -/
theorem hasLocalOrdHom_ordFinsupp {S : Set (Subgroup Gal(Ω/k))}
    (hS : finiteDecompositionSubgroups k Ω ⊆ S)
    (x : {v : HeightOneSpectrum (𝓞 ↥K) // v ∉ T}) :
    HasLocalOrdHom h htriv htrivE α hEp (ordFinsupp T) S x :=
  hasLocalOrdHom_of_ord h htriv htrivE α hEp hfix (ordFinsupp T) eM hroot hS
    (x : HeightOneSpectrum (𝓞 ↥K)) (fun _ => rfl)
    (fun σ => by
      rw [outsidePlacesQuotient_smul_mk, Subtype.ext_iff, coe_smul_outsidePlaces])
    (fun ρ a y => ordFinsupp_quotient_smul K T ρ a y)

end Dict

end InverseGalois.CFT

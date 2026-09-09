/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.LocalOrdKummer
import InverseGalois.CFT.Kummer.SupKummerData
import InverseGalois.CFT.Kummer.SupPowSurjective
import InverseGalois.CFT.Units.DecompositionClosed
import InverseGalois.CFT.Units.InfiniteDecomposition
import InverseGalois.CFT.Units.LocalEmbedding
import InverseGalois.CFT.Profinite.KummerFinite

/-!
# The dictionary at a finite place, from a prime above it

The dictionary at a place asks for a decomposition subgroup of the whole extension whose image
covers the subgroup fixing the place, together with an equivariant homomorphism computing the
valuation there.  Both are supplied by a single prime of the integers of the whole extension lying
above the place.

Its stabiliser is a decomposition subgroup, and it covers the subgroup fixing the place because the
Galois group over the subextension is transitive on the primes above a given one: an automorphism
of the subextension fixing the place lifts, and the lift can be corrected inside the Galois group
over the subextension so as to fix the prime.  The fixed field of the stabiliser, composed with the
subextension, receives the units of the subextension surjectively after tensoring with coefficients
of finite rank over the prime field, and what that inclusion kills already dies in the completion
at the place; the valuation at the place factors through the completion, so it vanishes there too.
Feeding the two into the dictionary built from surjectivity and vanishing gives the dictionary at
the place.

## Main results

* `InverseGalois.CFT.hasLocalOrdHom_of_ord`: **the dictionary at a finite place**, for a family of
  subgroups containing every decomposition subgroup at a prime.

## Tags

number field, decomposition group, Kummer theory, valuation, local-global principle
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET
open groupCohomology TensorProduct

open scoped Pointwise

section Place

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
variable {X : Type} [MulAction (Gal(Ω/k) ⧸ K.fixingSubgroup) X] [DecidableEq X]
variable (g : Additive (↥K)ˣ →+ (X →₀ ℤ))
variable (eM : Additive (M →* E) ≃+ (Fin d → ZMod p))
variable (hroot : ∀ y : Ωˣ, ∃ z : Ωˣ, z ^ p = y)

include eM hroot hfix in
/-- **The dictionary at a finite place.**  A prime of the integers of the whole extension above the
place has a decomposition subgroup covering the subgroup fixing the place, because an automorphism
of the subextension fixing the place lifts to one fixing the prime; the fixed field of that
subgroup, composed with the subextension, receives the units of the subextension surjectively after
tensoring with the coefficients, and what the inclusion kills dies in the completion at the place
and therefore has vanishing valuation there. -/
theorem hasLocalOrdHom_of_ord {S : Set (Subgroup Gal(Ω/k))}
    (hS : finiteDecompositionSubgroups k Ω ⊆ S) {x : X} (v : HeightOneSpectrum (𝓞 ↥K))
    (hordx : ∀ a : (↥K)ˣ, g (Additive.ofMul a) x = ord ↥K v ((a : (↥K)ˣ) : ↥K))
    (hxv : ∀ σ : Gal(Ω/k), (QuotientGroup.mk σ : Gal(Ω/k) ⧸ K.fixingSubgroup) • x = x ↔
      AlgEquiv.restrictNormalHom (↥K) σ • v = v)
    (hgeq : ∀ (σ : Gal(Ω/k) ⧸ K.fixingSubgroup) (a : (↥K)ˣ) (y : X),
      g (Additive.ofMul (σ • a)) y = g (Additive.ofMul a) (σ⁻¹ • y)) :
    HasLocalOrdHom h htriv htrivE α hEp g S x := by
  classical
  haveI : IsGalois k ↥K := ⟨⟩
  haveI := v.isPrime
  obtain ⟨P, -, hPp, hPu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (R := 𝓞 ↥K) (S := 𝓞 Ω) v.asIdeal ⊥ (by simp)
  haveI := hPp
  have hPunder : v.asIdeal = Ideal.under (𝓞 ↥K) P := hPu.symm
  have hPbot : P ≠ ⊥ := by
    intro hb
    refine v.ne_bot ?_
    rw [hPunder, hb, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      RingOfIntegers.ker_algebraMap_eq_bot]
  have hDS : stabilizer Gal(Ω/k) P ∈ S := hS ⟨P, hPp, hPbot, rfl⟩
  obtain ⟨F, hD⟩ : ∃ F : IntermediateField k Ω, F.fixingSubgroup = stabilizer Gal(Ω/k) P :=
    ⟨_, fixingSubgroup_fixedField_of_mem_decompositionSubgroups
      (finiteDecompositionSubgroups_subset ⟨P, hPp, hPbot, rfl⟩)⟩
  letI := trivialMulDistribMulAction Gal(Ω/↥(K ⊔ F)) M
  obtain ⟨ζ, hζ⟩ := h.exists_isPrimitiveRoot
  have hjalg := algebraMap_unitsInclusion (le_sup_left : K ≤ K ⊔ F)
  have htrivEL : ∀ (y : ↥(K ⊔ F).fixingSubgroup) (e : E), y • e = e := fun y e =>
    htrivE ⟨y.1, IntermediateField.fixingSubgroup_le le_sup_left y.2⟩ e
  have hstabv : ∀ σ ∈ stabilizer Gal(Ω/k) P, AlgEquiv.restrictNormalHom (↥K) σ • v = v := by
    intro σ hσ
    refine HeightOneSpectrum.ext ?_
    rw [asIdeal_smul, hPunder, ← under_smul_ringOfIntegers ↥K σ P]
    exact congrArg (Ideal.under (𝓞 ↥K)) hσ
  have hstab : ∀ ρ : Gal(Ω/k) ⧸ K.fixingSubgroup, ρ • x = x →
      ∃ σ ∈ stabilizer Gal(Ω/k) P, (QuotientGroup.mk σ : Gal(Ω/k) ⧸ K.fixingSubgroup) = ρ := by
    intro ρ hρ
    obtain ⟨σ₁, rfl⟩ := QuotientGroup.mk_surjective ρ
    obtain ⟨σ, hσP, hσres⟩ := exists_mem_stabilizer_restrictNormalHom_eq (k := k) (K := Ω) K
      ((hxv σ₁).1 hρ) P hPunder.symm
    refine ⟨σ, hσP, (quotientFixingSubgroupEquiv K).injective ?_⟩
    rw [quotientFixingSubgroupEquiv_mk, quotientFixingSubgroupEquiv_mk, hσres]
  have hker : ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
      TensorProduct.map (MonoidHom.toAdditive (unitsInclusion
        (le_sup_left : K ≤ K ⊔ F))).toIntLinearMap LinearMap.id t = 0 →
        tensorVal (M →* E) g t x = 0 := by
    intro t ht
    refine tensorVal_eq_zero_of_tensorMap_eq_zero (M →* E) g
      (MonoidHom.toAdditive (adicUnitHom v)) (-unitVal) x (fun a => ?_)
      (tensor_adicUnitHom_eq_zero_of_tensor_sup_eq_zero eM _ hjalg hζ hD hPunder ht)
    show -unitVal (Additive.ofMul (adicUnitHom v (Additive.toMul a))) = g a x
    rw [unitVal_adicUnitHom, neg_neg]
    exact (hordx (Additive.toMul a)).symm
  exact hasLocalOrdHom_of_surjective_tensor h (isKummerData_of_le h le_sup_left hroot) htriv
    htrivE htrivEL α hEp hfix g (unitsInclusion le_sup_left) hjalg (fun m => hjalg (ι m)) hDS hD
    hstab (fun σ hσ => (hxv σ).2 (hstabv σ hσ)) hgeq
    (surjective_tensor_sup_of_stabilizer_ideal eM _ hjalg hζ hroot hD hPunder) hker

end Place

end InverseGalois.CFT

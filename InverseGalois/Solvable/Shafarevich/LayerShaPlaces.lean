/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.SUnitFinite
import InverseGalois.Solvable.Shafarevich.LayerLocalOrd

/-!
# Shrinking away the everywhere locally trivial classes of a layer, unconditionally

The two countings which annihilate an everywhere locally trivial class with coefficients in a layer
were carried out against an abstract reading of the units of a finite Galois subextension: a
homomorphism to the free abelian group on some Galois set, onto, with a stable kernel which is
finitely generated, and satisfying the local dictionary at every place.  All four requirements are
met at once by the vector of orders at the primes outside a finite set of primes stable under the
Galois group, chosen large enough to meet every ideal class.

Onto is the choice of the set, the kernel is the group of units for the set and is finitely
generated because Dirichlet's theorem makes the units of the ring of integers finitely generated and
the orders at the chosen primes span a subgroup of a free abelian group of finite rank, stability is
the stability of the set, and the dictionary is the reading of a class at a single prime.  So the
shrinking is available for the data itself, with no arithmetic hypothesis left over beyond the
Kummer data and the roots of unity of the top field.

## Main results

* `InverseGalois.Shafarevich.hasShrinkableSha_of_isKummerData`: **every everywhere locally trivial
  class with coefficients in a layer dies under a shrinking**, for any Kummer datum over a finite
  Galois subextension through which the base realization factors.

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, S-unit, locally trivial class
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain NumberField

section Places

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] [TopologicalSpace U] (n : ℕ)
  (S : Type) [Group S] [Finite S] (j : ℕ)
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [Algebra.IsIntegral k Ω]
variable (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
  [IsAlgClosure ↥K Ω]
variable {M : Type} [CommGroup M] [Finite M] [IsCyclic M] [MulDistribMulAction Gal(Ω/↥K) M]
  [MulDistribMulAction Gal(Ω/k) M] {ι : M →* (↥K)ˣ}
variable (f : Gal(↥K/k) →* U) {φ : Gal(Ω/k) →* U}

/-- **Every everywhere locally trivial class with coefficients in a layer dies under a shrinking.**
The reading of the units of the finite Galois subextension is the vector of orders at the primes
outside a finite set of primes stable under the Galois group and meeting every ideal class: it is
onto by the choice of the set, its kernel is the finitely generated group of units for the set, and
it is a local dictionary because a class is read at one prime at a time. -/
theorem hasShrinkableSha_of_isKummerData (hS : IsPGroup ℓ S)
    (hφ : ∀ x : Gal(Ω/k), φ x = f (AlgEquiv.restrictNormalHom ↥K x))
    (h : IsKummerData ↥K Ω M ι ℓ) (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
    (hM : Nat.card M = ℓ)
    (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
      σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
        = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
    (hroot : ∀ y : Ωˣ, ∃ z : Ωˣ, z ^ ℓ = y) :
    HasShrinkableSha ℓ U n S j φ (decompositionSubgroups k Ω) := by
  classical
  haveI : Finite (Gal(Ω/k) ⧸ K.fixingSubgroup) :=
    Finite.of_equiv _ (quotientFixingSubgroupEquiv K).toEquiv.symm
  obtain ⟨T, hTfin, hTstab, hg⟩ := exists_finite_stable_ordFinsupp_surjective (k := k) (K := ↥K)
  haveI := hTstab
  have hB : ∀ a : (↥K)ˣ, a ∈ sUnits (↥K) T ↔ ordFinsupp T (Additive.ofMul a) = 0 := by
    intro a
    rw [← AddMonoidHom.mem_ker]
    exact (mem_ker_ordFinsupp T).symm
  haveI : IsStableSubgroup (Gal(Ω/k) ⧸ K.fixingSubgroup) (sUnits (↥K) T) := by
    constructor
    intro σ a ha
    refine (hB _).2 (Finsupp.ext fun y => ?_)
    rw [Finsupp.coe_zero, Pi.zero_apply, ordFinsupp_quotient_smul K T σ a y, (hB a).1 ha,
      Finsupp.coe_zero, Pi.zero_apply]
  haveI := module_finite_sUnits T hTfin
  obtain ⟨d, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := Additive ↥(sUnits (↥K) T))
  exact hasShrinkableSha_of_hasLayerLocalOrdHom ℓ U n S j K f (ordFinsupp T) (sUnits (↥K) T)
    hS hφ h htriv hM hfix hg hB (ordFinsupp_quotient_smul K T) b hb
    (hasLayerLocalOrdHom_ordFinsupp ℓ U S j K φ T finiteDecompositionSubgroups_subset
      (fixingSubgroup_le_ker U K f hφ) h htriv hM hfix hroot)

end Places

end InverseGalois.Shafarevich

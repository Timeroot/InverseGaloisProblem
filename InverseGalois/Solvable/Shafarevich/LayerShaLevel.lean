/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.LocalSymbol
import InverseGalois.CFT.Profinite.Symbol
import InverseGalois.Solvable.Shafarevich.LayerShaPlaces

/-!
# The shrinking, with the level and the roots of unity built rather than assumed

The shrinking which annihilates an everywhere locally trivial class with coefficients in a layer was
carried out over a finite Galois subextension through which the base realization factors, and with
an abstract Kummer datum over that subextension.  Both are produced by the base realization itself,
once the base contains a primitive root of unity of the prime order in play.

The realization is smooth and its target is finite and discrete, so the subgroup it kills is open
and normal, and therefore contains the subgroup fixing a finite Galois subextension; the realization
then factors through the Galois group of that subextension, a factorization which needs nothing of
the target beyond being a group.  The subextension is a number field because it is finite over one,
and the ambient field is its algebraic closure because it is an algebraic closure of the base.  The
Kummer datum is the residues modulo the prime, read as the roots of unity of the subextension: they
are the base's own roots of unity, so the Galois group of the ambient field over the base fixes
them, which is what the two triviality clauses of the shrinking ask.

## Main results

* `InverseGalois.Shafarevich.exists_monoidHom_comp_restrictNormalHom`: a homomorphism to any group
  which kills the subgroup fixing a finite Galois level factors through the Galois group of that
  level.
* `InverseGalois.Shafarevich.hasShrinkableSha_of_isPrimitiveRoot`: **every everywhere locally
  trivial class with coefficients in a layer dies under a shrinking**, over any number field
  containing a primitive root of unity of the prime order in play.

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, roots of unity, locally trivial class
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

/-! ### Two ingredients -/

/-- A unit of an extension which comes from the base is fixed by every automorphism over the
base. -/
theorem smul_units_eq_self_of_algebraMap_eq {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (σ : Gal(Ω/k)) {w : Ωˣ} {a : k} (ha : algebraMap k Ω a = (w : Ω)) : σ • w = w := by
  refine Units.ext ?_
  show σ ((w : Ω)) = (w : Ω)
  rw [← ha, AlgEquiv.commutes]

/-- **A homomorphism to any group which kills the subgroup fixing a finite Galois level factors
through the Galois group of that level.**  Restriction to the level is onto, so a right inverse of
it carries the homomorphism down, and the kernel of restriction is exactly the subgroup fixing the
level. -/
theorem exists_monoidHom_comp_restrictNormalHom {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsGalois k K] (L : IntermediateField k K) [Normal k L] {N : Type*} [Group N]
    (u : Gal(K/k) →* N) (hker : L.fixingSubgroup ≤ u.ker) :
    ∃ f : Gal(↥L/k) →* N, ∀ σ : Gal(K/k),
      f (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L σ) = u σ := by
  obtain ⟨g, hg⟩ := (restrictNormalHom_surjective_level L).hasRightInverse
  have hle : (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L).ker ≤ u.ker := by
    rwa [IntermediateField.restrictNormalHom_ker]
  refine ⟨(AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L).liftOfRightInverse g hg ⟨u, hle⟩,
    fun σ => ?_⟩
  exact MonoidHom.liftOfRightInverse_comp_apply
    (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) ↥L) g hg ⟨u, hle⟩ σ

/-! ### The shrinking over a base with the roots of unity -/

section Main

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] [TopologicalSpace U]
  [DiscreteTopology U] (n : ℕ) (S : Type) [Group S] [Finite S] (j : ℕ)
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {φ : Gal(Ω/k) →* U}

/-- **Every everywhere locally trivial class with coefficients in a layer dies under a shrinking**,
over a number field containing a primitive root of unity of the prime order in play.  The finite
Galois subextension is the one whose fixing subgroup the realization kills, and the Kummer datum is
the residues modulo the prime read as the roots of unity of that subextension. -/
theorem hasShrinkableSha_of_isPrimitiveRoot (hS : IsPGroup ℓ S) (hsmφ : IsSmoothHom φ)
    {ζ : k} (hζ : IsPrimitiveRoot ζ ℓ) :
    HasShrinkableSha ℓ U n S j φ (decompositionSubgroups k Ω) := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsIntegral k Ω := Algebra.IsAlgebraic.isIntegral
  -- the finite Galois level the realization factors through
  have hbot : IsOpenNormal (⊥ : Subgroup U) := ⟨inferInstance, isOpen_discrete _⟩
  obtain ⟨N, hN, hNle⟩ := hsmφ ⊥ hbot
  have hNker : N ≤ φ.ker := hNle
  obtain ⟨E, hEfin, hEgal, hEle⟩ := exists_fixingSubgroup_le hN
  haveI := hEfin
  haveI := hEgal
  haveI : NumberField ↥E := NumberField.of_module_finite k ↥E
  haveI : IsAlgClosure ↥E Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := k) _⟩
  have hkerE : E.fixingSubgroup ≤ φ.ker := le_trans hEle hNker
  obtain ⟨f, hf⟩ := exists_monoidHom_comp_restrictNormalHom E φ hkerE
  -- the Kummer datum: the residues modulo the prime, read as the roots of unity of the base
  letI := zmodTrivialAction (↥E) Ω ℓ
  letI := zmodTrivialAction k Ω ℓ
  have hζE : IsPrimitiveRoot (algebraMap k ↥E ζ) ℓ :=
    hζ.map_of_injective (algebraMap k ↥E).injective
  have hdata := isKummerData_zmod (Ω := Ω) hζE (fun a => exists_units_pow_eq a)
  refine hasShrinkableSha_of_isKummerData ℓ U n S j E f hS (fun x => (hf x).symm) hdata
    (fun _ _ => rfl) ?_ ?_ (fun y => exists_units_pow_eq_self y)
  · simp
  · intro σ m
    refine smul_units_eq_self_of_algebraMap_eq σ (a := ζ ^ (Multiplicative.toAdd m).val) ?_
    show algebraMap k Ω (ζ ^ (Multiplicative.toAdd m).val)
      = algebraMap ↥E Ω ((zmodRootHom hζE m : (↥E)ˣ) : ↥E)
    rw [zmodRootHom_apply]
    have hval : ((primitiveRootUnit hζE : (↥E)ˣ) : ↥E) = algebraMap k ↥E ζ := IsUnit.unit_spec _
    rw [Units.val_pow_eq_pow_val, hval, map_pow, map_pow, ← IsScalarTower.algebraMap_apply]

end Main

end InverseGalois.Shafarevich

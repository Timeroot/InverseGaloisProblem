/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LevelRungData
import InverseGalois.Solvable.Shafarevich.RootsLevel

/-!
# The step of the ladder over the rationals, in exchange for the repair alone

Six of the seven clauses of the package the ladder consumes are theorems, and the family they are
proved for is produced from a level of the base realization.  Over the rationals that level is
available for free: the kernel of a smooth realization is open and normal, so the subfield it fixes
is a finite Galois extension whose fixing subgroup is exactly that kernel, and the roots of unity
the restricted step of the ladder puts in the base realization sit inside it.  Feeding those to the
family and the family to the package leaves a single condition, the repair of the property on a
lift, and that is what this file names.

## Main definitions

* `Shafarevich.SolutionRepairEP` — **the repair of the property on a lift, asked of every base
  realization over the rationals**.

## Main results

* `InverseGalois.Shafarevich.exists_level_fixingSubgroup_eq` — an open normal subgroup of the
  Galois group of an infinite Galois extension is the subgroup fixing a finite Galois level.
* `Shafarevich.genericLevelStepEPRoots_of_solutionRepairEP` — **the repair of the property is the
  only thing between the arithmetic and the step of the ladder** for an odd prime.

## Tags

Shafarevich's theorem, embedding problem, Krull topology, level, roots of unity
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT MulAction NumberField

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### A level for an open normal subgroup -/

section Level

/-- **An open normal subgroup of the Galois group of an infinite Galois extension is the subgroup
fixing a finite Galois level.**  An open subgroup of a topological group is closed, so the Galois
correspondence for the Krull topology returns it from the subfield it fixes; that subfield is
finite over the base because the subgroup is open, and Galois over it because the subgroup is
normal. -/
theorem exists_level_fixingSubgroup_eq {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsGalois k K] {N : Subgroup Gal(K/k)} (hN : IsOpenNormal N) :
    ∃ E : IntermediateField k K, FiniteDimensional k ↥E ∧ IsGalois k ↥E ∧
      E.fixingSubgroup = N ∧ ∀ x : K, (∀ σ ∈ N, σ x = x) → x ∈ E := by
  haveI : N.Normal := hN.normal
  have hfix : (IntermediateField.fixedField N).fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, Subgroup.isClosed_of_isOpen N hN.isOpen⟩
  refine ⟨IntermediateField.fixedField N, ?_, ?_, hfix, ?_⟩
  · exact (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfix]; exact hN.isOpen)
  · exact (InfiniteGalois.normal_iff_isGalois _).1 (by rw [hfix]; exact hN.normal)
  · intro x hx
    exact (IntermediateField.mem_fixedField_iff N x).2 hx

/-- A finite subextension of an extension of a number field is a number field. -/
theorem numberField_of_finiteDimensional {k Ω : Type*} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (E : IntermediateField k Ω) [FiniteDimensional k ↥E] : NumberField ↥E :=
  NumberField.of_module_finite k ↥E

end Level

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### The residual condition -/

/-- **The repair of the property on a lift, asked of every base realization over the rationals.**

A solution at one rung of the ladder, and a lift of it across the next layer which is onto, smooth,
compatible with the solution below and trivial on the part of each member of the finite family that
the base realization already kills, is asked to yield a solution at the next rung: everything but
the restriction on ramification is in hand, and what is asked is that the restriction be restored.
The layer must be past the first, the layer there being the Frattini layer, and the property is the
one the family is built for, that the field a solution cuts out ramify only at primes where the
base field splits completely and the local extension is cyclic and totally ramified. -/
def SolutionRepairEP (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U] [TopologicalSpace U]
      [DiscreteTopology U] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (φ : Gal(Ω/ℚ) →* U) (t : ℕ) (D : Fin t → Subgroup Gal(Ω/ℚ)) (n j : ℕ), 1 ≤ j →
    HasSolutionRepair ℓ U n S j φ D (IsSplitTotallyRamified ℓ U S φ)

/-! ### The step -/

/-- **The repair of the property is the only thing between the arithmetic and the step of the
ladder** for an odd prime.

The kernel of the base realization fixes a finite Galois level, the roots of unity of order the
prime lie in that level because the realization is asked to fix those of order its square, and the
level with its root of unity produces the finite family carrying six of the seven clauses of the
package the ladder consumes.  The seventh is supplied. -/
theorem genericLevelStepEPRoots_of_solutionRepairEP (ℓ : ℕ) [Fact ℓ.Prime] (hodd : 2 < ℓ)
    (h : SolutionRepairEP ℓ) : GenericLevelStepEPRoots ℓ (ℓ * ℓ) := by
  refine genericLevelStepEPRoots_of_hasRungData ℓ (ℓ * ℓ) ?_
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ hS hsurj hsm hroots
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨K, hfin, hgal, hKker, hKmem⟩ :=
    exists_level_fixingSubgroup_eq (isOpenNormal_ker_of_isSmoothHom hsm)
  haveI := hfin
  haveI := hgal
  haveI : NumberField ↥K := numberField_of_finiteDimensional K
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_of_isAlgClosure ℚ Ω ℓ
  have hzsq : z ^ (ℓ * ℓ) = 1 := by
    rw [pow_mul, hz.pow_eq_one, one_pow]
  have hzK : z ∈ K := hKmem z fun σ hσ => hroots σ hσ z hzsq
  have hζ : IsPrimitiveRoot (⟨z, hzK⟩ : ↥K) ℓ :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) hz (algebraMap ↥K Ω).injective
  have hmu : ∀ y : Ωˣ, y ^ (ℓ * ℓ) = 1 → ∀ σ ∈ φ.ker, σ • y = y := by
    intro y hy σ hσ
    refine Units.ext ?_
    show σ ((y : Ω)) = (y : Ω)
    refine hroots σ hσ (y : Ω) ?_
    simpa using congrArg Units.val hy
  obtain ⟨t, Pr, -, hdata⟩ :=
    exists_family_rungData hodd hS hsurj hsm K hKker hζ hmu ∅ Set.finite_empty
  exact ⟨t, _, _, _, hdata fun n j hj => h S U Ω φ t _ n j hj⟩

end Shafarevich

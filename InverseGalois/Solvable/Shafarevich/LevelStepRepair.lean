/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.OpenLevel
import InverseGalois.Solvable.Shafarevich.LevelConfinedTwist
import InverseGalois.Solvable.Shafarevich.LevelCyclicRepair
import InverseGalois.Solvable.Shafarevich.LevelKernelPrescription
import InverseGalois.Solvable.Shafarevich.LevelRepair
import InverseGalois.Solvable.Shafarevich.LevelRungData
import InverseGalois.Solvable.Shafarevich.LevelShrink
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

The condition is named five times.  The form the ladder consumes asks for a whole solution back; the
form the arithmetic is actually asked for only asks for a lift, being onto costing nothing past the
first layer; the form the class field theory can answer asks for a lift whose ramification is
described prime by prime; the next drops even total ramification, which is a consequence of
cyclicity over a totally ramified solution below; and the last drops the lift altogether, two lifts
of one solution differing by a one cocycle with values in the layer.  Each implies the one before,
so the last is all the arithmetic owes: **two smooth one cocycles, prescribed along finitely many
subgroups of decomposition subgroups, trivial along the family and ramified only where they are
allowed to be** — a weak one which flattens the lift at arbitrary primes and a sharp one which
makes it cyclic at the completely decomposed primes the first leaves behind.

## Main definitions

* `Shafarevich.SolutionRepairEP` — **the repair of the property on a lift, asked of every base
  realization over the rationals**.
* `Shafarevich.LiftRepairEP` — the same repair, asked to return only a lift.
* `Shafarevich.CyclicRepairEP` — the same repair, with the property read prime by prime.
* `Shafarevich.SplitCyclicRepairEP` — the same repair, with total ramification dropped as well.
* `Shafarevich.FlatPrescriptionEP` — the flattening as a prescription in degree one.
* `Shafarevich.ConfinedPrescriptionEP` — the repair as a prescription in degree one at completely
  decomposed primes.
* `Shafarevich.KernelPrescriptionEP` — the sharp prescription, made one field up as a homomorphism.

## Main results

* `Shafarevich.solutionRepairEP_of_liftRepairEP` — **repairing a lift repairs a solution**.
* `Shafarevich.liftRepairEP_of_cyclicRepairEP` — **confining the new ramification and making it
  cyclic repairs a lift**.
* `Shafarevich.cyclicRepairEP_of_splitCyclicRepairEP` — **confining the new ramification and making
  it cyclic is all the arithmetic owes**.
* `Shafarevich.splitCyclicRepairEP_of_confinedPrescriptionEP` — **and that is bought with two
  prescriptions in degree one**, the finite family covering the primes above the prime.
* `Shafarevich.genericLevelStepEPRoots_of_solutionRepairEP` — **the repair of the property is the
  only thing between the arithmetic and the step of the ladder** for an odd prime.
* `Shafarevich.genericLevelStepEPRoots_of_liftRepairEP` — the same step, in exchange for the repair
  of a lift alone.
* `Shafarevich.genericLevelStepEPRoots_of_cyclicRepairEP` — the same step, in exchange for the
  repair read prime by prime.
* `Shafarevich.genericLevelStepEPRoots_of_splitCyclicRepairEP` — the same step, in exchange for
  confining the new ramification and making it cyclic.
* `Shafarevich.genericLevelStepEPRoots_of_confinedPrescriptionEP` — the same step, in exchange for
  the prescriptions in degree one alone.
* `Shafarevich.confinedPrescriptionEP_of_kernelPrescriptionEP` — **the sharp prescription may be
  made one field up**, where the action on the layer is trivial and a cocycle is a homomorphism.
* `Shafarevich.genericLevelStepEPRoots_of_kernelPrescriptionEP` — the same step, with the sharp
  prescription made one field up.

## Tags

Shafarevich's theorem, embedding problem, Krull topology, level, roots of unity
-/

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich NumberField

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
base field splits completely and the local extension is cyclic and totally ramified.  The base
realization is asked to fix the roots of unity of order the square of the prime times the exponent
of the test group, which is what the restricted step of the ladder puts into it, and the family is
asked to be the family of decomposition subgroups of a family of primes covering the primes above
the prime, which is what the family produced from a level is. -/
def SolutionRepairEP (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U] [TopologicalSpace U]
      [DiscreteTopology U] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (φ : Gal(Ω/ℚ) →* U) (t : ℕ) (D : Fin t → Subgroup Gal(Ω/ℚ)) (n j : ℕ), IsPGroup ℓ S → 1 ≤ j →
      (∀ ζ : Ωˣ, ζ ^ (ℓ * ℓ * Monoid.exponent S) = 1 → ∀ σ ∈ φ.ker, σ • ζ = ζ) →
      (∃ Pr : Fin t → Ideal (𝓞 Ω), IsCoveringPrimeFamily ℓ Pr D) →
    HasSolutionRepair ℓ U n S j φ D (IsSplitTotallyRamified ℓ U S φ)

/-- **The repair of the property, asked to return only a lift.**

The data is the same as for `Shafarevich.SolutionRepairEP` and what is asked back is less: a lift
over the same solution below, again smooth and again trivial along the family, which carries the
restriction.  Nothing is asked about it being onto. -/
def LiftRepairEP (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U] [TopologicalSpace U]
      [DiscreteTopology U] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (φ : Gal(Ω/ℚ) →* U) (t : ℕ) (D : Fin t → Subgroup Gal(Ω/ℚ)) (n j : ℕ), IsPGroup ℓ S → 1 ≤ j →
      (∀ ζ : Ωˣ, ζ ^ (ℓ * ℓ * Monoid.exponent S) = 1 → ∀ σ ∈ φ.ker, σ • ζ = ζ) →
      (∃ Pr : Fin t → Ideal (𝓞 Ω), IsCoveringPrimeFamily ℓ Pr D) →
    HasLiftRepair ℓ U n S j φ D

/-- **The repair of the property, with the property read prime by prime.**

The data is the same again, and what is asked back is a lift whose ramification is described one
prime at a time: it carries the restriction where the solution below already ramifies over the base
realization, it does not ramify where the solution below neither ramifies nor splits completely,
and its local image is cyclic where the solution below splits completely. -/
def CyclicRepairEP (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U] [TopologicalSpace U]
      [DiscreteTopology U] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (φ : Gal(Ω/ℚ) →* U) (t : ℕ) (D : Fin t → Subgroup Gal(Ω/ℚ)) (n j : ℕ), IsPGroup ℓ S → 1 ≤ j →
      (∀ ζ : Ωˣ, ζ ^ (ℓ * ℓ * Monoid.exponent S) = 1 → ∀ σ ∈ φ.ker, σ • ζ = ζ) →
      (∃ Pr : Fin t → Ideal (𝓞 Ω), IsCoveringPrimeFamily ℓ Pr D) →
    HasCyclicRepair ℓ U n S j φ D

/-- **The repair of the property, with total ramification dropped as well.**

The data is the same once more, and what is asked back is the least of all: a lift whose new
ramification over the base realization occurs only at primes where the solution below splits
completely, and whose local image is cyclic there.  Being totally ramified is not asked for, being
a consequence of cyclicity over a totally ramified solution below. -/
def SplitCyclicRepairEP (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U] [TopologicalSpace U]
      [DiscreteTopology U] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (φ : Gal(Ω/ℚ) →* U) (t : ℕ) (D : Fin t → Subgroup Gal(Ω/ℚ)) (n j : ℕ), IsPGroup ℓ S → 1 ≤ j →
      (∀ ζ : Ωˣ, ζ ^ (ℓ * ℓ * Monoid.exponent S) = 1 → ∀ σ ∈ φ.ker, σ • ζ = ζ) →
      (∃ Pr : Fin t → Ideal (𝓞 Ω), IsCoveringPrimeFamily ℓ Pr D) →
    HasSplitCyclicRepair ℓ U n S j φ D

/-- **Repairing a lift repairs a solution.**  Past the first layer the layer lies in the Frattini
subgroup of the normal factor, so a lift over a solution which is onto is itself onto; and a lift
over a solution below is over the base realization, the projection of the layer extension leaving
the operator coordinate alone. -/
theorem solutionRepairEP_of_liftRepairEP (ℓ : ℕ) [Fact ℓ.Prime] (h : LiftRepairEP ℓ) :
    SolutionRepairEP ℓ := by
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ t D n j hS hj hmu hcov
  exact hasSolutionRepair_of_hasLiftRepair ℓ U n S hS hj (h S U Ω φ t D n j hS hj hmu hcov)

/-- **Confining the new ramification and making it cyclic repairs a lift.**  At a prime where the
solution below splits completely the values of a lift on the decomposition subgroup come from the
generic operator group and are killed by the exponent of the test group, and the base realization
fixes the roots of unity of order the prime times that exponent, so cyclicity is the whole of what
the restriction asks there. -/
theorem liftRepairEP_of_cyclicRepairEP (ℓ : ℕ) [Fact ℓ.Prime] (h : CyclicRepairEP ℓ) :
    LiftRepairEP ℓ := by
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ t D n j hS hj hmu hcov
  refine hasLiftRepair_of_hasCyclicRepair (fun ζ hζ => hmu ζ ?_)
    (h S U Ω φ t D n j hS hj hmu hcov)
  rw [mul_right_comm, pow_mul, hζ, one_pow]

/-- **Confining the new ramification and making it cyclic is all the arithmetic owes.**  Total
ramification at the primes where the new ramification occurs follows from cyclicity there, the
solution below being totally ramified wherever it ramifies at all and trivial on the decomposition
subgroup at the remaining primes. -/
theorem cyclicRepairEP_of_splitCyclicRepairEP (ℓ : ℕ) [Fact ℓ.Prime] (h : SplitCyclicRepairEP ℓ) :
    CyclicRepairEP ℓ := by
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ t D n j hS hj hmu hcov
  exact hasCyclicRepair_of_hasSplitCyclicRepair hS (h S U Ω φ t D n j hS hj hmu hcov)

/-- **The flattening as a prescription in degree one.**

The data is the same once more, and what is asked back is no lift at all but a smooth one cocycle
with values in the layer: prescribed along finitely many subgroups of decomposition subgroups at
primes named in advance, trivial along the finite family wherever the base realization already is,
and ramifying only at those named primes or else at primes where the given lift kills the whole
decomposition subgroup.  Nothing is asked of the local image, and the named primes are arbitrary.
The prescription announces the number of letters its data is read at and answers at the number
asked for. -/
def FlatPrescriptionEP (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U] [TopologicalSpace U]
      [DiscreteTopology U] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (φ : Gal(Ω/ℚ) →* U) (t : ℕ) (D : Fin t → Subgroup Gal(Ω/ℚ)) (n j : ℕ), IsPGroup ℓ S → 1 ≤ j →
      (∀ ζ : Ωˣ, ζ ^ (ℓ * ℓ * Monoid.exponent S) = 1 → ∀ σ ∈ φ.ker, σ • ζ = ζ) →
    letI := galLayerAction ℓ U n S j φ
    HasFlatPrescription ℓ U n S j φ D

/-- **The repair as a prescription in degree one at completely decomposed primes.**

The data is the same once more, and what is asked back is no lift at all but a smooth one cocycle
with values in the layer: prescribed along finitely many subgroups of decomposition subgroups at
primes named in advance and completely decomposed in the field the base realization cuts out,
trivial along the finite family wherever the base realization already is, and ramifying only at
those named primes or else at primes where the given lift kills the whole decomposition subgroup and
the cocycle is cyclic.  The prescription announces the number of letters its data is read at and
answers at the number asked for, and the finite family is named by the primes it is the family of
decomposition subgroups of. -/
def ConfinedPrescriptionEP (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U] [TopologicalSpace U]
      [DiscreteTopology U] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (φ : Gal(Ω/ℚ) →* U) (t : ℕ) (D : Fin t → Subgroup Gal(Ω/ℚ)) (n j : ℕ), IsPGroup ℓ S → 1 ≤ j →
      (∀ ζ : Ωˣ, ζ ^ (ℓ * ℓ * Monoid.exponent S) = 1 → ∀ σ ∈ φ.ker, σ • ζ = ζ) →
      (∃ Pr : Fin t → Ideal (𝓞 Ω), IsCoveringPrimeFamily ℓ Pr D) →
    letI := galLayerAction ℓ U n S j φ
    HasConfinedPrescription ℓ U n S j φ D

/-- **The sharp prescription, made one field up.**

The data is the same once more, and what is asked back is not a cocycle over the rationals but a
smooth homomorphism into the layer defined on the kernel of the base realization, the action there
being trivial: prescribed along the same subgroups, killing the conjugates of the finite family and
the decomposition subgroups of all but one prime of each orbit it is allowed to ramify in, and
cyclic on the decomposition subgroup of each prime it brings in itself.  The prescription announces
the number of letters its data is read at and answers at the number asked for, and the finite family
is named by the primes it is the family of decomposition subgroups of. -/
def KernelPrescriptionEP (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (S U : Type) [Group S] [Finite S] [Group U] [Finite U] [TopologicalSpace U]
      [DiscreteTopology U] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (φ : Gal(Ω/ℚ) →* U) (t : ℕ) (D : Fin t → Subgroup Gal(Ω/ℚ)) (n j : ℕ), IsPGroup ℓ S → 1 ≤ j →
      (∀ ζ : Ωˣ, ζ ^ (ℓ * ℓ * Monoid.exponent S) = 1 → ∀ σ ∈ φ.ker, σ • ζ = ζ) →
      (∃ Pr : Fin t → Ideal (𝓞 Ω), IsCoveringPrimeFamily ℓ Pr D) →
    letI := galLayerAction ℓ U n S j φ
    HasKernelPrescription ℓ U n S j φ D

/-- **The sharp prescription may be made one field up.**  The base realization acts trivially on the
layer through its own kernel, so over the field that kernel cuts out a cocycle is a homomorphism;
averaging a prescribed homomorphism over the cosets of the kernel carries the whole prescription
back down, the primes it names being completely decomposed there. -/
theorem confinedPrescriptionEP_of_kernelPrescriptionEP (ℓ : ℕ) [Fact ℓ.Prime]
    (h : KernelPrescriptionEP ℓ) : ConfinedPrescriptionEP ℓ := by
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ t D n j hS hj hmu hcov
  letI := galLayerAction ℓ U n S j φ
  exact hasConfinedPrescription_of_hasKernelPrescription (fun _ _ => rfl)
    (h S U Ω φ t D n j hS hj hmu hcov)

/-- **The repair is bought with two prescriptions in degree one**, the finite family covering the
primes above the prime.

Two lifts of one solution across one layer differ by a one cocycle with values in the layer.  The
first prescription flattens the given lift, so that every prime at which it then ramifies over the
base realization is completely decomposed in the field the base realization cuts out unless the
solution below ramifies there too; the second makes the corrected lift cyclic at each of the
finitely many orbits of primes where the flattened lift ramifies, such a prime being away from the
prime itself and its local image therefore generated by two elements. -/
theorem splitCyclicRepairEP_of_confinedPrescriptionEP (ℓ : ℕ) [Fact ℓ.Prime]
    (hflat : FlatPrescriptionEP ℓ) (h : ConfinedPrescriptionEP ℓ) : SplitCyclicRepairEP ℓ := by
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ t D n j hS hj hmu hcov
  letI := galLayerAction ℓ U n S j φ
  obtain ⟨Pr, hPr⟩ := hcov
  exact hasSplitCyclicRepair_of_hasConfinedPrescription hS (fun _ _ => rfl)
    (coversAbove_of_isCoveringPrimeFamily hPr)
    (fun m => hflat S U Ω φ t D m j hS hj hmu) (h S U Ω φ t D n j hS hj hmu ⟨Pr, hPr⟩)

/-! ### The step -/

/-- **The repair of the property is the only thing between the arithmetic and the step of the
ladder** for an odd prime.

The kernel of the base realization fixes a finite Galois level, the roots of unity of order the
prime lie in that level because the realization is asked to fix those of order its square, and the
level with its root of unity produces the finite family carrying six of the seven clauses of the
package the ladder consumes.  The seventh is supplied. -/
theorem genericLevelStepEPRoots_of_solutionRepairEP (ℓ : ℕ) [Fact ℓ.Prime] (hodd : 2 < ℓ)
    (h : SolutionRepairEP ℓ) : GenericLevelStepEPRoots ℓ := by
  refine genericLevelStepEPRoots_of_hasRungData ℓ ?_
  intro S U _ _ _ _ _ _ Ω _ _ _ _ φ hS hsurj hsm hroots
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨K, hfin, hgal, hKker, hKmem⟩ :=
    exists_level_fixingSubgroup_eq (isOpenNormal_ker_of_isSmoothHom hsm)
  haveI := hfin
  haveI := hgal
  haveI : NumberField ↥K := numberField_of_finiteDimensional K
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_of_isAlgClosure ℚ Ω ℓ
  have hzsq : z ^ (ℓ * ℓ * Monoid.exponent S) = 1 := by
    rw [pow_mul, pow_mul, hz.pow_eq_one, one_pow, one_pow]
  have hzK : z ∈ K := hKmem z fun σ hσ => hroots σ hσ z hzsq
  have hζ : IsPrimitiveRoot (⟨z, hzK⟩ : ↥K) ℓ :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) hz (algebraMap ↥K Ω).injective
  have hmuE : ∀ y : Ωˣ, y ^ (ℓ * ℓ * Monoid.exponent S) = 1 → ∀ σ ∈ φ.ker, σ • y = y := by
    intro y hy σ hσ
    refine Units.ext ?_
    show σ ((y : Ω)) = (y : Ω)
    refine hroots σ hσ (y : Ω) ?_
    simpa using congrArg Units.val hy
  have hmu : ∀ y : Ωˣ, y ^ (ℓ * ℓ) = 1 → ∀ σ ∈ φ.ker, σ • y = y := by
    refine fun y hy => hmuE y ?_
    rw [pow_mul, hy, one_pow]
  obtain ⟨t, Pr, -, hPrp, hPrbot, hcov, hdata⟩ :=
    exists_family_rungData hodd hS hsurj hsm K hKker hζ hmu ∅ Set.finite_empty
  exact ⟨t, _, _, _, hdata fun n j hj =>
    h S U Ω φ t _ n j hS hj hmuE ⟨Pr, hPrp, hPrbot, fun _ => rfl, hcov⟩⟩

/-- **The step of the ladder, in exchange for the repair of a lift alone.** -/
theorem genericLevelStepEPRoots_of_liftRepairEP (ℓ : ℕ) [Fact ℓ.Prime] (hodd : 2 < ℓ)
    (h : LiftRepairEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_solutionRepairEP ℓ hodd (solutionRepairEP_of_liftRepairEP ℓ h)

/-- **The step of the ladder, in exchange for the repair read prime by prime.** -/
theorem genericLevelStepEPRoots_of_cyclicRepairEP (ℓ : ℕ) [Fact ℓ.Prime] (hodd : 2 < ℓ)
    (h : CyclicRepairEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_liftRepairEP ℓ hodd (liftRepairEP_of_cyclicRepairEP ℓ h)

/-- **The step of the ladder, in exchange for confining the new ramification and making it cyclic**
— the least the arithmetic can be asked for. -/
theorem genericLevelStepEPRoots_of_splitCyclicRepairEP (ℓ : ℕ) [Fact ℓ.Prime] (hodd : 2 < ℓ)
    (h : SplitCyclicRepairEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_cyclicRepairEP ℓ hodd (cyclicRepairEP_of_splitCyclicRepairEP ℓ h)

/-- **The step of the ladder, in exchange for the prescriptions in degree one alone** — the last
thing between the arithmetic and every finite solvable group. -/
theorem genericLevelStepEPRoots_of_confinedPrescriptionEP (ℓ : ℕ) [Fact ℓ.Prime] (hodd : 2 < ℓ)
    (hflat : FlatPrescriptionEP ℓ) (h : ConfinedPrescriptionEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_splitCyclicRepairEP ℓ hodd
    (splitCyclicRepairEP_of_confinedPrescriptionEP ℓ hflat h)

/-- **The step of the ladder, with the sharp prescription made one field up** — where the action on
the layer is trivial and a cocycle is a homomorphism. -/
theorem genericLevelStepEPRoots_of_kernelPrescriptionEP (ℓ : ℕ) [Fact ℓ.Prime] (hodd : 2 < ℓ)
    (hflat : FlatPrescriptionEP ℓ) (h : KernelPrescriptionEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_confinedPrescriptionEP ℓ hodd hflat
    (confinedPrescriptionEP_of_kernelPrescriptionEP ℓ h)

end Shafarevich

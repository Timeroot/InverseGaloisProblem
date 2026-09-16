/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.DecompositionField
import InverseGalois.Solvable.Shafarevich.FlatStep

/-!
# The radicand of a flat prescription, taken from the field its place decomposes in

The flat prescription at a named prime is assembled out of a single unit of the level, and every
clause of the demand made on that unit is a clause at one place at a time — its order at the place
below the named prime, its class at the places it is asked to be a local power at, the places where
its order is not divisible by the exponent — except one.  The exceptional clause is the
equivariance clause: the automorphisms of the level which fix the place are asked to fix the unit
modulo exponent-th powers, which is what carries the prescribed value of the layer to its own power
when the argument of the prescription is conjugated.

That clause is a statement about the whole class of the unit modulo exponent-th powers and not
about any one place, and it is the clause the arithmetic has to be arranged for.  It is met on the
nose by a unit of the subfield of the level which the place decomposes in: the automorphisms fixing
the place are exactly the ones fixing that subfield pointwise, so a unit of the subfield is fixed
by them outright and the exponent-th power the clause allows may be taken to be one.

Asking for such a unit at one named place at a time costs nothing.  The only way the demands made
at the several named places interact is through the clause asking the unit belonging to one place
to have an order divisible by the exponent at every conjugate of the others, and that clause is a
clause at a finite set of places, so it is handed over as a second prescribed set.  The named
places lie in distinct orbits, so that set avoids the place the unit belongs to, which is what
keeps the demand at that place from colliding with the ones made at the conjugates.

## Main definitions

* `InverseGalois.Shafarevich.HasDecomposedPrescribedUnits` — **a unit of the subfield a place
  decomposes in can be found at every reachable place, of order there prime to the exponent, a
  local power at a prescribed finite set of places and at the proper conjugates of its own place,
  of order divisible by the exponent at a second prescribed finite set, and confined elsewhere to
  the conjugates of its place or to places completely decomposed in a given finite level.**
* `Shafarevich.DecomposedUnitsEP` — the same demand, asked of every finite Galois level of the
  rationals.

## Main results

* `InverseGalois.Shafarevich.hasFlatPrescribedUnits_of_hasDecomposedPrescribedUnits` — **units of
  the decomposition fields carry the flat prescription's units.**
* `Shafarevich.genericLevelStepEPRoots_of_decomposedUnitsEP` — the step of the ladder, in exchange
  for those units.

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, decomposition field, local class
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

/-! ### The unit at one place -/

section Units

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

/-- **A unit of the subfield a place decomposes in can be found at every reachable place**, of
order there prime to the exponent, a local power at a prescribed finite set of places that place
avoids and at every proper conjugate of that place, of order divisible by the exponent at a second
prescribed finite set that place avoids, and confined elsewhere to the conjugates of that place or
to places completely decomposed in a given finite level.

The demand is made at one place at a time, and the unit is asked to lie in the subfield of the
level which that place decomposes in rather than merely to be fixed modulo exponent-th powers by
the automorphisms fixing the place.  That is the shape the arithmetic takes: the decomposition
field embeds into the completion of the base field at the prime below, so what is asked of the
unit at the place it belongs to and at its conjugates is asked of a single element of the base
completion, and the automorphisms of the level have nothing left to say about it.

Reachability of the place in the given finite level is the divisor class half of the demand, the
same half the prescription over the whole family names, and it is passed through unchanged; the
set of places the unit is asked to be a local power at is the set the reachability is read
against, the second set being asked only for an order. -/
def HasDecomposedPrescribedUnits (ℓ : ℕ) [NeZero ℓ] (K : IntermediateField k Ω) [NumberField ↥K]
    [IsGalois k ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ (w : HeightOneSpectrum (𝓞 ↥K)) (Tz Xex : Finset (HeightOneSpectrum (𝓞 ↥K))), w ∉ Tz →
      w ∉ Xex → (ℓ : 𝓞 ↥K) ∉ w.asIdeal → IsReachablePlace ℓ K E (↑Tz) w →
        ∃ Z : (↥K)ˣ, (Z : ↥K) ∈ decompositionField k w ∧
          ¬ (ℓ : ℤ) ∣ placeValue w Z ∧
          (∀ v : HeightOneSpectrum (𝓞 ↥K), v ∈ Tz → localClassHom v ℓ Z = 1) ∧
          (∀ v : HeightOneSpectrum (𝓞 ↥K), v ∈ Xex → (ℓ : ℤ) ∣ placeValue v Z) ∧
          (∀ σ : Gal(↥K/k), σ • w ≠ w → localClassHom (σ • w) ℓ Z = 1) ∧
          ∀ v : HeightOneSpectrum (𝓞 ↥K), ¬ (ℓ : ℤ) ∣ placeValue v Z →
            (∃ σ : Gal(↥K/k), v = σ • w) ∨
              ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
                stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup

variable {ℓ : ℕ} [NeZero ℓ] {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K]
  {w : HeightOneSpectrum (𝓞 ↥K)}

omit [NumberField k] [NumberField ↥K] [IsGalois k ↥K] in
/-- A unit of the subfield a place decomposes in is fixed by every automorphism fixing that
place. -/
theorem smul_eq_of_mem_decompositionField {Z : (↥K)ˣ} (hZ : (Z : ↥K) ∈ decompositionField k w)
    {σ : Gal(↥K/k)} (hσ : σ • w = w) : σ • Z = Z :=
  Units.ext (eq_of_mem_decompositionField k w hZ ⟨σ, mem_stabilizer_iff.2 hσ⟩)

omit [NumberField k] in
/-- **Units of the decomposition fields carry the units the flat prescription is assembled out
of.**

The equivariance clause is met with the exponent-th power taken to be one, a unit of the subfield
a place decomposes in being fixed outright by the automorphisms fixing that place.  The clause
asking the unit belonging to one named place to have an order divisible by the exponent at every
conjugate of the other named places is met by handing those conjugates over as the second
prescribed set; that set is finite because the level is, and it avoids the place the unit belongs
to because the named places lie in distinct orbits.  The remaining clauses are clauses at the one
place and are passed through, the confinement clause naming the place the unit belongs to among
the named ones. -/
theorem hasFlatPrescribedUnits_of_hasDecomposedPrescribedUnits [FiniteDimensional k ↥K]
    (h : HasDecomposedPrescribedUnits ℓ K) : HasFlatPrescribedUnits ℓ K := by
  classical
  intro E hEfin hEgal hKE ι _ w hconj Tz hwTz hℓw hreach
  set Xex : ι → Finset (HeightOneSpectrum (𝓞 ↥K)) := fun μ =>
    Finset.image (fun p : Gal(↥K/k) × ι => p.1 • w p.2)
      (Finset.univ ×ˢ (Finset.univ.erase μ)) with hXex
  have hmemXex : ∀ (μ ν : ι), ν ≠ μ → ∀ σ : Gal(↥K/k), σ • w ν ∈ Xex μ := by
    intro μ ν hνμ σ
    refine Finset.mem_image.2 ⟨(σ, ν), ?_, rfl⟩
    exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_erase.2 ⟨hνμ, Finset.mem_univ _⟩⟩
  have hstep : ∀ μ : ι, ∃ Z : (↥K)ˣ, (Z : ↥K) ∈ decompositionField k (w μ) ∧
      ¬ (ℓ : ℤ) ∣ placeValue (w μ) Z ∧
      (∀ v : HeightOneSpectrum (𝓞 ↥K), v ∈ Tz → localClassHom v ℓ Z = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 ↥K), v ∈ Xex μ → (ℓ : ℤ) ∣ placeValue v Z) ∧
      (∀ σ : Gal(↥K/k), σ • w μ ≠ w μ → localClassHom (σ • w μ) ℓ Z = 1) ∧
      ∀ v : HeightOneSpectrum (𝓞 ↥K), ¬ (ℓ : ℤ) ∣ placeValue v Z →
        (∃ σ : Gal(↥K/k), v = σ • w μ) ∨
          ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
            stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup := by
    intro μ
    refine h E hEfin hEgal hKE (w μ) Tz (Xex μ) (hwTz μ) ?_ (hℓw μ) (hreach μ)
    rw [hXex]
    intro hcon
    obtain ⟨⟨σ, ν⟩, hmem, hσν⟩ := Finset.mem_image.1 hcon
    exact hconj ν μ (Finset.mem_erase.1 (Finset.mem_product.1 hmem).2).1 σ hσν
  choose Z hZdec hZord hZT hZX hZconj hZconf using hstep
  refine ⟨Z, fun μ σ hσ => ⟨1, ?_⟩, hZord, hZT,
    fun μ σ hσ => dvd_placeValue_of_localClassHom_eq_one (hZconj μ σ hσ),
    fun μ ν hνμ σ => hZX μ _ (hmemXex μ ν hνμ σ),
    fun μ v hv => ?_⟩
  · rw [smul_eq_of_mem_decompositionField (hZdec μ) hσ, one_pow, mul_one]
  · exact (hZconf μ v hv).imp (fun hcon => ⟨μ, hcon⟩) id

end Units

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

-- Pin `Algebra ℚ ↥K` to the tower instance rather than `DivisionRing.toRatAlgebra`.
attribute [local instance 2000] IntermediateField.algebra'

/-! ### The arithmetic, asked of every level -/

/-- **Every finite Galois level of the rationals carries units of the decomposition fields of its
places.**

The demand is the one the flat prescription is assembled out of, read one place at a time and with
the unit asked to come from the subfield the place decomposes in: a place of the level and two
finite sets of places avoiding it are named, and a unit of the decomposition field is asked for, of
order at the place prime to the exponent, a local power at the first named set and at the proper
conjugates of the place, of order divisible by the exponent at the second, and confined elsewhere
to the conjugates of the place or to places completely decomposed in a finite level given in
advance. -/
def DecomposedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (K : IntermediateField ℚ Ω) [FiniteDimensional ℚ ↥K] [NumberField ↥K] [IsGalois ℚ ↥K],
    HasDecomposedPrescribedUnits ℓ K

/-- **Units of the decomposition fields buy the units the flat prescription needs.** -/
theorem flatUnitsEP_of_decomposedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : DecomposedUnitsEP ℓ) : FlatUnitsEP ℓ := by
  intro Ω _ _ _ _ K _ _ _
  exact hasFlatPrescribedUnits_of_hasDecomposedPrescribedUnits (h Ω K)

/-- **The step of the ladder, in exchange for units of the decomposition fields** — the arithmetic
half of the climb, read at one place at a time and with the equivariance the prescription asks for
replaced by membership in the subfield the place decomposes in. -/
theorem genericLevelStepEPRoots_of_decomposedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hunits : DecomposedUnitsEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_flatUnitsEP ℓ (flatUnitsEP_of_decomposedUnitsEP ℓ hunits)

end Shafarevich

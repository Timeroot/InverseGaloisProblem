/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ModPowEquivariant
import InverseGalois.Solvable.Shafarevich.FlatDiagonalUnits

/-!
# The obstruction, bought with one unit per place with a decomposition group

The demand made of a choice of places has two halves: a diagonal of units at the chosen places,
which the arithmetic input of the prescription already supplies, and the vanishing of the
obstruction to correcting an invariant divisor of confined units to an invariant radicand.  This
file buys the second half against arithmetic of the same shape as the first.

What it costs is one confined unit for each place of the hull of the named ones: a unit of order
one at that place and none at the other places of the hull, each read up to a multiple of the
exponent, and whose class modulo exponent-th powers the automorphisms fixing the place fix.  The
vector of orders is equivariant, so such a unit carries with it the unit belonging to every place of
the same orbit, up to exponent-th powers, and the family so assembled splits the vector of orders
equivariantly after tensoring with a module the exponent kills, which trivialises the obstruction of
every tensor with invariant valuation.

Only the class modulo exponent-th powers is asked to be fixed, because that is all the obstruction
reads: the splitting is spent against a module killed by the exponent, where an exponent-th power
contributes nothing.  The room this leaves over a unit fixed on the nose is exactly the room a
decomposition group leaves by Hilbert's theorem 90, and it is what makes the demand meetable.

The cost is nil at a place no automorphism of order the exponent fixes.  There the decomposition
group has order prime to the exponent, and the product over it of a unit of order one at the place
and none at the others — which the vector of orders being onto already supplies — is fixed by the
automorphisms fixing the place and has order the size of that group there, which a power brings
back to one modulo the exponent.  So what is bought here is a unit at each place of the hull whose
decomposition group has order divisible by the exponent, and nothing at all at the other places.

## Main definitions

* `InverseGalois.Shafarevich.HasStabilizerConfinedUnits`: the units the obstruction is bought
  with, asked for only at the places some automorphism of order the exponent fixes, and asked to be
  fixed there only modulo exponent-th powers.
* `Shafarevich.StabilizerConfinedUnitsEP`: the same, made of every level.

## Main results

* `InverseGalois.Shafarevich.hasConfinedObstruction_of_hasStabilizerConfinedUnits`: **the units buy
  the obstruction.**
* `Shafarevich.genericLevelStepEPRoots_of_stabilizerConfinedUnitsEP`: the step of the ladder over
  an odd prime, in exchange for the units of the obstruction alone.

## Tags

Shafarevich's theorem, embedding problem, S-unit, confined unit, decomposition group, obstruction
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain MulAction NumberField

set_option synthInstance.maxHeartbeats 800000

/-! ### The units the obstruction is bought with -/

section Units

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **The units the obstruction is bought with.**

At each place of the hull of the named ones which some automorphism of order the exponent fixes, a
confined unit of order one at that place and none at the other places of the hull, each up to a
multiple of the exponent, whose class modulo exponent-th powers the automorphisms fixing the place
fix.  Nothing is asked at the places whose decomposition group has order prime to the exponent.

The place is asked to lie outside the set at which the radicand is kept inert, which it does
whenever the orders of the confined units are onto: a unit which is a local power at a place has
order divisible by the exponent there, so no confined unit has order one at a place of that set.  It
also arrives with its order taken by an element the whole group of automorphisms fixes, which is the
statement that its ramification index over the base field is prime to the exponent, and which is
what leaves room for a unit fixed at the place at all.

What has to be bought is the invariance and nothing else.  The orders of the confined units are
handed over as onto, so a confined unit with exactly the vector of orders asked for is already
there; what it need not be is fixed modulo exponent-th powers by the automorphisms fixing the place.
The named places are handed over already reached by a unit as well. -/
def HasStabilizerConfinedUnits (ℓ : ℕ) (K : IntermediateField k Ω) [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ Xs₀ Tz : Set (HeightOneSpectrum (𝓞 ↥K)), Xs₀.Finite → Tz.Finite →
      (∀ v ∈ Xs₀, IsReachablePlace ℓ K E (stableHull k ↥K Tz) v) →
      ∀ _ : Finite ↥(stableHull k ↥K Xs₀),
        Function.Surjective (confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)
          (stableHull k ↥K Xs₀)) →
        ∀ y : ↥(stableHull k ↥K Xs₀),
          (y : HeightOneSpectrum (𝓞 ↥K)) ∉ stableHull k ↥K Tz →
          IsBaseOrderPlace ℓ K (y : HeightOneSpectrum (𝓞 ↥K)) →
          (∃ σ : Gal(↥K/k), σ ≠ 1 ∧ σ ^ ℓ = 1 ∧ σ • y = y) →
          ∃ u : ↥(confinedUnits ↥K ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)),
            (∀ z : ↥(stableHull k ↥K Xs₀), (ℓ : ℤ) ∣
              confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) (stableHull k ↥K Xs₀)
                (Additive.ofMul u) z - Finsupp.single y 1 z) ∧
              ∀ σ : Gal(↥K/k), σ • y = y →
                ∃ v : ↥(confinedUnits ↥K ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)),
                  σ • u = u * v ^ ℓ

/-- **The units buy the obstruction.**

The vector of orders of a confined unit is equivariant, so the units asked for assemble into a
splitting of it carried by the action up to exponent-th powers, and such a splitting trivialises the
obstruction of every tensor whose valuation is invariant.  The splitting is read after tensoring
with a module killed by the exponent, which is why the orders are only asked for up to a multiple of
it and the class modulo exponent-th powers is all that has to be fixed.  Where no automorphism of
order the exponent fixes the place, the product over the decomposition group supplies the unit
unasked. -/
theorem hasConfinedObstruction_of_hasStabilizerConfinedUnits {ℓ : ℕ} [Fact ℓ.Prime]
    {K : IntermediateField k Ω} [NumberField ↥K] [FiniteDimensional k ↥K] [IsGalois k ↥K]
    (h : HasStabilizerConfinedUnits ℓ K) :
    HasConfinedObstruction ℓ K := by
  intro E hEfin hEgal hKE Xs₀ Tz hXs₀ hTz hbase hreach C _ _ hexp hfin hdec hsurj t ht
  haveI : Finite ↥(stableHull k ↥K Xs₀) := hfin
  letI : DecidableEq ↥(stableHull k ↥K Xs₀) := hdec
  have hnotTz : ∀ y : ↥(stableHull k ↥K Xs₀),
      (y : HeightOneSpectrum (𝓞 ↥K)) ∉ stableHull k ↥K Tz := by
    intro y hy
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    obtain ⟨u, hu⟩ := hsurj (Finsupp.single y 1)
    have hone : confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀)
        (stableHull k ↥K Xs₀) u y = 1 := by
      rw [hu, Finsupp.single_eq_same]
    have hdvd : (ℓ : ℤ) ∣ (1 : ℤ) := by
      rw [← hone, confinedOrd_apply]
      exact dvd_ord_of_localClassHom_eq_one (u.toMul.2.1 (y : HeightOneSpectrum (𝓞 ↥K)) hy)
    have h2 : ((ℓ : ℤ) : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
    have h3 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
    omega
  have hybase : ∀ y : ↥(stableHull k ↥K Xs₀),
      IsBaseOrderPlace ℓ K (y : HeightOneSpectrum (𝓞 ↥K)) := by
    intro y
    obtain ⟨σ, hσ⟩ := (mem_stableHull k ↥K Xs₀).1 y.2
    have h1 := (hbase _ hσ).smul σ⁻¹
    rwa [inv_smul_smul] at h1
  exact tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_pow_order ℓ
    (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) (stableHull k ↥K Xs₀) hexp hsurj
    (fun y => h E hEfin hEgal hKE Xs₀ Tz hXs₀ hTz hreach hfin hsurj y (hnotTz y) (hybase y)) ht

end Units

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

-- Pin `Algebra ℚ ↥K` to the tower instance rather than `DivisionRing.toRatAlgebra`.
attribute [local instance 2000] IntermediateField.algebra'

/-! ### The units, made of every level -/

/-- **Every finite Galois level of the rationals inside an algebraic closure carrying a primitive
root of unity of the exponent carries the units the obstruction is bought with.** -/
def StabilizerConfinedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (K : IntermediateField ℚ Ω) [FiniteDimensional ℚ ↥K] [NumberField ↥K] [IsGalois ℚ ↥K],
      (∃ ζ : ↥K, IsPrimitiveRoot ζ ℓ) → HasStabilizerConfinedUnits ℓ K

/-- **The units buy the obstruction, at every level.** -/
theorem confinedObstructionEP_of_stabilizerConfinedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : StabilizerConfinedUnitsEP ℓ) : ConfinedObstructionEP ℓ := by
  intro Ω _ _ _ _ K _ _ _ hζ
  exact hasConfinedObstruction_of_hasStabilizerConfinedUnits (h Ω K hζ)

/-- **The step of the ladder over an odd prime**, in exchange for the units the obstruction is
bought with and nothing else. -/
theorem genericLevelStepEPRoots_of_stabilizerConfinedUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (hstab : StabilizerConfinedUnitsEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_confinedObstructionEP ℓ hodd
    (confinedObstructionEP_of_stabilizerConfinedUnitsEP ℓ hstab)

end Shafarevich

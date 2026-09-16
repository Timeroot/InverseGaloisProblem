/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedDiagonal
import InverseGalois.CFT.PoitouTate.ConfinedTGens
import InverseGalois.CFT.PoitouTate.ConfinedWeightedSurj
import InverseGalois.Solvable.Shafarevich.FlatTensorConfined

/-!
# The choice of places, with the orders read off a diagonal

The demand the flat step makes of a choice of places asks that every system of orders at the chosen
places be realised by a confined unit.  That is a statement about the units of a number field, and
it is worth recording it in the form the arithmetic delivers.

For a prime exponent a single unit at each chosen place is enough — one whose order there is prime
to the exponent and whose order at the other chosen places is divisible by it — because modulo the
exponent those units form a diagonal matrix with invertible entries.  And the divisibility at the
other places is not something the arithmetic has to arrange separately: the units a prescription
produces are asked to be local powers at prescribed places, and a local power is unramified, so its
order there is automatically divisible by the exponent.

So the demand may be stated entirely in terms of local conditions, with one global demand left over:
the order of each unit at its own place is prime to the exponent, which is exactly what a place
reachable in the bigger level provides.  This file states the demand in that form and hands it back
to the one already in use.

What the flat step consumes besides is a second reading of the confined units, cutting them down to
a family spanned by boundedly many generators.  Nothing there has to be asked of the arithmetic: the
correction room a second reading needs is one prime of each refined class, which the refined class
group being finite bounds, and the coefficients the reading leaves are units for the correction room
alone, so their number of generators is bounded by that of the units of the ring of integers plus
the size of the room.  Both bounds belong to the field, so the count is settled before any place is
named, and the choice of places is all that is left to ask for.

## Main definitions

* `InverseGalois.Shafarevich.HasConfinedDiagonalPlaces`: **a finite stable set of places can be
  found, containing the named ones, carrying one unit per place described by local conditions.**
* `Shafarevich.ConfinedDiagonalPlacesEP`: that demand, made of every level.

## Main results

* `InverseGalois.Shafarevich.hasConfinedRadicandPlaces_of_diagonal`: **the diagonal of units is
  enough**, so the demand in the local form implies the one the flat step consumes, the count of
  generators being supplied by the correction room.
* `Shafarevich.genericLevelStepEPRoots_of_confinedDiagonalPlacesEP`: the step of the ladder, in
  exchange for the demand in the local form.

## Tags

Shafarevich's theorem, embedding problem, S-unit, confined unit, diagonal, local condition
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT CategoryTheory IsDedekindDomain MulAction NumberField Rigidity.RET
  TensorProduct groupCohomology

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### The demand, with the orders read off a diagonal -/

section Demand

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **A finite stable set of places can be found, containing the named ones, carrying one unit per
place described by local conditions.**

The unit attached to a place of the set is asked to be a local power at every place where the
radicand must stay inert, to have order divisible by the exponent outside the places the
ramification is allowed at and at every other place of the set, and to have order at its own place
prime to the exponent.  The first two conditions are the confinement; the third is the order at the
other places of the set, which a local power there would in particular give; the fourth is the one
demand that is not local, and it is what a reachable place provides.

Modulo a prime exponent such a family is a diagonal matrix with invertible entries, so the vector of
orders of the confined units is onto. -/
def HasConfinedDiagonalPlaces (ℓ : ℕ) [Fact ℓ.Prime] (K : IntermediateField k Ω)
    [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ Xs₀ Tz : Set (HeightOneSpectrum (𝓞 ↥K)), Xs₀.Finite → Tz.Finite →
      (∀ v ∈ Xs₀, (ℓ : 𝓞 ↥K) ∉ v.asIdeal) →
      (∀ v ∈ Xs₀, IsReachablePlace ℓ K E (stableHull k ↥K Tz) v) →
      (∀ v ∈ Xs₀, IsBaseOrderPlace ℓ K v) →
      (∀ v ∈ Xs₀, ∀ σ : Gal(↥K/k), σ • v ∉ Tz) →
      ∃ (Xs : Set (HeightOneSpectrum (𝓞 ↥K))) (_ : Finite ↥Xs) (_ : DecidableEq ↥Xs)
        (_ : IsGaloisStablePlaces k ↥K Xs) (_ : Xs₀ ⊆ Xs),
        ∀ y : ↥Xs, ∃ u : (↥K)ˣ,
          (∀ v ∈ stableHull k ↥K Tz, localClassHom v ℓ u = 1) ∧
          (∀ v ∉ allowedPlaces K E Xs₀, (ℓ : ℤ) ∣ ord ↥K v ((u : (↥K)ˣ) : ↥K)) ∧
          (∀ z : ↥Xs, z ≠ y →
            (ℓ : ℤ) ∣ ord ↥K (z : HeightOneSpectrum (𝓞 ↥K)) ((u : (↥K)ˣ) : ↥K)) ∧
          ¬ (ℓ : ℤ) ∣ ord ↥K (y : HeightOneSpectrum (𝓞 ↥K)) ((u : (↥K)ˣ) : ↥K)

/-- **The diagonal of units is enough.**  The four conditions make the family a diagonal matrix of
orders modulo the exponent with invertible entries, so the vector of orders of the confined units is
onto.

The second reading, which the flat step needs to be onto as well, costs nothing extra: a correction
room of one prime per refined class makes it onto, and the coefficients it leaves are units for that
room, so they are spanned by the generators of the units of the ring of integers together with one
generator per place of the room.  Both numbers are decided by the field, the exponent and the places
the radicand must stay inert at, so the bound is available before the bigger level and the named
places are. -/
theorem hasConfinedRadicandPlaces_of_diagonal {ℓ : ℕ} [Fact ℓ.Prime]
    {K : IntermediateField k Ω} [NumberField ↥K] [FiniteDimensional k ↥K]
    (h : HasConfinedDiagonalPlaces ℓ K) : HasConfinedRadicandPlaces ℓ K := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  intro Tz hTzfin hTzstab
  haveI := hTzstab
  haveI : Finite ↥Tz := hTzfin.to_subtype
  have hhull : stableHull k ↥K Tz = Tz := stableHull_eq_self
  obtain ⟨d₁, a, ha⟩ := Module.Finite.exists_fin (R := ℤ) (M := Additive (𝓞 ↥K)ˣ)
  refine ⟨Nat.card Gal(↥K/k) *
    (d₁ + (Nat.card ↥Tz + Nat.card Gal(↥K/k) * (2 * Nat.card (localIdealClass ↥K ℓ Tz)))), ?_⟩
  intro E hEfin hEgal hKE Xs₀ hXs₀fin hℓXs hreach hbase hdisj
  obtain ⟨Xs, hXsfin, hXsdec, hXsstab, hXs₀sub, hdiag⟩ :=
    h E hEfin hEgal hKE Xs₀ Tz hXs₀fin hTzfin hℓXs
      (fun v hv => by rw [hhull]; exact hreach v hv) hbase hdisj
  haveI := hXsfin
  haveI := hXsdec
  haveI := hXsstab
  rw [hhull] at hdiag
  obtain ⟨Aux, hAuxfin, hAuxstab, hAuxcard, hsurjT⟩ :=
    exists_surjective_confinedSWeightedOrd (k := k) ℓ Tz (allowedPlaces K E Xs₀) Xs
  haveI := hAuxstab
  haveI : IsGaloisStablePlaces k ↥K (Tz ∪ Aux) := isGaloisStablePlaces_union _ _
  have hcard : Nat.card ↥(Tz ∪ Aux)
      ≤ Nat.card ↥Tz + Nat.card Gal(↥K/k) * (2 * Nat.card (localIdealClass ↥K ℓ Tz)) := by
    refine le_trans ?_ (Nat.add_le_add_left hAuxcard _)
    exact Set.ncard_union_le Tz Aux
  obtain ⟨bb, hbb⟩ :=
    exists_fin_span_confinedTUnits ℓ Tz (allowedPlaces K E Xs₀) Xs (Xs ∪ (Tz ∪ Aux)) (Tz ∪ Aux)
      (hTzfin.union hAuxfin) Set.Subset.rfl a ha hcard
  exact ⟨Xs, hXsfin, hXsdec, hXsstab, hXs₀sub,
    surjective_confinedOrd_of_exists_units ℓ Tz (allowedPlaces K E Xs₀) Xs Fact.out hdiag,
    Xs ∪ (Tz ∪ Aux), isGaloisStablePlaces_union _ _, hsurjT, _, bb, hbb, le_rfl⟩

end Demand

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

-- Pin `Algebra ℚ ↥K` to the tower instance rather than `DivisionRing.toRatAlgebra`.
attribute [local instance 2000] IntermediateField.algebra'

/-! ### The demand in the local form, made of every level -/

/-- **Every finite Galois level of the rationals inside an algebraic closure admits a choice of
places carrying a diagonal of units described by local conditions.**

The same demand as before, with the surjectivity of the vector of orders replaced by the family of
units which produces it: one unit per chosen place, a local power where the radicand must stay
inert and at the other chosen places, of order divisible by the exponent outside the places the
ramification is allowed at, and of order at its own place prime to the exponent.

The level is asked to carry a primitive root of unity of the exponent, which is what the level the
climb reads the demand at carries anyway. -/
def ConfinedDiagonalPlacesEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] [IsGalois ℚ Ω]
      (K : IntermediateField ℚ Ω) [FiniteDimensional ℚ ↥K] [NumberField ↥K] [IsGalois ℚ ↥K],
      (∃ ζ : ↥K, IsPrimitiveRoot ζ ℓ) → HasConfinedDiagonalPlaces ℓ K

/-- **The demand in the local form implies the one the flat step consumes.** -/
theorem confinedRadicandPlacesEP_of_confinedDiagonalPlacesEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : ConfinedDiagonalPlacesEP ℓ) : ConfinedRadicandPlacesEP ℓ := by
  intro Ω _ _ _ _ K _ _ _ hζ
  exact hasConfinedRadicandPlaces_of_diagonal (h Ω K hζ)

/-- **The step of the ladder, in exchange for a diagonal of units** — the arithmetic of the climb
resting on the existence of finitely many units of a number field subject to local conditions. -/
theorem genericLevelStepEPRoots_of_confinedDiagonalPlacesEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : ConfinedDiagonalPlacesEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_confinedRadicandPlacesEP ℓ
    (confinedRadicandPlacesEP_of_confinedDiagonalPlacesEP ℓ h)

end Shafarevich

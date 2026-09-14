/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedDiagonal
import InverseGalois.Solvable.Shafarevich.FlatTensorConfined

/-!
# The choice of places, with the orders read off a diagonal

The demand the flat step makes of a choice of places has two clauses: that every system of orders at
the chosen places is realised by a confined unit, and that a confined radicand whose divisor is
already invariant may be corrected to an invariant radicand with the same divisor.  The second is
the genuine obstruction; the first is a statement about the units of a number field, and it is worth
recording it in the form the arithmetic delivers.

For a prime exponent a single unit at each chosen place is enough — one whose order there is prime
to the exponent and whose order at the other chosen places is divisible by it — because modulo the
exponent those units form a diagonal matrix with invertible entries.  And the divisibility at the
other places is not something the arithmetic has to arrange separately: the units a prescription
produces are asked to be local powers at prescribed places, and a local power is unramified, so its
order there is automatically divisible by the exponent.

So the first clause may be stated entirely in terms of local conditions, with one global demand left
over: the order of each unit at its own place is prime to the exponent, which is exactly what a
place reachable in the bigger level provides.  This file states the demand in that form and hands it
back to the one already in use.

## Main definitions

* `InverseGalois.Shafarevich.HasConfinedDiagonalPlaces`: **a finite stable set of places can be
  found, containing the named ones, carrying one unit per place described by local conditions, and
  over which a confined radicand with invariant divisor may be corrected to an invariant one.**
* `Shafarevich.ConfinedDiagonalPlacesEP`: that demand, made of every level.

## Main results

* `InverseGalois.Shafarevich.hasConfinedRadicandPlaces_of_diagonal`: **the diagonal of units is
  enough**, so the demand in the local form implies the one the flat step consumes.
* `Shafarevich.genericLevelStepEPRoots_of_confinedDiagonalPlacesEP`: the step of the ladder over an
  odd prime, in exchange for the demand in the local form.

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
place described by local conditions, and over which a confined radicand with invariant divisor may
be corrected to an invariant one.**

The unit attached to a place of the set is asked to be a local power at every place where the
radicand must stay inert, to have order divisible by the exponent outside the places the
ramification is allowed at and at every other place of the set, and to have order at its own place
prime to the exponent.  The first two conditions are the confinement; the third is the order at the
other places of the set, which a local power there would in particular give; the fourth is the one
demand that is not local, and it is what a reachable place provides.

Modulo a prime exponent such a family is a diagonal matrix with invertible entries, so the vector of
orders of the confined units is onto, and the second clause is then stated exactly as before. -/
def HasConfinedDiagonalPlaces (ℓ : ℕ) [Fact ℓ.Prime] (K : IntermediateField k Ω)
    [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ Xs₀ Tz : Set (HeightOneSpectrum (𝓞 ↥K)), Xs₀.Finite → Tz.Finite →
      (∀ v ∈ Xs₀, (ℓ : 𝓞 ↥K) ∉ v.asIdeal) → (∀ v ∈ Xs₀, IsReachablePlace ℓ K E v) →
      (∀ v ∈ Xs₀, ∀ σ : Gal(↥K/k), σ • v ∉ Tz) →
      ∀ (C : Type) [CommGroup C] [MulDistribMulAction Gal(↥K/k) C], (∀ c : C, c ^ ℓ = 1) →
        ∃ (Xs : Set (HeightOneSpectrum (𝓞 ↥K))) (_ : Finite ↥Xs) (_ : DecidableEq ↥Xs)
          (_ : IsGaloisStablePlaces k ↥K Xs) (_ : Xs₀ ⊆ Xs)
          (hdiag : ∀ y : ↥Xs, ∃ u : (↥K)ˣ,
            (∀ v ∈ stableHull k ↥K Tz, localClassHom v ℓ u = 1) ∧
            (∀ v ∉ allowedPlaces K E Xs₀, (ℓ : ℤ) ∣ ord ↥K v ((u : (↥K)ˣ) : ↥K)) ∧
            (∀ z : ↥Xs, z ≠ y →
              (ℓ : ℤ) ∣ ord ↥K (z : HeightOneSpectrum (𝓞 ↥K)) ((u : (↥K)ˣ) : ↥K)) ∧
            ¬ (ℓ : ℤ) ∣ ord ↥K (y : HeightOneSpectrum (𝓞 ↥K)) ((u : (↥K)ˣ) : ↥K)),
          ∀ (t : Additive ↥(confinedUnits ↥K ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀))
              ⊗[ℤ] Additive C)
            (ht : ∀ σ : Gal(↥K/k),
              tensorVal C (confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) Xs) (σ • t)
                = tensorVal C (confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) Xs) t),
            tensorInvariantClass C
              (confinedOrd ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) Xs)
              (confinedSUnits ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) Xs)
              (surjective_confinedOrd_of_exists_units ℓ (stableHull k ↥K Tz)
                (allowedPlaces K E Xs₀) Xs Fact.out hdiag)
              (mem_confinedSUnits_iff ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) Xs) ht = 0

/-- **The diagonal of units is enough.**  The four conditions make the family a diagonal
matrix of orders modulo the exponent with invertible entries, so the vector of orders of the
confined units is onto, and the obstruction clause is carried over unchanged. -/
theorem hasConfinedRadicandPlaces_of_diagonal {ℓ : ℕ} [Fact ℓ.Prime]
    {K : IntermediateField k Ω} [NumberField ↥K] (h : HasConfinedDiagonalPlaces ℓ K) :
    HasConfinedRadicandPlaces ℓ K := by
  intro E hEfin hEgal hKE Xs₀ Tz hXs₀ hTz hℓXs hreach hdisj C _ _ hexp
  obtain ⟨Xs, hfin, hdec, hstab, hsub, hdiag, hcls⟩ :=
    h E hEfin hEgal hKE Xs₀ Tz hXs₀ hTz hℓXs hreach hdisj C hexp
  haveI := hfin
  haveI := hdec
  haveI := hstab
  exact ⟨Xs, hfin, hdec, hstab, hsub,
    surjective_confinedOrd_of_exists_units ℓ (stableHull k ↥K Tz) (allowedPlaces K E Xs₀) Xs
      Fact.out hdiag, hcls⟩

end Demand

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

/-! ### The demand in the local form, made of every level -/

/-- **Every finite Galois level of a number field inside an algebraic closure admits a choice of
places carrying a diagonal of units described by local conditions.**

The same demand as before, with the surjectivity of the vector of orders replaced by the family of
units which produces it: one unit per chosen place, a local power where the radicand must stay
inert and at the other chosen places, of order divisible by the exponent outside the places the
ramification is allowed at, and of order at its own place prime to the exponent.

The level is asked to carry a primitive root of unity of the exponent, which is what the level the
climb reads the demand at carries anyway. -/
def ConfinedDiagonalPlacesEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K],
      (∃ ζ : ↥K, IsPrimitiveRoot ζ ℓ) → HasConfinedDiagonalPlaces ℓ K

/-- **The demand in the local form implies the one the flat step consumes.** -/
theorem confinedRadicandPlacesEP_of_confinedDiagonalPlacesEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (h : ConfinedDiagonalPlacesEP ℓ) : ConfinedRadicandPlacesEP ℓ := by
  intro k Ω _ _ _ _ _ _ K _ _ _ hζ
  exact hasConfinedRadicandPlaces_of_diagonal (h k Ω K hζ)

/-- **The step of the ladder over an odd prime, in exchange for a diagonal of units** — the
arithmetic of the climb resting on the existence of finitely many units of a number field subject to
local conditions. -/
theorem genericLevelStepEPRoots_of_confinedDiagonalPlacesEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (h : ConfinedDiagonalPlacesEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_confinedRadicandPlacesEP ℓ hodd
    (confinedRadicandPlacesEP_of_confinedDiagonalPlacesEP ℓ h)

end Shafarevich

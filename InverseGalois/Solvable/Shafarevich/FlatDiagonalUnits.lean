/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedDiagonal
import InverseGalois.CFT.PoitouTate.RadicandPlaces
import InverseGalois.Solvable.Shafarevich.FlatNorm
import InverseGalois.Solvable.Shafarevich.FlatTensorDiagonal

/-!
# The diagonal of units, supplied one orbit at a time

The demand made of a choice of places asks for a diagonal of units at the chosen places.  This file
discharges it against the arithmetic input the prescription over a level is already stated in terms
of.

That input asks, for finitely many places lying in distinct orbits, for a unit at each of them whose
order there is prime to the exponent, which is a local power at a prescribed finite set of places,
at the proper conjugates of its own place and at every conjugate of the other named places, and
whose remaining ramification sits over the named places or over places completely decomposed in a
bigger level.  Those are exactly the four conditions a diagonal asks for, once the chosen set of
places is taken to be the hull of the named ones: a place of the hull is a conjugate of a named one,
and moving the unit belonging to that named place by the same automorphism moves neither its order
nor its being a local power.

Two things make the fit exact.  The named places arriving with the demand need not lie in distinct
orbits, but naming one place in each orbit they meet replaces them by ones that do without changing
the hull.  And the places the ramification is allowed at include those completely decomposed in the
bigger level, which is a property of a whole orbit when that level is Galois over the base, so the
set of them is its own stable core.

The demand is then discharged outright.  A unit at a named place of order prime to the exponent
there, a local power on the prescribed set, of order divisible by the exponent at the finitely many
other translates of the named places and confined elsewhere, is precisely what the reachability of
that place produces; no equivariance is asked of it, and equivariance was the only clause the
arithmetic could not meet.

The chosen set of places is the hull of the named ones — the smallest choice, and by the reckoning
of the descent the best one, since enlarging the set of places whose orders are read enlarges the
free module the descent runs over.

## Main definitions

* `InverseGalois.Shafarevich.HasFlatDiagonalUnits`: the arithmetic input of the prescription with
  its equivariance clause dropped.
* `Shafarevich.FlatDiagonalUnitsEP`: that input, made of every level.

## Main results

* `InverseGalois.Shafarevich.isGaloisStablePlaces_decomposedPlaces`: complete decomposition in a
  Galois level is a property of the whole orbit of a place.
* `InverseGalois.Shafarevich.hasFlatDiagonalUnits`: **reachable places carry the units**, and
  nothing further is asked of the level.
* `InverseGalois.Shafarevich.hasConfinedDiagonalPlaces_of_flatDiagonalUnits`: **the units of the
  prescription are the diagonal**, so the choice of places costs nothing beyond them.
* `Shafarevich.flatDiagonalUnitsEP`: **every level carries the units.**
* `Shafarevich.genericLevelStepEPRoots`: **the step of the ladder over an odd prime**, with nothing
  left to assume.

## Tags

Shafarevich's theorem, embedding problem, S-unit, confined unit, diagonal, orbit
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT CategoryTheory IsDedekindDomain MulAction NumberField Rigidity.RET
  TensorProduct groupCohomology

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### The arithmetic input with no equivariance in it -/

section Units

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **A unit of a level can be found for each of finitely many places lying in distinct orbits, of
order there prime to the exponent, a local power at a prescribed finite set of places those avoid,
of order divisible by the exponent at every proper conjugate of its own place and at every conjugate
of the others, and confined elsewhere to places sitting over the named ones or completely decomposed
in a given finite level.**

This is the arithmetic input of the prescription with the one clause dropped that asks the unit to
be carried to itself, up to an exponent-th power, by the automorphisms fixing its place.  The
remaining clauses are all that the orders of the confined units being onto costs. -/
def HasFlatDiagonalUnits (ℓ : ℕ) [NeZero ℓ] (K : IntermediateField k Ω) [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ (ι : Type) [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K)),
      (∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν) →
      ∀ Tz : Finset (HeightOneSpectrum (𝓞 ↥K)), (∀ μ : ι, w μ ∉ Tz) →
        (∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal) →
        (∀ μ : ι, IsReachablePlace ℓ K E (↑Tz) (w μ)) →
        ∃ Z : ι → (↥K)ˣ,
          (∀ μ : ι, ¬ (ℓ : ℤ) ∣ placeValue (w μ) (Z μ)) ∧
          (∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → localClassHom v ℓ (Z μ) = 1) ∧
          (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ≠ w μ → (ℓ : ℤ) ∣ placeValue (σ • w μ) (Z μ)) ∧
          (∀ μ ν : ι, ν ≠ μ → ∀ σ : Gal(↥K/k), (ℓ : ℤ) ∣ placeValue (σ • w ν) (Z μ)) ∧
          ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), ¬ (ℓ : ℤ) ∣ placeValue v (Z μ) →
            (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
              ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
                stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup

/-- The units of the prescription are in particular units with no equivariance asked of them. -/
theorem hasFlatDiagonalUnits_of_flatPrescribedUnits {ℓ : ℕ} [NeZero ℓ]
    {K : IntermediateField k Ω} [NumberField ↥K] (h : HasFlatPrescribedUnits ℓ K) :
    HasFlatDiagonalUnits ℓ K := by
  intro E hEfin hEgal hKE ι _ w hdist Tz hwTz hℓw hreach
  obtain ⟨Z, _, h2, h3, h4, h5, h6⟩ := h E hEfin hEgal hKE ι w hdist Tz hwTz hℓw hreach
  exact ⟨Z, h2, h3, h4, h5, h6⟩

/-- **Reachable places carry the units, and nothing further is asked of the level.**

The places the unit belonging to a named place is asked to have order divisible by the exponent at
are the translates of the named places other than that place itself; there are finitely many of
them, the level being finite over the base and the named places finite in number, and the place
itself is not among them.  Reachability there hands back a unit of order prime to the exponent at
the place, a local power on the prescribed set, of order divisible by the exponent on those
translates, and with its remaining ramification completely decomposed away from the place.  That is
every clause at once: the place itself is the one place the confinement says nothing about, and it
is covered by the first alternative of the clause that consumes it. -/
theorem hasFlatDiagonalUnits {ℓ : ℕ} [NeZero ℓ] (K : IntermediateField k Ω) [NumberField ↥K]
    [IsGalois k ↥K] [FiniteDimensional k ↥K] : HasFlatDiagonalUnits ℓ K := by
  classical
  intro E hEfin hEgal hKE ι _ w hdist Tz hwTz hℓw hreach
  haveI : Finite Gal(↥K/k) := Finite.of_fintype _
  have hstep : ∀ μ : ι, ∃ Z : (↥K)ˣ,
      ¬ (ℓ : ℤ) ∣ placeValue (w μ) Z ∧
      (∀ v : HeightOneSpectrum (𝓞 ↥K), v ∈ Tz → localClassHom v ℓ Z = 1) ∧
      (∀ (σ : Gal(↥K/k)) (ν : ι), σ • w ν ≠ w μ → (ℓ : ℤ) ∣ placeValue (σ • w ν) Z) ∧
      ∀ v : HeightOneSpectrum (𝓞 ↥K), ¬ (ℓ : ℤ) ∣ placeValue v Z →
        (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
          ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
            stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup := by
    intro μ
    obtain ⟨u, hord, hTzu, hXex, hconf⟩ :=
      hreach μ (fun hc => hwTz μ (Finset.mem_coe.1 hc))
        ({v : HeightOneSpectrum (𝓞 ↥K) | ∃ (σ : Gal(↥K/k)) (ν : ι), v = σ • w ν} \ {w μ})
        (Set.Finite.subset (Set.finite_range fun p : Gal(↥K/k) × ι => p.1 • w p.2)
          (by rintro v ⟨⟨σ, ν, rfl⟩, _⟩; exact ⟨(σ, ν), rfl⟩))
        (fun hcon => hcon.2 rfl)
    refine ⟨u, hord, fun v hv => hTzu v (Finset.mem_coe.2 hv),
      fun σ ν hσν => hXex _ ⟨⟨σ, ν, rfl⟩, hσν⟩, fun v hv => ?_⟩
    by_cases hvw : v = w μ
    · exact Or.inl ⟨μ, 1, by rw [hvw, one_smul]⟩
    · exact Or.inr (hconf v hvw hv)
  choose Z hZord hZTz hZex hZconf using hstep
  exact ⟨Z, hZord, hZTz, fun μ σ hσ => hZex μ σ μ hσ,
    fun μ ν hνμ σ => hZex μ σ ν (hdist ν μ hνμ σ), hZconf⟩

end Units

/-! ### Complete decomposition along an orbit -/

section Decomposed

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- **Complete decomposition in a Galois level is a property of the whole orbit of a place**, so the
places of a level lying below only primes completely decomposed in a bigger Galois level form a
stable set. -/
theorem isGaloisStablePlaces_decomposedPlaces {K E : IntermediateField k Ω} [NumberField ↥K]
    [IsGalois k ↥K] [IsGalois k ↥E] : IsGaloisStablePlaces k ↥K (decomposedPlaces K E) where
  smul_mem_iff σ v := by
    constructor
    · intro h
      have h2 := forall_stabilizer_le_fixingSubgroup_smul (E := E) σ⁻¹ h
      rwa [inv_smul_smul] at h2
    · exact fun h => forall_stabilizer_le_fixingSubgroup_smul (E := E) σ h

end Decomposed

/-! ### The units of the prescription are the diagonal -/

section Bridge

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- **The units of the prescription are the diagonal**, so the choice of places costs nothing beyond
them.

The chosen set of places is the hull of the named ones, and the units are asked for at
representatives of the orbits the named places meet, which have the same hull.  A place of the hull
is a translate of one of those representatives, and the unit belonging to it is the unit of the
representative moved by the same automorphism: its order there is the order of the original at the
representative, prime to the exponent; it is a local power at the places the radicand must stay
inert at, exactly where the original was one, and its order is divisible by the exponent at the
other translates of its own place and at every translate of the other representatives — that is, at
every other place of the hull.

Outside the places the ramification is allowed at, the order is divisible by the exponent because
the confinement clause leaves only two possibilities for a place where it is not: sitting over a
named place, which puts it in the hull, or completely decomposed in the bigger level, which puts it
in the stable core of the completely decomposed places, that set being its own core. -/
theorem hasConfinedDiagonalPlaces_of_flatDiagonalUnits {ℓ : ℕ} [Fact ℓ.Prime] [NeZero ℓ]
    {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K] [FiniteDimensional k ↥K]
    (hunits : HasFlatDiagonalUnits ℓ K) : HasConfinedDiagonalPlaces ℓ K := by
  classical
  intro E hEfin hEgal hKE Xs₀ Tz hXs₀ hTz hℓXs hreach _hbase hTzavoid
  haveI : Finite Gal(↥K/k) := Finite.of_fintype _
  haveI := isGaloisStablePlaces_decomposedPlaces (K := K) (E := E)
  obtain ⟨ι, hιfin, w, hwmem, hwdist, hwhull⟩ := exists_orbitReps (k := k) Xs₀ hXs₀
  haveI := hιfin
  have hXsfin : (stableHull k ↥K Xs₀).Finite := stableHull_finite hXs₀
  haveI : Finite ↥(stableHull k ↥K Xs₀) := hXsfin
  have hTzfin : (stableHull k ↥K Tz).Finite := stableHull_finite hTz
  have hnotTz : ∀ μ : ι, w μ ∉ hTzfin.toFinset := by
    intro μ hcon
    obtain ⟨σ, hσ⟩ := hTzfin.mem_toFinset.1 hcon
    exact hTzavoid (w μ) (hwmem μ) σ hσ
  have hcoeTz : (hTzfin.toFinset : Set (HeightOneSpectrum (𝓞 ↥K))) = stableHull k ↥K Tz :=
    hTzfin.coe_toFinset
  obtain ⟨Z, hZord, hZTz, hZconj, hZother, hZconf⟩ :=
    hunits E hEfin hEgal hKE ι w hwdist hTzfin.toFinset hnotTz
      (fun μ => hℓXs (w μ) (hwmem μ))
      (fun μ => by rw [hcoeTz]; exact hreach (w μ) (hwmem μ))
  have hdiagdata : ∀ y : ↥(stableHull k ↥K Xs₀), ∃ u : (↥K)ˣ,
      (∀ v ∈ stableHull k ↥K Tz, localClassHom v ℓ u = 1) ∧
      (∀ v ∉ allowedPlaces K E Xs₀, (ℓ : ℤ) ∣ ord ↥K v ((u : (↥K)ˣ) : ↥K)) ∧
      (∀ z : ↥(stableHull k ↥K Xs₀), z ≠ y →
        (ℓ : ℤ) ∣ ord ↥K (z : HeightOneSpectrum (𝓞 ↥K)) ((u : (↥K)ˣ) : ↥K)) ∧
      ¬ (ℓ : ℤ) ∣ ord ↥K (y : HeightOneSpectrum (𝓞 ↥K)) ((u : (↥K)ˣ) : ↥K) := by
    intro y
    have hy : (y : HeightOneSpectrum (𝓞 ↥K)) ∈ stableHull k ↥K (Set.range w) := by
      rw [hwhull]
      exact y.2
    rw [mem_stableHull] at hy
    obtain ⟨σ, μ, hμ⟩ := hy
    refine ⟨galUnits σ⁻¹ (Z μ), fun v hv => ?_, fun v hv => ?_, fun z hz => ?_, ?_⟩
    · have hv' : σ • v ∈ stableHull k ↥K Tz :=
        ((isGaloisStablePlaces_stableHull k ↥K Tz).smul_mem_iff σ v).2 hv
      have h1 := (localClassHom_galUnits_eq_one_iff (k := k) σ⁻¹ (σ • v) ℓ (Z μ)).2
        (hZTz μ (σ • v) (hTzfin.mem_toFinset.2 hv'))
      rwa [inv_smul_smul] at h1
    · by_contra hcon
      have hord : ord ↥K v ((galUnits σ⁻¹ (Z μ) : (↥K)ˣ) : ↥K)
          = ord ↥K (σ • v) ((Z μ : (↥K)ˣ) : ↥K) := by
        have h2 := ord_galUnits (k := k) σ⁻¹ (σ • v) (Z μ)
        rwa [inv_smul_smul] at h2
      rw [hord] at hcon
      have hpv : ¬ (ℓ : ℤ) ∣ placeValue (σ • v) (Z μ) := by
        rw [placeValue_eq_neg_ord, dvd_neg]
        exact hcon
      rcases hZconf μ (σ • v) hpv with ⟨ν, τ, hτ⟩ | hdec
      · refine hv (mem_allowedPlaces.2 (Or.inl ((mem_stableHull k ↥K Xs₀).2 ⟨τ⁻¹ * σ, ?_⟩)))
        rw [mul_smul, hτ, inv_smul_smul]
        exact hwmem ν
      · refine hv (mem_allowedPlaces.2 (Or.inr ?_))
        rw [stableCore_eq_self (k := k) (S := decomposedPlaces K E)]
        have h3 := forall_stabilizer_le_fixingSubgroup_smul (E := E) σ⁻¹ hdec
        rwa [inv_smul_smul] at h3
    · have hz' : (z : HeightOneSpectrum (𝓞 ↥K)) ∈ stableHull k ↥K (Set.range w) := by
        rw [hwhull]
        exact z.2
      rw [mem_stableHull] at hz'
      obtain ⟨τ, ν, hν⟩ := hz'
      have hzσ : σ • (z : HeightOneSpectrum (𝓞 ↥K)) = (σ * τ⁻¹) • w ν := by
        rw [hν, mul_smul, inv_smul_smul]
      have key : (ℓ : ℤ) ∣ placeValue (σ • (z : HeightOneSpectrum (𝓞 ↥K))) (Z μ) := by
        rw [hzσ]
        rcases eq_or_ne ν μ with hνμ | hνμ
        · rw [hνμ]
          refine hZconj μ (σ * τ⁻¹) ?_
          intro hfix
          refine hz (Subtype.ext (smul_left_cancel σ ?_))
          rw [hzσ, hνμ, hfix, hμ]
        · exact hZother μ ν hνμ (σ * τ⁻¹)
      have hord : ord ↥K (z : HeightOneSpectrum (𝓞 ↥K)) ((galUnits σ⁻¹ (Z μ) : (↥K)ˣ) : ↥K)
          = ord ↥K (σ • (z : HeightOneSpectrum (𝓞 ↥K))) ((Z μ : (↥K)ˣ) : ↥K) := by
        have h4 := ord_galUnits (k := k) σ⁻¹ (σ • (z : HeightOneSpectrum (𝓞 ↥K))) (Z μ)
        rwa [inv_smul_smul] at h4
      rw [hord]
      rwa [placeValue_eq_neg_ord, dvd_neg] at key
    · have hord : ord ↥K (y : HeightOneSpectrum (𝓞 ↥K)) ((galUnits σ⁻¹ (Z μ) : (↥K)ˣ) : ↥K)
          = ord ↥K (w μ) ((Z μ : (↥K)ˣ) : ↥K) := by
        have h5 := ord_galUnits (k := k) σ⁻¹ (σ • (y : HeightOneSpectrum (𝓞 ↥K))) (Z μ)
        rw [inv_smul_smul] at h5
        rw [h5, hμ]
      rw [hord]
      have h6 := hZord μ
      rwa [placeValue_eq_neg_ord, dvd_neg] at h6
  exact ⟨stableHull k ↥K Xs₀, inferInstance, inferInstance, inferInstance,
    subset_stableHull k ↥K Xs₀, hdiagdata⟩

end Bridge

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich

-- Pin `Algebra ℚ ↥K` to the tower instance rather than `DivisionRing.toRatAlgebra`.
attribute [local instance 2000] IntermediateField.algebra'

/-! ### The input, made of every level -/

/-- **Every finite Galois level of a number field inside an algebraic closure carrying a primitive
root of unity of the exponent carries the units the prescription asks for at finitely many places
lying in distinct orbits**, with no equivariance asked of them. -/
def FlatDiagonalUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]
      (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K],
      (∃ ζ : ↥K, IsPrimitiveRoot ζ ℓ) → HasFlatDiagonalUnits ℓ K

/-- **Every level carries the units**, the reachability of a named place being all they cost. -/
theorem flatDiagonalUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : FlatDiagonalUnitsEP ℓ := by
  intro k Ω _ _ _ _ _ _ K _ _ _ _
  exact hasFlatDiagonalUnits K

/-- **The units buy the choice of places.** -/
theorem confinedDiagonalPlacesEP_of_flatDiagonalUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hunits : FlatDiagonalUnitsEP ℓ) : ConfinedDiagonalPlacesEP ℓ := by
  intro Ω _ _ _ _ K _ _ _ hζ
  exact hasConfinedDiagonalPlaces_of_flatDiagonalUnits (hunits ℚ Ω K hζ)

/-- **The step of the ladder over an odd prime, in exchange for the units.** -/
theorem genericLevelStepEPRoots_of_flatDiagonalUnitsEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (hunits : FlatDiagonalUnitsEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_confinedDiagonalPlacesEP ℓ hodd
    (confinedDiagonalPlacesEP_of_flatDiagonalUnitsEP ℓ hunits)

/-- **The step of the ladder over an odd prime**, with nothing left to assume: a place reachable in
the bigger level carries the unit the diagonal wants there, the diagonal makes every system of
orders at the chosen places the system of orders of a confined unit, and the correction room the
second reading of those units needs is bounded by the refined class group of the level. -/
theorem genericLevelStepEPRoots (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] (hodd : 2 < ℓ) :
    GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_flatDiagonalUnitsEP ℓ hodd (flatDiagonalUnitsEP ℓ)

end Shafarevich

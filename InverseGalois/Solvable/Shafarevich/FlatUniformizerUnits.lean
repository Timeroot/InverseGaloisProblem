/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.UniformizerLine
import InverseGalois.Solvable.Shafarevich.FlatLineUnits

/-!
# The families of units named on the line of an invariant uniformiser

The two-place construction prescribes the classes of a family of units at finitely many named
places on a line which is carried along by the automorphisms of the level, and a demand naming one
place in each of finitely many distinct orbits has no way of spreading a line named at one place
over its orbit.  The family of local unit groups supplies the line instead: it carries a Galois
invariant section whose value is a uniformiser at every place carrying one fixed by its
decomposition group, and the classes of the values of that section are a line at every place at
once, equivariant on the nose.

At a place carrying a uniformiser fixed by its decomposition group the valuation of that line is
one, so a unit whose class there is the line is ramified there, which is the other half of what a
prescription ramified at a place needs.  The reciprocity residue the construction still costs is,
on a line, a purely local demand at each named place taken on its own: the classes there of the
units of the level which become exponent-th powers in the auxiliary field are asked to lie on the
same line.  On the line of the invariant uniformiser that is the classical condition that the
extension of the completion cut out at a named place be the one a root of the uniformiser
generates.

## Main results

* `InverseGalois.Shafarevich.exists_units_uniformizerLine_named` — **classes lying on the line of
  the invariant uniformiser can be prescribed at one place in each of finitely many distinct
  orbits**, the family being trivial at a prescribed finite set of places, at every conjugate of a
  named place which is not itself named, and ramified only over the named places or at places
  completely decomposed in the auxiliary field.
* `InverseGalois.Shafarevich.exists_units_uniformizerLine_diagonal` — **one unit per named place,
  ramified at its own place and trivial at the others**, which is the diagonal the orders of the
  confined units are read off.
* `InverseGalois.Shafarevich.isNamedOrthogonal_uniformizerLine` — **the reciprocity residue of a
  naming on the line of the invariant uniformiser is trivial** as soon as, at each named place, the
  units of the level which become exponent-th powers in the auxiliary field have their classes on
  that line.
* `InverseGalois.Shafarevich.exists_units_uniformizerLine_diagonal_of_scholz` — **the diagonal, in
  exchange for that local demand at the named places alone**.

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, uniformiser, local class, reciprocity
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

section Uniformizer

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω]

/-- **Classes lying on the line of the invariant uniformiser can be prescribed at one place in each
of finitely many distinct orbits.**

The line is the same at every place, so nothing has to be spread and the orbits of the named places
are free of any further demand; the finite level the leftover places are asked to be decomposed in
serves as the auxiliary field of the two-place construction. -/
theorem exists_units_uniformizerLine_named {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hodd : 2 < ℓ)
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
    {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (E : IntermediateField k Ω)
    (hEfin : FiniteDimensional k ↥E) (hEgal : IsGalois k ↥E) (hKE : K ≤ E)
    {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K))
    (hdist : ∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν)
    (Tz : Finset (HeightOneSpectrum (𝓞 ↥K))) (hTz : ∀ μ : ι, w μ ∉ Tz)
    (hℓw : ∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal)
    {d : ℕ} (c : (μ : ι) → Fin d → localClasses (w μ) ℓ)
    (hline : ∀ (μ : ι) (q : Fin d), c μ q ∈ Subgroup.zpowers (uniformizerLine k ℓ (w μ)))
    (hnorth : IsNamedOrthogonal ℓ K hres hζ E w c) :
    ∃ z : Fin d → (↥K)ˣ,
      (∀ (q : Fin d) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → localClassHom v ℓ (z q) = 1) ∧
      (∀ (μ : ι) (q : Fin d), localClassHom (w μ) ℓ (z q) = c μ q) ∧
      (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ≠ w μ →
        ∀ q : Fin d, localClassHom (σ • w μ) ℓ (z q) = 1) ∧
      ∀ v : HeightOneSpectrum (𝓞 ↥K), (∃ q : Fin d, ¬ (ℓ : ℤ) ∣ placeValue v (z q)) →
        (∃ (μ : ι) (σ : Gal(↥K/k)), v = σ • w μ) ∨
          ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
            stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup :=
  exists_units_line_named hℓ hodd K hres hζ E hEfin hEgal hKE
    (fun σ v => uniformizerLine_zpowers_smul ℓ σ v) w hdist Tz hTz hℓw c hline hnorth

/-- **One unit per named place, ramified at its own place and trivial at the others.**

At a place carrying a uniformiser fixed by its decomposition group the valuation of the line is
one, so the unit of a coordinate is ramified at its own place. -/
theorem exists_units_uniformizerLine_diagonal {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hodd : 2 < ℓ)
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
    {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (E : IntermediateField k Ω)
    (hEfin : FiniteDimensional k ↥E) (hEgal : IsGalois k ↥E) (hKE : K ≤ E)
    {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K))
    (hdist : ∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν)
    (Tz : Finset (HeightOneSpectrum (𝓞 ↥K))) (hTz : ∀ μ : ι, w μ ∉ Tz)
    (hℓw : ∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal)
    (hfix : ∀ μ : ι, w μ ∈ fixedUniformizerPlaces k ↥K) (e : ι ≃ Fin (Fintype.card ι))
    (hnorth : IsNamedOrthogonal ℓ K hres hζ E w
      (fun μ q => if e μ = q then uniformizerLine k ℓ (w μ) else 1)) :
    ∃ Z : ι → (↥K)ˣ,
      (∀ μ : ι, ¬ (ℓ : ℤ) ∣ placeValue (w μ) (Z μ)) ∧
      (∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → localClassHom v ℓ (Z μ) = 1) ∧
      (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ≠ w μ → localClassHom (σ • w μ) ℓ (Z μ) = 1) ∧
      (∀ μ ν : ι, ν ≠ μ → ∀ σ : Gal(↥K/k), localClassHom (σ • w ν) ℓ (Z μ) = 1) ∧
      ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), ¬ (ℓ : ℤ) ∣ placeValue v (Z μ) →
        (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
          ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
            stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup :=
  exists_units_line_diagonal hℓ hodd K hres hζ E hEfin hEgal hKE
    (fun σ v => uniformizerLine_zpowers_smul ℓ σ v) w hdist Tz hTz hℓw
    (fun μ _ ha => not_dvd_placeValue_of_localClassHom_eq_uniformizerLine hℓ.one_lt (hfix μ) ha)
    e hnorth

/-! ### The reciprocity residue of a naming on the line -/

omit [NumberField k] [IsGalois k Ω] [IsAlgClosed Ω] in
/-- **A naming on the line of the invariant uniformiser is orthogonal to the units of the level
which become exponent-th powers in the auxiliary field**, as soon as the classes of those units at
the named places lie on that line too.

What is asked of a named place is local and says nothing whatever about the other named places, nor
about any place the naming is not made at: the class at it of a unit which becomes an exponent-th
power in the auxiliary field is a power of the class of the uniformiser there. -/
theorem isNamedOrthogonal_uniformizerLine {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hodd : 2 < ℓ)
    (K : IntermediateField k Ω) [NumberField ↥K]
    {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (E : IntermediateField k Ω)
    {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K)) {d : ℕ}
    {c : (μ : ι) → Fin d → localClasses (w μ) ℓ}
    (hline : ∀ (μ : ι) (q : Fin d), c μ q ∈ Subgroup.zpowers (uniformizerLine k ℓ (w μ)))
    (hscholz : ∀ (μ : ι) (u : (↥K)ˣ), (∃ y : Ω, y ∈ E ∧ y ^ ℓ = algebraMap ↥K Ω ((u : ↥K))) →
      localClassHom (w μ) ℓ u ∈ Subgroup.zpowers (uniformizerLine k ℓ (w μ))) :
    IsNamedOrthogonal ℓ K hres hζ E w c :=
  isNamedOrthogonal_line hℓ hodd K hres hζ E w hline hscholz

/-- **One unit per named place, ramified at its own place and trivial at the others, in exchange
for a local demand at the named places alone.**

The naming is the diagonal on the lines of the invariant uniformiser, so the reciprocity residue is
read off those lines: at each named place the classes of the units of the level which become
exponent-th powers in the auxiliary field are asked to be powers of the class of the uniformiser
there, and nothing at all is asked anywhere else. -/
theorem exists_units_uniformizerLine_diagonal_of_scholz {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    (hodd : 2 < ℓ) (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K]
    [NumberField ↥K] {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (E : IntermediateField k Ω)
    (hEfin : FiniteDimensional k ↥E) (hEgal : IsGalois k ↥E) (hKE : K ≤ E)
    {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K))
    (hdist : ∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν)
    (Tz : Finset (HeightOneSpectrum (𝓞 ↥K))) (hTz : ∀ μ : ι, w μ ∉ Tz)
    (hℓw : ∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal)
    (hfix : ∀ μ : ι, w μ ∈ fixedUniformizerPlaces k ↥K)
    (hscholz : ∀ (μ : ι) (u : (↥K)ˣ), (∃ y : Ω, y ∈ E ∧ y ^ ℓ = algebraMap ↥K Ω ((u : ↥K))) →
      localClassHom (w μ) ℓ u ∈ Subgroup.zpowers (uniformizerLine k ℓ (w μ))) :
    ∃ Z : ι → (↥K)ˣ,
      (∀ μ : ι, ¬ (ℓ : ℤ) ∣ placeValue (w μ) (Z μ)) ∧
      (∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → localClassHom v ℓ (Z μ) = 1) ∧
      (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ≠ w μ → localClassHom (σ • w μ) ℓ (Z μ) = 1) ∧
      (∀ μ ν : ι, ν ≠ μ → ∀ σ : Gal(↥K/k), localClassHom (σ • w ν) ℓ (Z μ) = 1) ∧
      ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), ¬ (ℓ : ℤ) ∣ placeValue v (Z μ) →
        (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
          ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
            stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup :=
  exists_units_line_diagonal_of_scholz hℓ hodd K hres hζ E hEfin hEgal hKE
    (fun σ v => uniformizerLine_zpowers_smul ℓ σ v) w hdist Tz hTz hℓw
    (fun μ _ ha => not_dvd_placeValue_of_localClassHom_eq_uniformizerLine hℓ.one_lt (hfix μ) ha)
    hscholz

end Uniformizer

end InverseGalois.Shafarevich

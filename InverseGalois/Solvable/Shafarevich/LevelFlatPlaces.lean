/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.KernelPlaces
import InverseGalois.Solvable.Shafarevich.LayerShaLevel
import InverseGalois.Solvable.Shafarevich.LevelFlatOrbit
import InverseGalois.Solvable.Shafarevich.LevelFlatRadicand

/-!
# The prescription at one named prime, traced over the automorphisms fixing its place

Over the field the base realization cuts out, the part of inertia at a prime away from the exponent
which that realization kills is carried by a single element modulo an open subgroup, so a
homomorphism of it into the layer is a power of a single one of its own values.  The homomorphism
belonging to a named prime is therefore assembled out of the conjugates of one unit of the level:
one coefficient of the layer for each automorphism of the level fixing the place below the prime,
sitting over the conjugate of the unit by that automorphism, and the coefficient one over every
automorphism moving that place.

The clause which decides the shape of the assembly is equivariance along the decomposition subgroup
of the named prime.  Conjugating the argument by an automorphism fixing the prime permutes the
conjugates of the unit by translation and multiplies every Kummer character by the power to which
that automorphism raises the roots of unity, so the assembled homomorphism is equivariant exactly
when the coefficients are carried into one another by the same translation, twisted by that power.
A family of coefficients with that property is a twisted orbit, and the value the assembly takes
where the character takes the value one is the product of the orbit.  What is asked of the layer is
therefore that a prescribed value carried to its own twisted powers by the automorphisms fixing the
place be the product of such an orbit — a twisted norm — and that is asked of the layer alone, of no
field.

The conjugates of the unit enter the assembly separately, each under its own coefficient, so no
invariance is asked of the unit: only its local behaviour.  Its order at its own place is prime to
the exponent, it is a local power at a prescribed finite set of places, at every proper conjugate of
its own place, and at every conjugate of the other named places, and at every further place where
its order is not divisible by the exponent it either sits over a named place or has its place
completely decomposed in a prescribed finite level.

The characters of the conjugates agree on inertia at the named prime, which is what lets the
assembly be read as a single power there: two units differing by an automorphism fixing the place
below the prime have the same order at that place, and Kummer characters at a prime away from the
exponent depend on the unit only through that order.

## Main definitions

* `InverseGalois.Shafarevich.HasFlatRadicands` — **one unit of a level for each of finitely many
  places lying in distinct orbits, of order at its own place prime to the exponent, a local power
  at a prescribed finite set of places and at every conjugate of the named places other than its
  own, and confined elsewhere to places sitting over the named ones or completely decomposed in a
  given finite level.**
* `InverseGalois.Shafarevich.TwistedNormEP` — **after one shrinking of the operator group, an
  element of a layer carried by a subgroup to the powers of itself by which that subgroup raises
  the roots of unity is the product of a twisted orbit of that subgroup.**

## Main results

* `InverseGalois.Shafarevich.hasFlatOrbitPrescription_of_places` — **a level carrying such units,
  over a layer carrying such twisted norms, carries the prescription read one named prime at a
  time.**

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, radicand, inertia subgroup, equivariance
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

/-! ### The arithmetic input -/

section Radicands

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **One unit of a level for each of finitely many places lying in distinct orbits, of order at
its own place prime to the exponent, a local power at a prescribed finite set of places and at
every conjugate of the named places other than its own, and confined elsewhere to places sitting
over the named ones or completely decomposed in a given finite level.**

The places are named by an arbitrary finite index type and are asked to lie in pairwise distinct
orbits under the automorphisms of the level over the base, which is what keeps the demand made at
one of them from colliding with the demand made at the others.

The order of the unit at its own place is asked to be prime to the exponent, which is the one thing
the prescription needs of it there: the Kummer character of such a unit takes a value which is a
unit on the part of inertia the base realization kills, and every character of that part is then
proportional to it.  No local class is prescribed, the coefficient of proportionality being read off
after the unit is chosen.

The set of places at which the unit is asked to be a local power is prescribed along with the named
places and is asked to avoid them, which is the only thing that keeps the two demands from
colliding.  The places above the exponent are covered by that set rather than by a clause of their
own, and a named place is asked not to be one of them, which is the same disjointness read at the
exponent.

The finite level in which the leftover places are asked to be completely decomposed is part of the
demand, so that a level cutting out any prescribed finite amount of arithmetic may be named before
the units are chosen; it is asked to be Galois over the base, which costs nothing, a level being
contained in its normal closure and a place decomposed in the larger field decomposed in the
smaller.

Nothing is asked of the unit under the automorphisms of the level: the conjugates of the unit are
spent separately, each under a coefficient of its own. -/
def HasFlatRadicands (ℓ : ℕ) [NeZero ℓ] (K : IntermediateField k Ω) [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ (ι : Type) [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K)),
      (∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν) →
      ∀ Tz : Finset (HeightOneSpectrum (𝓞 ↥K)), (∀ μ : ι, w μ ∉ Tz) →
        (∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal) →
        ∃ z : ι → (↥K)ˣ,
          (∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → localClassHom v ℓ (z μ) = 1) ∧
          (∀ μ : ι, ¬ (ℓ : ℤ) ∣ placeValue (w μ) (z μ)) ∧
          (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ≠ w μ → localClassHom (σ • w μ) ℓ (z μ) = 1) ∧
          (∀ μ ν : ι, ν ≠ μ → ∀ σ : Gal(↥K/k), localClassHom (σ • w ν) ℓ (z μ) = 1) ∧
          ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), ¬ (ℓ : ℤ) ∣ placeValue v (z μ) →
            (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
              ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
                stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup

end Radicands

/-! ### The input from the layer -/

/-- **After one shrinking of the operator group, an element of a layer carried by a subgroup to the
powers of itself by which that subgroup raises the roots of unity is the product of a twisted orbit
of that subgroup.**

A twisted orbit of a subgroup is a family of elements of the layer supported on that subgroup and
carried into one another by translation along it, each translation being accompanied by the
operator the group acts by and by the power to which it raises the roots of unity.  Such a family
is determined by any one of its values, and its product is a twisted norm from the subgroup; the
demand is that every element carried to its own twisted powers by the subgroup be such a product.

Finitely many elements are asked for at once, one for each member of an arbitrary finite family of
subgroups, and one shrinking of the operator group serves them all.  The shrinking is onto the
intended rank, which is named in advance, and the rank it starts from is named before the family
is; nothing else about the family is fixed in advance.

The group acting is an arbitrary finite one carried into the operator group by an injection,
together with the character by which it raises the roots of unity; nothing is asked of the two
except that the first be injective, which is what an operator group cutting out a level supplies. -/
def TwistedNormEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : Prop :=
  ∀ (U : Type) [Group U] [Finite U] (S : Type) [Group S] [Finite S] (n j : ℕ),
    ∃ N : ℕ, ∀ (ι : Type) [Fintype ι] (G : Type) [Group G] [Fintype G] (ψ : G →* U)
        (ee : G →* (ZMod ℓ)ˣ) (Z : ι → Subgroup G) (V : ι → ↥(layerSub ℓ (Generic U N S) j)),
      Function.Injective ψ →
      (∀ (μ : ι) (σ : G), σ ∈ Z μ → ψ σ • V μ = V μ ^ ((ee σ : (ZMod ℓ)ˣ) : ZMod ℓ).val) →
      ∃ (β : Generic U N S →* Generic U n S) (_ : IsOperatorHom β), Function.Surjective β ∧
        ∃ b : ι → G → ↥(layerSub ℓ (Generic U n S) j),
          (∀ (μ : ι) (σ : G), σ ∉ Z μ → b μ σ = 1) ∧
          (∀ (μ : ι) (σ g : G), g ∈ Z μ →
            b μ σ ^ ((ee g : (ZMod ℓ)ˣ) : ZMod ℓ).val = ψ g • b μ (g⁻¹ * σ)) ∧
          ∀ μ : ι, layerSubMap ℓ β j (V μ) = ∏ σ, b μ σ

/-! ### The prescription -/

section Places

variable {ℓ : ℕ} [Fact ℓ.Prime] [NeZero ℓ] {U : Type} [Group U] [Finite U] {n : ℕ} {S : Type}
  [Group S] [Finite S] {j : ℕ} {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] {φ : Gal(Ω/k) →* U} {t : ℕ} {D : Fin t → Subgroup Gal(Ω/k)}

attribute [local instance] genericQuotAction zmodTrivialAction

/-- **A level carrying one radicand for each named place, over a layer carrying the twisted norms,
carries the prescription read one named prime at a time.**

The homomorphism belonging to a named prime is assembled out of the conjugates of the single unit
belonging to the place below it: one coefficient of the layer for each automorphism of the level,
sitting over the conjugate of the unit by that automorphism, with the coefficient one over every
automorphism moving the place.  Its value at an element of the prescribed subgroup is the product
of the coefficients raised to the common value the characters of the conjugates take there — common
because two units differing by an automorphism fixing the place have the same order at it, and a
Kummer character at a prime away from the exponent sees the unit only through that order.

Equivariance along the decomposition subgroup of the named prime is bought from the layer.  An
automorphism fixing the prime translates the conjugates of the unit and raises every character by
the power by which it raises the roots of unity, so the assembly is carried by the operator group
exactly when the coefficients form a twisted orbit; the prescribed values already have equivariance
of that shape, and the product of the orbit is asked to be the value at the element where the
character takes the value one, which is the element every prescribed value is a power of.

The remaining clauses are read off the unit place by place.  Triviality along the finite family,
and along the subgroups belonging to the other named primes, and along the decomposition subgroups
of the conjugates of the prime outside the saturation, is triviality of the local class of every
conjugate of the unit at the corresponding place, which is the same statement read at the conjugate
place.  Where the assembled homomorphism ramifies, one conjugate of the unit has order at the place
below not divisible by the exponent, hence so does the unit itself at the conjugate place, and the
confinement clause then says the prime sits over a named place — in which case it is a conjugate of
that named prime, two primes with the same place below differing by an automorphism of the level —
or that its place is completely decomposed in a finite level killing the given lift, whence the
whole decomposition subgroup dies there.

The finite level in which the leftover places are asked to be completely decomposed is the normal
closure of the level together with a finite level killing the given lift, which exists because that
lift is smooth and the trivial subgroup of a finite discrete group is open. -/
theorem hasFlatOrbitPrescription_of_places (K : IntermediateField k Ω)
    [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hkd : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)
    {Pr : Fin t → Ideal (𝓞 Ω)} (hPrp : ∀ ν, (Pr ν).IsPrime) (hPrbot : ∀ ν, Pr ν ≠ ⊥)
    (hDPr : ∀ ν, D ν = stabilizer Gal(Ω/k) (Pr ν))
    (hℓPr : ∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : 𝓞 ↥K) ∈ v.asIdeal →
      ∃ (σ : Gal(↥K/k)) (ν : Fin t), v = σ • placeUnder K (Pr ν) (hPrbot ν))
    (htw : TwistedNormEP ℓ) (hrad : HasFlatRadicands ℓ K) :
    HasFlatOrbitPrescription ℓ U n S j φ D := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  haveI : IsGalois ↥K Ω := IsGalois.tower_top_of_isGalois k ↥K Ω
  -- the values at a place, read off the multiplicativity of the order
  have hpvone : ∀ v : HeightOneSpectrum (𝓞 ↥K), placeValue v (1 : (↥K)ˣ) = 0 := by
    intro v
    have h1 := placeValue_mul v 1 1
    rw [mul_one] at h1
    omega
  have hpvdiv : ∀ (v : HeightOneSpectrum (𝓞 ↥K)) (a b : (↥K)ˣ),
      placeValue v a = placeValue v b → placeValue v (a * b⁻¹) = 0 := by
    intro v a b hab
    have h1 := placeValue_mul v a b⁻¹
    have h2 := placeValue_mul v b b⁻¹
    rw [mul_inv_cancel, hpvone] at h2
    omega
  have hlccong : ∀ (v v' : HeightOneSpectrum (𝓞 ↥K)) (x : (↥K)ˣ), v = v' →
      localClassHom v ℓ x = 1 → localClassHom v' ℓ x = 1 := by
    rintro v v' x rfl h
    exact h
  obtain ⟨N, hN⟩ := htw U S n j
  refine ⟨N, ?_⟩
  intro F ι hιfin Q A a _ hFsm _ hQp hQbot hQℓ hQorb hAstab hAker hAeq _ hasm haequiv havoid
  haveI := hιfin
  haveI : ∀ μ, (Q μ).IsPrime := hQp
  haveI : ∀ ν, (Pr ν).IsPrime := hPrp
  letI : Fintype ι := Fintype.ofFinite ι
  -- a finite level killing the given lift, enlarged to contain the level and made Galois
  obtain ⟨N', hN', hN'F⟩ := hFsm ⊥ isOpenNormal_bot
  obtain ⟨E₀, hE₀fin, -, hE₀N⟩ := exists_fixingSubgroup_le hN'
  haveI := hE₀fin
  obtain ⟨E, hEfin, hEnorm, hKE, hE₀E⟩ : ∃ E : IntermediateField k Ω, FiniteDimensional k ↥E ∧
      Normal k ↥E ∧ K ≤ E ∧ E₀ ≤ E :=
    ⟨normalClosure k ↥(E₀ ⊔ K) Ω, inferInstance, inferInstance,
      le_trans le_sup_right (IntermediateField.le_normalClosure _),
      le_trans le_sup_left (IntermediateField.le_normalClosure _)⟩
  haveI := hEfin
  haveI := hEnorm
  haveI hEgal : IsGalois k ↥E := ⟨⟩
  have hEF : E.fixingSubgroup ≤ F.ker := fun x hx =>
    hN'F (hE₀N (fixingSubgroup_antitone hE₀E hx))
  -- the places below the named primes lie in pairwise distinct orbits
  have hwdist : ∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k),
      σ • placeUnder K (Q μ) (hQbot μ) ≠ placeUnder K (Q ν) (hQbot ν) := by
    intro μ ν hμν σ heq
    obtain ⟨ρ, hρ⟩ := restrictNormalHom_surjective_level K σ
    have hbot : ρ • Q μ ≠ ⊥ := by
      intro h0
      exact hQbot μ (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ⁻¹ • I) h0)
    have hpl : placeUnder K (ρ • Q μ) hbot = placeUnder K (Q ν) (hQbot ν) := by
      refine HeightOneSpectrum.ext ?_
      rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot μ) ρ, hρ, heq]
    obtain ⟨τ, -, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot (hQbot ν) hpl
    exact hQorb μ ν hμν (τ * ρ) (by rw [mul_smul]; exact hτ)
  -- the places carrying the finite family, and the named places avoiding them
  obtain ⟨Tz, hmemTz, hdisj⟩ : ∃ Tz : Finset (HeightOneSpectrum (𝓞 ↥K)),
      (∀ (σ : Gal(↥K/k)) (ν : Fin t), σ • placeUnder K (Pr ν) (hPrbot ν) ∈ Tz) ∧
        ∀ μ : ι, placeUnder K (Q μ) (hQbot μ) ∉ Tz := by
    refine ⟨Finset.image
      (fun στ : Gal(↥K/k) × Fin t => στ.1 • placeUnder K (Pr στ.2) (hPrbot στ.2)) Finset.univ,
      fun σ ν => Finset.mem_image.2 ⟨(σ, ν), Finset.mem_univ _, rfl⟩, ?_⟩
    intro μ hmem
    obtain ⟨⟨σ, ν⟩, -, hσν⟩ := Finset.mem_image.1 hmem
    have hσν' : σ • placeUnder K (Pr ν) (hPrbot ν) = placeUnder K (Q μ) (hQbot μ) := hσν
    obtain ⟨ρ₀, hρ₀⟩ := restrictNormalHom_surjective_level K σ
    have hbot : ρ₀ • Pr ν ≠ ⊥ := by
      intro h0
      exact hPrbot ν (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ₀⁻¹ • I) h0)
    have hpl : placeUnder K (ρ₀ • Pr ν) hbot = placeUnder K (Q μ) (hQbot μ) := by
      refine HeightOneSpectrum.ext ?_
      rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hPrbot ν) ρ₀, hρ₀, hσν']
    obtain ⟨τ, -, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot (hQbot μ) hpl
    obtain ⟨y, hy, hyn⟩ := havoid μ ν (τ * ρ₀)⁻¹
    have hy' : y ∈ stabilizer Gal(Ω/k) ((τ * ρ₀) • Pr ν) := by
      rw [mul_smul, ← hτ]
      exact hy
    refine hyn ?_
    rw [hDPr ν, inv_inv]
    exact mem_stabilizer_smul_iff.1 hy'
  have hdisjℓ : ∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (placeUnder K (Q μ) (hQbot μ)).asIdeal := by
    intro μ hmem
    obtain ⟨σ, ν, hσν⟩ := hℓPr _ hmem
    exact hdisj μ (hσν ▸ hmemTz σ ν)
  -- the radicands
  obtain ⟨z, hzT, hzord, hzconj, hzother, hzram⟩ :=
    hrad E hEfin hEgal hKE ι (fun μ => placeUnder K (Q μ) (hQbot μ)) hwdist Tz hdisj hdisjℓ
  -- the automorphisms of the level fixing the place below a named prime
  obtain ⟨Zs, hZs⟩ : ∃ Zs : ι → Subgroup Gal(↥K/k), ∀ μ : ι,
      Zs μ = stabilizer Gal(↥K/k) (placeUnder K (Q μ) (hQbot μ)) := ⟨_, fun _ => rfl⟩
  have hmemZs : ∀ (μ : ι) (σ : Gal(↥K/k)),
      σ ∈ Zs μ ↔ σ • placeUnder K (Q μ) (hQbot μ) = placeUnder K (Q μ) (hQbot μ) := by
    intro μ σ
    rw [hZs μ]
    exact mem_stabilizer_iff
  -- the conjugates of the radicand, one for each automorphism of the level
  obtain ⟨zz, hzzin, hzzout⟩ : ∃ zz : ι → Gal(↥K/k) → (↥K)ˣ,
      (∀ (μ : ι) (σ : Gal(↥K/k)), σ ∈ Zs μ → zz μ σ = σ • z μ) ∧
      ∀ (μ : ι) (σ : Gal(↥K/k)), σ ∉ Zs μ → zz μ σ = 1 :=
    ⟨fun μ σ => if σ ∈ Zs μ then σ • z μ else 1, fun _ _ h => if_pos h, fun _ _ h => if_neg h⟩
  have hzzone : ∀ (μ : ι) (σ : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)),
      (σ ∈ Zs μ → localClassHom (σ⁻¹ • v) ℓ (z μ) = 1) → localClassHom v ℓ (zz μ σ) = 1 := by
    intro μ σ v hv
    by_cases hσ : σ ∈ Zs μ
    · rw [hzzin μ σ hσ]
      have h1 := localClassesGalEquiv_localClassHom σ (σ⁻¹ • v) ℓ (z μ)
      rw [hv hσ, _root_.map_one, smul_inv_smul, galUnits_eq_smul] at h1
      exact h1.symm
    · rw [hzzout μ σ hσ, _root_.map_one]
  have hzzconj : ∀ (μ : ι) (σ ρ : Gal(↥K/k)),
      ρ • placeUnder K (Q μ) (hQbot μ) ≠ placeUnder K (Q μ) (hQbot μ) →
      localClassHom (ρ • placeUnder K (Q μ) (hQbot μ)) ℓ (zz μ σ) = 1 := by
    intro μ σ ρ hne
    refine hzzone μ σ _ fun hσ => ?_
    have hne' : (σ⁻¹ * ρ) • placeUnder K (Q μ) (hQbot μ)
        ≠ placeUnder K (Q μ) (hQbot μ) := by
      intro heq
      refine hne ?_
      calc ρ • placeUnder K (Q μ) (hQbot μ)
          = σ • ((σ⁻¹ * ρ) • placeUnder K (Q μ) (hQbot μ)) := by
            rw [← mul_smul, mul_inv_cancel_left]
        _ = σ • placeUnder K (Q μ) (hQbot μ) := by rw [heq]
        _ = placeUnder K (Q μ) (hQbot μ) := (hmemZs μ σ).1 hσ
    exact hlccong _ _ _ (mul_smul σ⁻¹ ρ (placeUnder K (Q μ) (hQbot μ))) (hzconj μ _ hne')
  -- the characters of the conjugates agree on inertia at the named prime
  have hconjchar : ∀ (μ : ι) (σ : Gal(↥K/k)), σ ∈ Zs μ → ∀ τ : Gal(Ω/↥K),
      τ ∈ Ideal.inertia Gal(Ω/↥K) (Q μ) →
      kummerChar hkd (σ • z μ) τ = kummerChar hkd (z μ) τ := by
    intro μ σ hσ τ hτ
    refine kummerChar_eq_of_dvd_placeValue hkd hℓ (hQℓ μ)
      (v := placeUnder K (Q μ) (hQbot μ)) rfl ?_ hτ
    have hpv : placeValue (placeUnder K (Q μ) (hQbot μ)) (σ • z μ)
        = placeValue (placeUnder K (Q μ) (hQbot μ)) (z μ) := by
      have h1 := placeValue_galSmul (placeUnder K (Q μ) (hQbot μ)) σ (z μ)
      rwa [(hmemZs μ σ).1 hσ, galUnits_eq_smul] at h1
    rw [hpvdiv _ _ _ hpv]
    exact dvd_zero _
  -- the Kummer character of the radicand on the part of inertia the base realization kills
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (μ : ι) → ↥(A μ) → ZMod ℓ, ∀ (μ : ι) (x : ↥(A μ))
      (hx : (x : Gal(Ω/k)) ∈ φ.ker),
      ψ μ x = kummerChar hkd (z μ) (kerGalEquiv hKker ⟨(x : Gal(Ω/k)), hx⟩) :=
    ⟨fun μ x => kummerChar hkd (z μ) (kerGalEquiv hKker ⟨(x : Gal(Ω/k)), hAker μ x.2⟩),
      fun _ _ _ => rfl⟩
  have hψadd : ∀ (μ : ι) (x y : ↥(A μ)), ψ μ (x * y) = ψ μ x + ψ μ y := by
    intro μ x y
    rw [hψ μ (x * y) (hAker μ (x * y).2), hψ μ x (hAker μ x.2), hψ μ y (hAker μ y.2),
      show (⟨((x * y : ↥(A μ)) : Gal(Ω/k)), hAker μ (x * y).2⟩ : ↥φ.ker)
        = ⟨(x : Gal(Ω/k)), hAker μ x.2⟩ * ⟨(y : Gal(Ω/k)), hAker μ y.2⟩ from rfl,
      _root_.map_mul, kummerChar_mul]
  have hunit : ∀ μ : ι, ∃ x₁ : ↥(A μ), IsUnit (ψ μ x₁) := by
    intro μ
    obtain ⟨x₁, hx₁⟩ := exists_isUnit_kummerChar_of_not_dvd_ord
      (v := placeUnder K (Q μ) (hQbot μ)) hKker hkd hℓ (hAeq μ) (hAker μ) (z μ) rfl
      (fun hdvd => hzord μ (by rw [placeValue_eq_neg_ord]; exact dvd_neg.2 hdvd))
    exact ⟨x₁, by rw [hψ μ x₁ (hAker μ x₁.2)]; exact hx₁⟩
  -- an element of that subgroup at which the character takes the value one
  have hnorm : ∀ μ : ι, ∃ x₀ : ↥(A μ), ψ μ x₀ = 1 := by
    intro μ
    obtain ⟨x₁, hx₁⟩ := hunit μ
    refine ⟨x₁ ^ ((ψ μ x₁)⁻¹).val, ?_⟩
    rw [zmodChar_pow (hψadd μ) x₁ _, nsmul_eq_mul, ZMod.natCast_zmod_val,
      inv_mul_cancel₀ (isUnit_iff_ne_zero.1 hx₁)]
  choose x₀ hx₀ using hnorm
  -- the prescribed homomorphism is a multiple of that character, coordinate by coordinate
  have hcycl : ∀ μ : ι, ∃ y₀ : ↥(A μ), ∀ x : ↥(A μ), a μ x ∈ Subgroup.zpowers (a μ y₀) :=
    fun μ => exists_forall_mem_zpowers_of_inertia_inf_ker hKker (hQbot μ) (hQℓ μ) (hAeq μ)
      (layerSub_pow_eq_one ℓ (Generic U N S) j) (a μ) (hasm μ)
  have hdata : ∀ μ : ι, ∃ (e : ↥(A μ) → ZMod ℓ) (m : Fin (layerDim ℓ (Generic U N S) j) → ZMod ℓ),
      (∀ x y : ↥(A μ), e (x * y) = e x + e y) ∧ (∀ x : ↥(A μ), a μ x = 1 → e x = 0) ∧
        ∀ (q : Fin (layerDim ℓ (Generic U N S) j)) (x : ↥(A μ)),
          layerCoord ℓ (Generic U N S) j (a μ x) q = m q * e x :=
    fun μ => exists_zmodChar_forall_eq_smul hℓ prod_layerBasis_pow_layerCoord
      (fun q v v' => layerCoord_mul v v' q) (a μ) (hcycl μ)
  choose e m headd hetriv hcoord using hdata
  have hprop : ∀ μ : ι, ∃ cc : ZMod ℓ, ∀ x : ↥(A μ), e μ x = cc * ψ μ x := by
    intro μ
    obtain ⟨x₁, hx₁⟩ := hunit μ
    obtain ⟨cc, hcc⟩ := exists_forall_eq_mul_kummerChar hKker hkd (hQbot μ) (hQℓ μ) (hAeq μ)
      (hAker μ) (headd μ) (isSmooth₁_of_map_eq_one (hasm μ) (headd μ) (hetriv μ)) (z μ)
      (x₁ := x₁) (by rw [← hψ μ x₁ (hAker μ x₁.2)]; exact hx₁)
    exact ⟨cc, fun x => by rw [hψ μ x (hAker μ x.2)]; exact hcc x⟩
  choose c hc using hprop
  -- every prescribed value is a power of the value at the normalized element
  have haval : ∀ (μ : ι) (x : ↥(A μ)), a μ x = a μ (x₀ μ) ^ (ψ μ x).val := by
    intro μ x
    rw [← prod_layerBasis_pow_layerCoord (a μ x),
      ← prod_layerBasis_pow_layerCoord (a μ (x₀ μ)), ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [← pow_mul]
    refine pow_eq_pow_of_pow_eq_one (layerBasis_pow_eq_one q) ?_
    rw [hcoord μ q x, hcoord μ q (x₀ μ), hc μ x, hc μ (x₀ μ), hx₀ μ, mul_one, Nat.cast_mul,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  -- conjugation by an automorphism fixing the named prime
  have hgw : ∀ (μ : ι) (g : Gal(Ω/k)), g ∈ stabilizer Gal(Ω/k) (Q μ) →
      AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g • placeUnder K (Q μ) (hQbot μ)
        = placeUnder K (Q μ) (hQbot μ) := by
    intro μ g hg
    refine HeightOneSpectrum.ext ?_
    rw [asIdeal_smul_placeUnder K (hQbot μ) g, mem_stabilizer_iff.1 hg, placeUnder_asIdeal]
  have hcA : ∀ (μ : ι) (g : Gal(Ω/k)), g ∈ stabilizer Gal(Ω/k) (Q μ) → ∀ x : ↥(A μ),
      g * ((x : ↥(A μ)) : Gal(Ω/k)) * g⁻¹ ∈ A μ := by
    intro μ g hg x
    have hmem : ((x : ↥(A μ)) : Gal(Ω/k)) ∈ Ideal.inertia Gal(Ω/k) (Q μ) ⊓ φ.ker :=
      (hAeq μ).le x.2
    refine (hAeq μ).ge (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · have hin := mem_inertia_conj (Subgroup.mem_inf.1 hmem).1 g
      rwa [mem_stabilizer_iff.1 hg] at hin
    · refine MonoidHom.mem_ker.2 ?_
      rw [_root_.map_mul, _root_.map_mul, _root_.map_inv,
        MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hmem).2, mul_one, mul_inv_cancel]
  have hψconj : ∀ (μ : ι) (g : Gal(Ω/k)) (hg : g ∈ stabilizer Gal(Ω/k) (Q μ)) (ee : ℕ),
      g • kummerRootUnit Ω hζ = kummerRootUnit Ω hζ ^ ee → ∀ x : ↥(A μ),
      ψ μ ⟨g * ((x : ↥(A μ)) : Gal(Ω/k)) * g⁻¹, hcA μ g hg x⟩ = (ee : ZMod ℓ) * ψ μ x := by
    intro μ g hg ee hee x
    have hxk : ((x : ↥(A μ)) : Gal(Ω/k)) ∈ φ.ker := hAker μ x.2
    have hck : g * ((x : ↥(A μ)) : Gal(Ω/k)) * g⁻¹ ∈ φ.ker := hAker μ (hcA μ g hg x)
    have hτconj : galSubHom K (kerGalEquiv hKker ⟨g * ((x : ↥(A μ)) : Gal(Ω/k)) * g⁻¹, hck⟩)
        = g * galSubHom K (kerGalEquiv hKker ⟨((x : ↥(A μ)) : Gal(Ω/k)), hxk⟩) * g⁻¹ := by
      rw [galSubHom_kerGalEquiv, galSubHom_kerGalEquiv]
    have hinert : kerGalEquiv hKker ⟨g * ((x : ↥(A μ)) : Gal(Ω/k)) * g⁻¹, hck⟩
        ∈ Ideal.inertia Gal(Ω/↥K) (Q μ) := by
      rw [← mem_inertia_galSubHom_iff K, galSubHom_kerGalEquiv]
      have hin := mem_inertia_conj (Subgroup.mem_inf.1 ((hAeq μ).le x.2)).1 g
      rwa [mem_stabilizer_iff.1 hg] at hin
    rw [hψ μ _ hck, hψ μ x hxk,
      ← hconjchar μ _ ((hmemZs μ _).2 (hgw μ g hg)) _ hinert,
      kummerChar_smul_galConj hkd hee (z μ) _, galConj_eq_of_galSubHom_conj K hτconj]
  -- every automorphism of the level fixing the place lifts to one fixing the prime
  have hlift : ∀ (μ : ι) (σ : Gal(↥K/k)), σ ∈ Zs μ →
      ∃ g : Gal(Ω/k), g ∈ stabilizer Gal(Ω/k) (Q μ) ∧
        AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g = σ := by
    intro μ σ hσ
    obtain ⟨ρ, hρ⟩ := restrictNormalHom_surjective_level K σ
    have hbot : ρ • Q μ ≠ ⊥ := by
      intro h0
      exact hQbot μ (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ⁻¹ • I) h0)
    have hpl : placeUnder K (ρ • Q μ) hbot = placeUnder K (Q μ) (hQbot μ) := by
      refine HeightOneSpectrum.ext ?_
      rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot μ) ρ, hρ, (hmemZs μ σ).1 hσ]
    obtain ⟨τ, hτK, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot (hQbot μ) hpl
    have hτker : τ ∈ φ.ker := by
      rw [← hKker]
      exact hτK
    refine ⟨τ * ρ, mem_stabilizer_iff.2 (by rw [mul_smul, ← hτ]), ?_⟩
    rw [_root_.map_mul, (restrictNormalHom_eq_one_iff_mem_ker hKker τ).2 hτker, one_mul, hρ]
  -- the operator group, read on the automorphisms of the level
  obtain ⟨ψU, hψU⟩ := exists_monoidHom_comp_restrictNormalHom (K := Ω) K φ (le_of_eq hKker)
  have hψUinj : Function.Injective ψU := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    obtain ⟨g, rfl⟩ := restrictNormalHom_surjective_level K σ
    refine Subgroup.mem_bot.2 ?_
    refine (restrictNormalHom_eq_one_iff_mem_ker hKker g).2 ?_
    rw [MonoidHom.mem_ker, ← hψU g]
    exact MonoidHom.mem_ker.1 hσ
  -- the prescribed values are twisted along the automorphisms fixing the place
  obtain ⟨V, hV⟩ : ∃ V : ι → ↥(layerSub ℓ (Generic U N S) j), ∀ μ : ι, V μ = a μ (x₀ μ) :=
    ⟨_, fun _ => rfl⟩
  have hVtw : ∀ (μ : ι) (σ : Gal(↥K/k)), σ ∈ Zs μ →
      ψU σ • V μ = V μ ^ ((hζ.autToPow k σ : (ZMod ℓ)ˣ) : ZMod ℓ).val := by
    intro μ σ hσ
    obtain ⟨g, hg, hgres⟩ := hlift μ σ hσ
    obtain ⟨ee, hee⟩ := exists_smul_kummerRootUnit_eq_pow (hζ := hζ) g
    calc ψU σ • V μ
        = φ g • a μ (x₀ μ) := by rw [hV μ, ← hgres, hψU g]
      _ = a μ ⟨g * ((x₀ μ : ↥(A μ)) : Gal(Ω/k)) * g⁻¹, hcA μ g hg (x₀ μ)⟩ :=
          (haequiv μ g (x₀ μ) (hcA μ g hg (x₀ μ))).symm
      _ = a μ (x₀ μ) ^ (ψ μ ⟨g * ((x₀ μ : ↥(A μ)) : Gal(Ω/k)) * g⁻¹,
            hcA μ g hg (x₀ μ)⟩).val := haval μ _
      _ = V μ ^ ((hζ.autToPow k σ : (ZMod ℓ)ˣ) : ZMod ℓ).val := by
          rw [hV μ, hψconj μ g hg ee hee (x₀ μ), hx₀ μ, mul_one,
            natCast_eq_autToPow_of_smul_kummerRootUnit hee, hgres]
  -- the twisted orbit of coefficients the layer supplies
  obtain ⟨β, hβ, hβsurj, b, hbsupp, hbeq, hbnorm⟩ :=
    hN ι Gal(↥K/k) ψU (hζ.autToPow k) Zs V hψUinj hVtw
  have hbpow : ∀ (μ : ι) (σ : Gal(↥K/k)), b μ σ ^ ℓ = 1 :=
    fun μ σ => layerSub_pow_eq_one ℓ (Generic U n S) j (b μ σ)
  -- the homomorphism belonging to each named prime
  obtain ⟨u, hu⟩ : ∃ u : ι → (↥(φ.ker) →* ↥(layerSub ℓ (Generic U n S) j)), ∀ μ : ι,
      u μ = kummerKernelHom hKker hkd (b μ) (hbpow μ) (zz μ) := ⟨_, fun _ => rfl⟩
  -- the prescribed values are reproduced
  have hfive : ∀ (μ : ι) (x : ↥(A μ)) (hx : (x : Gal(Ω/k)) ∈ φ.ker),
      u μ ⟨(x : Gal(Ω/k)), hx⟩ = layerSubMap ℓ β j (a μ x) := by
    intro μ x hx
    have hinert : kerGalEquiv hKker ⟨((x : ↥(A μ)) : Gal(Ω/k)), hx⟩
        ∈ Ideal.inertia Gal(Ω/↥K) (Q μ) := by
      rw [← mem_inertia_galSubHom_iff K, galSubHom_kerGalEquiv]
      exact (Subgroup.mem_inf.1 ((hAeq μ).le x.2)).1
    have hy : ∀ σ : Gal(↥K/k), b μ σ = 1 ∨
        kummerChar hkd (zz μ σ) (kerGalEquiv hKker ⟨((x : ↥(A μ)) : Gal(Ω/k)), hx⟩)
          = ψ μ x := by
      intro σ
      by_cases hσ : σ ∈ Zs μ
      · refine Or.inr ?_
        rw [hzzin μ σ hσ, hconjchar μ σ hσ _ hinert, hψ μ x hx]
      · exact Or.inl (hbsupp μ σ hσ)
    rw [hu μ, kummerKernelHom_eq_prod_pow hKker hkd (b μ) (hbpow μ) (zz μ) hy, ← hbnorm μ, hV μ,
      ← _root_.map_pow, ← haval μ x]
  -- equivariance along the decomposition subgroup of the named prime
  have htwo : ∀ (μ : ι) (g : Gal(Ω/k)), g ∈ stabilizer Gal(Ω/k) (Q μ) →
      ∀ (y : ↥(φ.ker)) (hy : g * (y : Gal(Ω/k)) * g⁻¹ ∈ φ.ker),
        u μ ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩ = φ g • u μ y := by
    intro μ g hg y hy
    obtain ⟨ee, hee⟩ := exists_smul_kummerRootUnit_eq_pow (hζ := hζ) g
    have hgZ : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g ∈ Zs μ :=
      (hmemZs μ _).2 (hgw μ g hg)
    obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm Gal(↥K/k), ∀ σ : Gal(↥K/k),
        π σ = (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g)⁻¹ * σ :=
      ⟨⟨fun σ => (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g)⁻¹ * σ,
        fun σ => AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g * σ,
        fun σ => mul_inv_cancel_left _ _, fun σ => inv_mul_cancel_left _ _⟩, fun _ => rfl⟩
    have hf : ∀ x : ↥(layerSub ℓ (Generic U n S) j),
        MulDistribMulAction.toMonoidHom (↥(layerSub ℓ (Generic U n S) j)) (φ g) x = φ g • x :=
      fun _ => rfl
    have hzperm : ∀ σ : Gal(↥K/k), ∃ s : (↥K)ˣ,
        AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g • zz μ (π σ) = zz μ σ * s ^ ℓ := by
      intro σ
      refine ⟨1, ?_⟩
      rw [one_pow, mul_one, hπ σ]
      by_cases hσ : σ ∈ Zs μ
      · have hmem : (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g)⁻¹ * σ ∈ Zs μ :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ hgZ) hσ
        rw [hzzin μ _ hmem, hzzin μ σ hσ, smul_smul, mul_inv_cancel_left]
      · have hnot : (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g)⁻¹ * σ ∉ Zs μ := by
          intro hmem
          have hm := Subgroup.mul_mem _ hgZ hmem
          rw [mul_inv_cancel_left] at hm
          exact hσ hm
        rw [hzzout μ _ hnot, hzzout μ σ hσ, smul_one]
    have hbperm : ∀ σ : Gal(↥K/k), b μ σ ^ ee
        = MulDistribMulAction.toMonoidHom (↥(layerSub ℓ (Generic U n S) j)) (φ g)
            (b μ (π σ)) := by
      intro σ
      rw [hf, hπ σ, ← hψU g, ← hbeq μ σ _ hgZ]
      refine pow_eq_pow_of_pow_eq_one (hbpow μ σ) ?_
      rw [ZMod.natCast_zmod_val]
      exact natCast_eq_autToPow_of_smul_kummerRootUnit hee
    rw [hu μ, kummerKernelHom_conj_of_perm hKker hkd (b μ) (hbpow μ) (zz μ) hee π
      (MulDistribMulAction.toMonoidHom (↥(layerSub ℓ (Generic U n S) j)) (φ g)) hzperm hbperm
      y hy, hf]
  refine ⟨β, hβ, hβsurj, u, ?_, htwo, ?_, ?_, hfive, ?_, ?_⟩
  · obtain ⟨W, hW, hWu⟩ := exists_isOpenNormal_forall_kummerKernelHom_eq_one hKker hkd b hbpow zz
    exact ⟨W, hW, fun μ y hy => by rw [hu μ]; exact hWu μ y hy⟩
  · intro μ ν ρ y hy
    haveI : (ρ⁻¹ • Pr ν).IsPrime := inferInstance
    rw [hu μ]
    exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd (b μ) (hbpow μ) (zz μ)
      (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ⁻¹ • placeUnder K (Pr ν) (hPrbot ν))
      (asIdeal_smul_placeUnder K (hPrbot ν) ρ⁻¹)
      (fun σ => hzzone μ σ _ fun _ =>
        hlccong _ _ _ (mul_smul _ _ _) (hzT μ _ (hmemTz _ ν)))
      (mem_stabilizer_smul_iff.2 (by rw [inv_inv, ← hDPr ν]; exact hy))
  · intro μ ν hνμ ρ y hy
    haveI : (ρ⁻¹ • Q ν).IsPrime := inferInstance
    rw [hu μ]
    exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd (b μ) (hbpow μ) (zz μ)
      (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ⁻¹ • placeUnder K (Q ν) (hQbot ν))
      (asIdeal_smul_placeUnder K (hQbot ν) ρ⁻¹)
      (fun σ => hzzone μ σ _ fun _ =>
        hlccong _ _ _ (mul_smul _ _ _) (hzother μ ν hνμ _))
      (mem_stabilizer_smul_iff.2 (by rw [inv_inv]; exact hAstab ν hy))
  · intro μ ρ hρ y hy
    haveI : (ρ • Q μ).IsPrime := inferInstance
    have hne : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ •
        placeUnder K (Q μ) (hQbot μ) ≠ placeUnder K (Q μ) (hQbot μ) := by
      intro heq
      have hbot : ρ • Q μ ≠ ⊥ := by
        intro h0
        exact hQbot μ (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ⁻¹ • I) h0)
      have hpl : placeUnder K (ρ • Q μ) hbot = placeUnder K (Q μ) (hQbot μ) := by
        refine HeightOneSpectrum.ext ?_
        rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot μ) ρ, heq]
      obtain ⟨τ, hτK, hτ⟩ :=
        exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot (hQbot μ) hpl
      refine hρ (τ * ρ) (mem_stabilizer_iff.2 (by rw [mul_smul, ← hτ])) ?_
      have hτker : τ ∈ φ.ker := by
        rw [← hKker]
        exact hτK
      rw [_root_.map_mul, MonoidHom.mem_ker.1 hτker, one_mul]
    rw [hu μ]
    exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd (b μ) (hbpow μ) (zz μ)
      (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ • placeUnder K (Q μ) (hQbot μ))
      (asIdeal_smul_placeUnder K (hQbot μ) ρ)
      (fun σ => hzzconj μ σ _ hne) hy
  · rintro μ P hPp hPbot ⟨y, hyI, hyne⟩
    haveI := hPp
    rw [hu μ] at hyne
    have hpz : ∀ (σ' : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)), (ℓ : 𝓞 ↥K) ∈ v.asIdeal →
        localClassHom v ℓ (zz μ σ') = 1 := by
      intro σ' v hv
      refine hzzone μ σ' v fun _ => ?_
      obtain ⟨τ, ν, hτν⟩ := hℓPr v hv
      subst hτν
      exact hlccong _ _ _ (mul_smul _ _ _) (hzT μ _ (hmemTz _ ν))
    obtain ⟨σ, hσdvd⟩ := exists_not_dvd_placeValue_of_kummerKernelHom_ne_one (P := P) hKker hkd
      (b μ) (hbpow μ) (zz μ) hℓ hPbot hpz hyI hyne
    by_cases hσZ : σ ∈ Zs μ
    · have hpv : placeValue (placeUnder K P hPbot) (zz μ σ)
          = placeValue (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K 1 • σ⁻¹ •
              placeUnder K P hPbot) (z μ) := by
        rw [_root_.map_one, one_smul, hzzin μ σ hσZ]
        have h1 := placeValue_galSmul (σ⁻¹ • placeUnder K P hPbot) σ (z μ)
        rw [smul_inv_smul, galUnits_eq_smul] at h1
        exact h1
      rw [hpv, _root_.map_one, one_smul] at hσdvd
      rcases hzram μ (σ⁻¹ • placeUnder K P hPbot) hσdvd with ⟨ν, ρ₂, hvρ⟩ | hsplit
      · have hvρ' : placeUnder K P hPbot = (σ * ρ₂) • placeUnder K (Q ν) (hQbot ν) := by
          rw [mul_smul, ← hvρ, smul_inv_smul]
        obtain ⟨ρ, hρ⟩ := restrictNormalHom_surjective_level K (σ * ρ₂)
        have hbot : ρ • Q ν ≠ ⊥ := by
          intro h0
          exact hQbot ν (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ⁻¹ • I) h0)
        have hpl : placeUnder K (ρ • Q ν) hbot = placeUnder K P hPbot := by
          refine HeightOneSpectrum.ext ?_
          rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot ν) ρ, hρ, ← hvρ']
        obtain ⟨τ, -, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot hPbot hpl
        exact Or.inl ⟨ν, τ * ρ, by rw [mul_smul]; exact hτ⟩
      · refine Or.inr fun x hx => ?_
        obtain ⟨ρ₁, hρ₁⟩ := restrictNormalHom_surjective_level K σ
        haveI : (ρ₁⁻¹ • P).IsPrime := inferInstance
        have hbot : ρ₁⁻¹ • P ≠ ⊥ := by
          intro h0
          exact hPbot (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ₁ • I) h0)
        have hund : Ideal.under (𝓞 ↥K) (ρ₁⁻¹ • P) = (σ⁻¹ • placeUnder K P hPbot).asIdeal := by
          rw [← asIdeal_smul_placeUnder K hPbot ρ₁⁻¹, _root_.map_inv, hρ₁]
        have hxc : ρ₁⁻¹ * x * ρ₁ ∈ stabilizer Gal(Ω/k) (ρ₁⁻¹ • P) :=
          mem_stabilizer_smul_iff.2 (by
            rw [inv_inv, show ρ₁ * (ρ₁⁻¹ * x * ρ₁) * ρ₁⁻¹ = x by group]
            exact hx)
        have hxE : x ∈ E.fixingSubgroup := by
          have hc := (normal_fixingSubgroup E).conj_mem _
            (hsplit (ρ₁⁻¹ • P) inferInstance hbot hund hxc) ρ₁
          rwa [show ρ₁ * (ρ₁⁻¹ * x * ρ₁) * ρ₁⁻¹ = x by group] at hc
        rw [MonoidHom.mem_ker.1 (hEF hxE), _root_.map_one]
    · exact absurd (hzzout μ σ hσZ ▸ hpvone (placeUnder K P hPbot) ▸ dvd_zero (ℓ : ℤ)) hσdvd

end Places

end InverseGalois.Shafarevich

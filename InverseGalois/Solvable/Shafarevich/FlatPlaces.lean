/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceSubcyclotomic
import InverseGalois.CFT.PoitouTate.SUnitReduce
import InverseGalois.Solvable.Shafarevich.FlatCyclic
import InverseGalois.Solvable.Shafarevich.KernelClauses
import InverseGalois.Solvable.Shafarevich.LevelFlatOrbit

/-!
# The flat prescription bought from one unit at each named place

The prescription made at a single named prime is a homomorphism of the part of inertia there which
the base realization kills, and that part of inertia is carried by one element modulo an open
subgroup.  So a single unit of the level suffices to carry it: a unit whose order at the place below
is prime to the exponent has a Kummer character taking a unit value on that subgroup, the
coordinates of the prescribed homomorphism are multiples of that character, and the powers of the
one unit by those multipliers assemble into exactly the prescribed homomorphism.

That is what makes the flat prescription cheaper than the sharp one.  The sharp prescription names a
class at each named place in each coordinate, and the reciprocity law then has something to say
about the naming: the product of the power residue symbols of a global unit against the named
classes vanishes over all the places at once, which leaves a pairing condition behind.  Here nothing
is named but a single unit, and the Kummer character of a unit on inertia at a place away from the
exponent depends on the unit only through its order there.  Any unit of order prime to the exponent
will do, the coordinates absorbing the rest, so no pairing condition is left over.

The equivariance the flat prescription asks for is equivariance for the decomposition subgroup of
the named prime alone, and that is bought by asking the unit to be fixed, up to an exponent-th
power, by the automorphisms of the level fixing the place below — everything depending on the unit
only through its class modulo exponent-th powers.  An automorphism raises the chosen roots of unity
to some power, and multiplies the Kummer character of a unit it fixes in that sense by that power;
the prescribed value is therefore carried to its own power by that same exponent, which is what the
prescription at the conjugated argument asks for.

## Main definitions

* `InverseGalois.Shafarevich.HasFlatPrescribedUnits` — **a unit of a level can be found for each of
  finitely many places lying in distinct orbits, fixed by the automorphisms fixing its place, of
  order there prime to the exponent, a local power at a prescribed finite set of places those avoid
  and at every proper conjugate of its own place and at every conjugate of the others, and confined
  elsewhere to places sitting over the named ones or completely decomposed in a given finite
  level.**

## Main results

* `InverseGalois.Shafarevich.hasFlatOrbitPrescription_of_places` — **a level carrying such units
  carries the flat prescription read one named prime at a time.**

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, decomposition group, local class
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

/-! ### The arithmetic input -/

section Units

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **A unit of a level can be found for each of finitely many places lying in distinct orbits,
fixed by the automorphisms fixing its place, of order there prime to the exponent, a local power at
a prescribed finite set of places those avoid and at every proper conjugate of its own place and at
every conjugate of the others, and confined elsewhere to places sitting over the named ones or
completely decomposed in a given finite level.**

The places are named by an arbitrary finite index type and are asked to lie in distinct orbits under
the automorphisms of the level; nothing is asked of the orbit of a single one of them, which is the
whole difference from the demand the prescription over the base field makes.  A place may therefore
be moved by the automorphisms of the level, and what is asked of the unit belonging to it is only
that those automorphisms which fix the place itself fix the unit up to an exponent-th power, the
whole demand depending on the unit only through its class modulo exponent-th powers.

One unit is asked for at each named place rather than one class in each coordinate, and the only
thing asked of it at its own place is that its order there be prime to the exponent.  That is what
the prescription needs and all it needs: the Kummer character of a unit on inertia at a place away
from the exponent is read off that order, so the coordinates of any prescribed homomorphism are
multiples of the character of any such unit.

The remaining clauses are the local shape of the prescription.  The finite set of places the unit is
asked to be a local power at is prescribed along with the named places and avoided by them, so that
the two demands do not collide; the places above the exponent are covered by that set, which is what
makes the assembled homomorphism unramified there.  The unit is also asked to be a local power at
the proper conjugates of its own place and at every conjugate of the other named places, which is
what lets the prescriptions made at the several named primes be multiplied without disturbing one
another.  Elsewhere the unit is confined: at any place where its order is not divisible by the
exponent it sits over a named place, or the primes above it are completely decomposed in a finite
level named in advance. -/
def HasFlatPrescribedUnits (ℓ : ℕ) [NeZero ℓ] (K : IntermediateField k Ω) [NumberField ↥K] :
    Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ (ι : Type) [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K)),
      (∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν) →
      ∀ Tz : Finset (HeightOneSpectrum (𝓞 ↥K)), (∀ μ : ι, w μ ∉ Tz) →
        (∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal) →
        ∃ Z : ι → (↥K)ˣ,
          (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ = w μ → ∃ y : (↥K)ˣ, σ • Z μ = Z μ * y ^ ℓ) ∧
          (∀ μ : ι, ¬ (ℓ : ℤ) ∣ placeValue (w μ) (Z μ)) ∧
          (∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → localClassHom v ℓ (Z μ) = 1) ∧
          (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ≠ w μ → localClassHom (σ • w μ) ℓ (Z μ) = 1) ∧
          (∀ μ ν : ι, ν ≠ μ → ∀ σ : Gal(↥K/k), localClassHom (σ • w ν) ℓ (Z μ) = 1) ∧
          ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), ¬ (ℓ : ℤ) ∣ placeValue v (Z μ) →
            (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
              ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
                stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup

end Units

/-! ### The level killing the lift -/

section Level

variable {ℓ : ℕ} {U : Type} [Group U] {m n : ℕ} {S : Type} [Group S] {j : ℕ} {k Ω : Type}
  [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {φ : Gal(Ω/k) →* U}

/-- **A finite level over a given one killing a lift carried across a shrinking.**

A smooth homomorphism onto a discrete group has open kernel, and the kernel of the lift carried
across the shrinking is larger still, so a finite Galois level cuts it out exactly.  That level
contains the level the base realization cuts out because the lift lies over the base realization:
an element killing the lift kills the base realization, so it fixes the level below. -/
theorem exists_level_ker_le {β : Generic U m S →* Generic U n S} (hβ : IsOperatorHom β)
    (K : IntermediateField k Ω) (hKker : K.fixingSubgroup = φ.ker)
    (F : Gal(Ω/k) →* GenericQuot ℓ U m S (j + 1)) (hFsm : IsSmoothHom F)
    (hFright : ∀ x, SemidirectProduct.rightHom (F x) = φ x) :
    ∃ E : IntermediateField k Ω, FiniteDimensional k ↥E ∧ IsGalois k ↥E ∧ K ≤ E ∧
      E.fixingSubgroup ≤ ((layerSemidirectMap ℓ hβ (j + 1)).comp F).ker := by
  have hle : F.ker ≤ ((layerSemidirectMap ℓ hβ (j + 1)).comp F).ker := by
    intro x hx
    refine MonoidHom.mem_ker.2 ?_
    show layerSemidirectMap ℓ hβ (j + 1) (F x) = 1
    rw [MonoidHom.mem_ker.1 hx, _root_.map_one]
  obtain ⟨E, hEfin, hEgal, hEfix, hEmem⟩ :=
    exists_level_fixingSubgroup_eq (N := ((layerSemidirectMap ℓ hβ (j + 1)).comp F).ker)
      ⟨inferInstance, Subgroup.isOpen_mono hle (isOpenNormal_ker_of_isSmoothHom hFsm).isOpen⟩
  have hkerφ : ((layerSemidirectMap ℓ hβ (j + 1)).comp F).ker ≤ φ.ker := by
    intro x hx
    have hx1 : layerSemidirectMap ℓ hβ (j + 1) (F x) = 1 := MonoidHom.mem_ker.1 hx
    have h2 : (layerSemidirectMap ℓ hβ (j + 1) (F x)).right = φ x := hFright x
    rw [hx1] at h2
    exact MonoidHom.mem_ker.2 h2.symm
  refine ⟨E, hEfin, hEgal, fun x hx => hEmem x fun σ hσ => ?_, le_of_eq hEfix⟩
  have hσK : σ ∈ K.fixingSubgroup := by
    rw [hKker]
    exact hkerφ hσ
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσK x hx

end Level

/-! ### The prescription -/

section Places

variable {ℓ : ℕ} [Fact ℓ.Prime] [NeZero ℓ] {U : Type} [Group U] [Finite U] {n : ℕ} {S : Type}
  [Group S] [Finite S] {j : ℕ} {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] {φ : Gal(Ω/k) →* U} {t : ℕ} {D : Fin t → Subgroup Gal(Ω/k)}

attribute [local instance] genericQuotAction zmodTrivialAction

omit [NumberField k] in
/-- **A level carrying units prescribed at named places carries the flat prescription read one named
prime at a time.**

A basis of the layer is named, and the homomorphism belonging to a named prime is assembled out of
the powers of the one unit belonging to that prime, the exponents being the coordinates the
prescription forces.  Those coordinates exist because the prescribed homomorphism is a smooth
homomorphism of the part of inertia which the base realization kills, and the Kummer character of
the unit takes a unit value there, the order of the unit at the place below being prime to the
exponent.

Each clause is then read off the unit.  Equivariance for the decomposition subgroup of the named
prime holds because the automorphisms of the level fixing the place below fix the unit up to an
exponent-th power: the Kummer character is multiplied by the power to which that element raises the
roots of
unity, and the prescribed value is raised to that same power, which is exactly what the prescription
at the conjugated argument asks.  Triviality along the finite family and along the subgroups
belonging to the other named primes is triviality of the local classes at the corresponding places,
and triviality on the decomposition subgroups of the proper conjugates of the named prime is
triviality at the proper conjugates of the place below — the conjugates the prescription leaves
alone being exactly those the base realization cannot separate, which are those fixing the place.
Where the assembled homomorphism ramifies the unit has order not divisible by the exponent at the
place below, and the confinement clause then says the prime is a conjugate of a named one — two
primes with the same place below differing by an automorphism of the level — or that its place is
completely decomposed in a finite level killing the given lift, whence the whole decomposition
subgroup dies there.

The set of places the unit is asked to be a local power at is the orbit of the places below the
given finite family of decomposition subgroups; the named places avoid it because no named prime
sits under that family, and the places above the exponent are among it, which is what makes the
assembled homomorphism unramified there.  The finite level the leftover places are asked to be
decomposed in comes with the shrinking, and is asked to kill the given lift carried down. -/
theorem hasFlatOrbitPrescription_of_places (N : ℕ) (K : IntermediateField k Ω)
    [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hkd : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)
    {Pr : Fin t → Ideal (𝓞 Ω)} (hPrp : ∀ ν, (Pr ν).IsPrime) (hPrbot : ∀ ν, Pr ν ≠ ⊥)
    (hDPr : ∀ ν, D ν = stabilizer Gal(Ω/k) (Pr ν))
    (hℓPr : ∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : 𝓞 ↥K) ∈ v.asIdeal →
      ∃ (σ : Gal(↥K/k)) (ν : Fin t), v = σ • placeUnder K (Pr ν) (hPrbot ν))
    (hlevel : ∀ F : Gal(Ω/k) →* GenericQuot ℓ U N S (j + 1), Function.Surjective F →
      IsSmoothHom F → (∀ x, SemidirectProduct.rightHom (F x) = φ x) →
      ∃ (β : Generic U N S →* Generic U n S) (hβ : IsOperatorHom β), Function.Surjective β ∧
        ∃ E : IntermediateField k Ω, FiniteDimensional k ↥E ∧ IsGalois k ↥E ∧ K ≤ E ∧
          E.fixingSubgroup ≤ ((layerSemidirectMap ℓ hβ (j + 1)).comp F).ker)
    (hfam : HasFlatPrescribedUnits ℓ K) :
    HasFlatOrbitPrescription ℓ U n S j φ D := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  haveI : IsGalois ↥K Ω := IsGalois.tower_top_of_isGalois k ↥K Ω
  refine ⟨N, ?_⟩
  intro F ι _ Q A a hFsurj hFsm hFright hQp hQbot hQℓ hQconj hAstab hAker hAeq _ hasm haequiv hesc
  haveI : ∀ μ, (Q μ).IsPrime := hQp
  haveI : ∀ ν, (Pr ν).IsPrime := hPrp
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨β, hβ, hβsurj, E, hEfin, hEgal, hKE, hEF⟩ := hlevel F hFsurj hFsm hFright
  haveI := hEfin
  haveI := hEgal
  -- the named primes lie in distinct orbits, so their places below are moved off one another
  have hconjw : ∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k),
      σ • placeUnder K (Q μ) (hQbot μ) ≠ placeUnder K (Q ν) (hQbot ν) := by
    intro μ ν hμν σ heq
    obtain ⟨ρ₀, hρ₀⟩ := restrictNormalHom_surjective_level K σ
    have hbot : ρ₀ • Q μ ≠ ⊥ := by
      intro h0
      exact hQbot μ (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ₀⁻¹ • I) h0)
    have hpl : placeUnder K (ρ₀ • Q μ) hbot = placeUnder K (Q ν) (hQbot ν) := by
      refine HeightOneSpectrum.ext ?_
      rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot μ) ρ₀, hρ₀, heq]
    obtain ⟨τ, -, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot (hQbot ν) hpl
    exact hQconj μ ν hμν (τ * ρ₀) (by rw [mul_smul]; exact hτ)
  -- an element fixing a named prime fixes the place below it
  have hfix : ∀ (μ : ι) (g : Gal(Ω/k)), g ∈ stabilizer Gal(Ω/k) (Q μ) →
      AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g • placeUnder K (Q μ) (hQbot μ)
        = placeUnder K (Q μ) (hQbot μ) := by
    intro μ g hg
    refine HeightOneSpectrum.ext ?_
    rw [asIdeal_smul_placeUnder K (hQbot μ) g, mem_stabilizer_iff.1 hg, placeUnder_asIdeal]
  -- an element the base realization separates from the decomposition subgroup moves the place
  have hne : ∀ (μ : ι) (ρ : Gal(Ω/k)), (∀ s ∈ stabilizer Gal(Ω/k) (Q μ), φ s ≠ φ ρ) →
      AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ • placeUnder K (Q μ) (hQbot μ)
        ≠ placeUnder K (Q μ) (hQbot μ) := by
    intro μ ρ hρ heq
    have hbot : ρ • Q μ ≠ ⊥ := by
      intro h0
      exact hQbot μ (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ⁻¹ • I) h0)
    have hpl : placeUnder K (ρ • Q μ) hbot = placeUnder K (Q μ) (hQbot μ) := by
      refine HeightOneSpectrum.ext ?_
      rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot μ) ρ, heq]
    obtain ⟨τ, hτmem, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot (hQbot μ) hpl
    have hτker : τ ∈ φ.ker := by rw [← hKker]; exact hτmem
    refine hρ (τ * ρ) (mem_stabilizer_iff.2 (by rw [mul_smul]; exact hτ.symm)) ?_
    rw [_root_.map_mul, MonoidHom.mem_ker.1 hτker, one_mul]
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
    obtain ⟨y, hy, hyn⟩ := hesc μ ν (τ * ρ₀)⁻¹
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
  -- the units the arithmetic supplies
  obtain ⟨Z, hZinv, hZord, hZT, hZconj, hZother, hZconf⟩ := hfam E hEfin hEgal hKE ι
    (fun μ => placeUnder K (Q μ) (hQbot μ)) hconjw Tz hdisj hdisjℓ
  -- the coordinates the prescription forces
  have hasm' : ∀ μ : ι, IsSmooth₁
      (((layerSubMap ℓ β j).comp (a μ) : ↥(A μ) →* ↥(layerSub ℓ (Generic U n S) j)) :
        ↥(A μ) → ↥(layerSub ℓ (Generic U n S) j)) := by
    intro μ
    obtain ⟨N₀, hN₀, hcon⟩ := hasm μ
    exact ⟨N₀, hN₀, fun x y hy => congrArg (layerSubMap ℓ β j) (hcon x y hy)⟩
  have hunit : ∀ μ : ι, ∃ x₁ : ↥(A μ), IsUnit (subKummerChar hKker hkd (hAker μ) (Z μ) x₁) := by
    intro μ
    have hord : ¬ (ℓ : ℤ) ∣ Rigidity.RET.ord ↥K (placeUnder K (Q μ) (hQbot μ)) ((Z μ : ↥K)) := by
      intro hd
      refine hZord μ ?_
      rw [placeValue_eq_neg_ord]
      exact dvd_neg.2 hd
    exact exists_isUnit_kummerChar_of_not_dvd_ord hKker hkd hℓ (hAeq μ) (hAker μ) (Z μ)
      (v := placeUnder K (Q μ) (hQbot μ)) rfl hord
  have hcoord : ∀ μ : ι, ∃ c : Fin (layerDim ℓ (Generic U n S) j) → ZMod ℓ, ∀ x : ↥(A μ),
      ((layerSubMap ℓ β j).comp (a μ)) x
        = (∏ q, layerBasis ℓ (Generic U n S) j q ^ (c q).val)
            ^ (subKummerChar hKker hkd (hAker μ) (Z μ) x).val := by
    intro μ
    obtain ⟨x₁, hx₁⟩ := hunit μ
    exact exists_forall_eq_pow_subKummerChar hKker hkd (hQbot μ) (hQℓ μ) (hAeq μ) (hAker μ)
      layerBasis_pow_eq_one (χ := fun q e => layerCoord ℓ (Generic U n S) j e q)
      prod_layerBasis_pow_layerCoord (fun q e e' => layerCoord_mul e e' q)
      ((layerSubMap ℓ β j).comp (a μ)) (hasm' μ) (Z μ) hx₁
  choose c hc using hcoord
  have hVpow : ∀ μ : ι,
      (∏ q, layerBasis ℓ (Generic U n S) j q ^ (c μ q).val) ^ ℓ = 1 :=
    fun _ => prod_pow_pow_eq_one layerBasis_pow_eq_one _
  have hx₀ : ∀ μ : ι, ∃ x₀ : ↥(A μ), subKummerChar hKker hkd (hAker μ) (Z μ) x₀ = 1 := by
    intro μ
    obtain ⟨x₁, hx₁⟩ := hunit μ
    exact exists_subKummerChar_eq_one hKker hkd (hAker μ) (Z μ) hx₁
  have hAI : ∀ ν : ι, A ν ≤ Ideal.inertia Gal(Ω/k) (Q ν) :=
    fun ν => (hAeq ν).le.trans inf_le_left
  have hAmem : ∀ (ν : ι) (z : Gal(Ω/k)),
      z ∈ Ideal.inertia Gal(Ω/k) (Q ν) → z ∈ φ.ker → z ∈ A ν := by
    intro ν z h1 h2
    rw [hAeq ν]
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  -- the prescribed value is raised to the power by which the conjugating element moves the roots
  have hVsmul : ∀ (μ : ι) (g : Gal(Ω/k)), g ∈ stabilizer Gal(Ω/k) (Q μ) → ∀ e : ℕ,
      g • kummerRootUnit Ω hζ = kummerRootUnit Ω hζ ^ e →
      (∏ q, layerBasis ℓ (Generic U n S) j q ^ (c μ q).val) ^ e
        = φ g • ∏ q, layerBasis ℓ (Generic U n S) j q ^ (c μ q).val := by
    intro μ g hg e hge
    obtain ⟨x₀, hx₀1⟩ := hx₀ μ
    have hx₀I : (x₀ : Gal(Ω/k)) ∈ Ideal.inertia Gal(Ω/k) (Q μ) := hAI μ x₀.2
    have hconjmem : g * (x₀ : Gal(Ω/k)) * g⁻¹ ∈ A μ := by
      refine hAmem μ _ ?_ ?_
      · have h1 := mem_inertia_conj hx₀I g
        rwa [mem_stabilizer_iff.1 hg] at h1
      · have h2 : (x₀ : Gal(Ω/k)) ∈ φ.ker := hAker μ x₀.2
        rw [MonoidHom.mem_ker] at h2 ⊢
        rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, h2, mul_one, mul_inv_cancel]
    have hτ : galSubHom K (kerGalEquiv hKker ⟨g * (x₀ : Gal(Ω/k)) * g⁻¹, hAker μ hconjmem⟩)
        = g * galSubHom K (kerGalEquiv hKker ⟨(x₀ : Gal(Ω/k)), hAker μ x₀.2⟩) * g⁻¹ := by
      rw [galSubHom_kerGalEquiv, galSubHom_kerGalEquiv]
    obtain ⟨yg, hZ'⟩ := hZinv μ _ (hfix μ g hg)
    have hsub : subKummerChar hKker hkd (hAker μ) (Z μ) ⟨g * (x₀ : Gal(Ω/k)) * g⁻¹, hconjmem⟩
        = (e : ZMod ℓ) := by
      simp only [subKummerChar] at hx₀1 ⊢
      rw [kummerChar_conj_of_smul_eq_mul_pow hkd hge hZ' hτ, hx₀1, mul_one]
    have hleft : layerSubMap ℓ β j (a μ ⟨g * (x₀ : Gal(Ω/k)) * g⁻¹, hconjmem⟩)
        = φ g • layerSubMap ℓ β j (a μ x₀) := by
      rw [haequiv μ g x₀ hconjmem, layerSubMap_smul hβ]
    have hright : layerSubMap ℓ β j (a μ x₀)
        = ∏ q, layerBasis ℓ (Generic U n S) j q ^ (c μ q).val := by
      have hx := hc μ x₀
      rw [hx₀1, ZMod.val_one, pow_one] at hx
      exact hx
    have hleft' : layerSubMap ℓ β j (a μ ⟨g * (x₀ : Gal(Ω/k)) * g⁻¹, hconjmem⟩)
        = (∏ q, layerBasis ℓ (Generic U n S) j q ^ (c μ q).val) ^ (e : ZMod ℓ).val := by
      have hx := hc μ ⟨g * (x₀ : Gal(Ω/k)) * g⁻¹, hconjmem⟩
      rw [hsub] at hx
      exact hx
    have hkey : (∏ q, layerBasis ℓ (Generic U n S) j q ^ (c μ q).val) ^ (e : ZMod ℓ).val
        = φ g • ∏ q, layerBasis ℓ (Generic U n S) j q ^ (c μ q).val := by
      rw [← hleft', hleft, hright]
    rw [← hkey]
    exact pow_eq_pow_of_pow_eq_one (hVpow μ) (ZMod.natCast_zmod_val _).symm
  -- the local classes of the powers of a unit
  have hpow1 : ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), localClassHom v ℓ (Z μ) = 1 →
      ∀ q, localClassHom v ℓ (Z μ ^ (c μ q).val) = 1 := by
    intro μ v hv q
    rw [_root_.map_pow, hv, one_pow]
  have hz1 : ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), (ℓ : 𝓞 ↥K) ∈ v.asIdeal →
      localClassHom v ℓ (Z μ) = 1 := by
    intro μ v hv
    obtain ⟨σ, ν, rfl⟩ := hℓPr v hv
    exact hZT μ _ (hmemTz σ ν)
  refine ⟨β, hβ, hβsurj,
    fun μ => kummerKernelHom hKker hkd (layerBasis ℓ (Generic U n S) j) layerBasis_pow_eq_one
      (fun q => Z μ ^ (c μ q).val), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exists_isOpenNormal_forall_kummerKernelHom_eq_one hKker hkd
      (fun _ : ι => layerBasis ℓ (Generic U n S) j) (fun _ q => layerBasis_pow_eq_one q)
      (fun μ q => Z μ ^ (c μ q).val)
  · intro μ g hg y hy
    obtain ⟨e, hge⟩ := exists_smul_kummerRootUnit_eq_pow (hζ := hζ) g
    obtain ⟨yg, hyg⟩ := hZinv μ _ (hfix μ g hg)
    exact kummerKernelHom_conj_of_pow hKker hkd (layerBasis ℓ (Generic U n S) j)
      layerBasis_pow_eq_one (Z μ) (c μ) hge hyg
      (MulDistribMulAction.toMonoidHom ↥(layerSub ℓ (Generic U n S) j) (φ g))
      (hVsmul μ g hg e hge) y hy
  · intro μ ν ρ y hyD
    haveI : (ρ⁻¹ • Pr ν).IsPrime := inferInstance
    exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd (layerBasis ℓ (Generic U n S) j)
      layerBasis_pow_eq_one (fun q => Z μ ^ (c μ q).val)
      (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ⁻¹ • placeUnder K (Pr ν) (hPrbot ν))
      (asIdeal_smul_placeUnder K (hPrbot ν) ρ⁻¹)
      (fun q => hpow1 μ _ (hZT μ _ (hmemTz _ ν)) q)
      (mem_stabilizer_smul_iff.2 (by rw [inv_inv, ← hDPr ν]; exact hyD))
  · intro μ ν hνμ ρ y hyA
    haveI : (ρ⁻¹ • Q ν).IsPrime := inferInstance
    refine kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd (layerBasis ℓ (Generic U n S) j)
      layerBasis_pow_eq_one (fun q => Z μ ^ (c μ q).val)
      (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ⁻¹ • placeUnder K (Q ν) (hQbot ν))
      (asIdeal_smul_placeUnder K (hQbot ν) ρ⁻¹)
      (fun q => hpow1 μ _ (hZother μ ν hνμ _) q) (mem_stabilizer_smul_iff.2 ?_)
    rw [inv_inv]
    exact hAstab ν hyA
  · intro μ x hx
    rw [kummerKernelHom_eq_pow hKker hkd (layerBasis ℓ (Generic U n S) j) layerBasis_pow_eq_one
      (Z μ) (c μ)]
    exact (hc μ x).symm
  · intro μ ρ hρ y hy
    haveI : (ρ • Q μ).IsPrime := inferInstance
    exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd (layerBasis ℓ (Generic U n S) j)
      layerBasis_pow_eq_one (fun q => Z μ ^ (c μ q).val)
      (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ • placeUnder K (Q μ) (hQbot μ))
      (asIdeal_smul_placeUnder K (hQbot μ) ρ)
      (fun q => hpow1 μ _ (hZconj μ _ (hne μ ρ hρ)) q) hy
  · rintro μ P hPp hPbot ⟨y, hyI, hyne⟩
    haveI := hPp
    obtain ⟨q, hq⟩ := exists_not_dvd_placeValue_of_kummerKernelHom_ne_one hKker hkd
      (layerBasis ℓ (Generic U n S) j) layerBasis_pow_eq_one (fun q => Z μ ^ (c μ q).val) hℓ hPbot
      (fun q v hv => hpow1 μ v (hz1 μ v hv) q) hyI hyne
    have hq' : ¬ (ℓ : ℤ) ∣ placeValue (placeUnder K P hPbot) (Z μ) := by
      intro hd
      refine hq ?_
      show (ℓ : ℤ) ∣ placeValue (placeUnder K P hPbot) (Z μ ^ (c μ q).val)
      rw [placeValue_pow]
      exact hd.mul_left _
    rcases hZconf μ (placeUnder K P hPbot) hq' with ⟨ν, σ, hvσ⟩ | hsplit
    · obtain ⟨ρ, hρ⟩ := restrictNormalHom_surjective_level K σ
      have hbot : ρ • Q ν ≠ ⊥ := by
        intro h0
        exact hQbot ν (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ⁻¹ • I) h0)
      have hpl : placeUnder K (ρ • Q ν) hbot = placeUnder K P hPbot := by
        refine HeightOneSpectrum.ext ?_
        rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot ν) ρ, hρ, ← hvσ]
      obtain ⟨τ, -, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot hPbot hpl
      exact Or.inl ⟨ν, τ * ρ, by rw [mul_smul]; exact hτ⟩
    · exact Or.inr fun x hx => MonoidHom.mem_ker.1 (hEF (hsplit P hPp hPbot rfl hx))

omit [NumberField k] in
/-- **A level carrying units prescribed at named places carries the flat prescription**, with no
shrinking spent.

The prescription made one named prime at a time asks nothing of the operator group beyond the
number of letters its data is read at, so that number may be answered with itself and the shrinking
taken to be the identity.  What is left of the demand on the level is then a finite Galois level
killing the given lift, and the kernel of a smooth lift is open, so such a level exists. -/
theorem hasFlatOrbitPrescription_of_units (K : IntermediateField k Ω)
    [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hkd : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)
    {Pr : Fin t → Ideal (𝓞 Ω)} (hPrp : ∀ ν, (Pr ν).IsPrime) (hPrbot : ∀ ν, Pr ν ≠ ⊥)
    (hDPr : ∀ ν, D ν = stabilizer Gal(Ω/k) (Pr ν))
    (hℓPr : ∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : 𝓞 ↥K) ∈ v.asIdeal →
      ∃ (σ : Gal(↥K/k)) (ν : Fin t), v = σ • placeUnder K (Pr ν) (hPrbot ν))
    (hfam : HasFlatPrescribedUnits ℓ K) :
    HasFlatOrbitPrescription ℓ U n S j φ D :=
  hasFlatOrbitPrescription_of_places n K hKker hζ hkd hPrp hPrbot hDPr hℓPr
    (fun F _ hFsm hFright => ⟨MonoidHom.id _, isOperatorHom_id, Function.surjective_id,
      exists_level_ker_le isOperatorHom_id K hKker F hFsm hFright⟩) hfam

end Places

end InverseGalois.Shafarevich

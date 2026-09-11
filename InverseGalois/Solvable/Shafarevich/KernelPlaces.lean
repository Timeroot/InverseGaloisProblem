/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.InertiaCharLift
import InverseGalois.Solvable.Shafarevich.KernelCyclic
import InverseGalois.Solvable.Shafarevich.KernelPrimeCyclic
import InverseGalois.Solvable.Shafarevich.LevelKernelPrescription

/-!
# The sharp prescription bought from a family of units of the level

The whole prescription over the field the base realization cuts out is a statement about one
homomorphism of the kernel into a finite elementary abelian group, and such a homomorphism is a
tuple of Kummer characters: name a basis of the layer, and a family of units of the level, one for
each basis vector, assembles into a homomorphism whose coordinates are the Kummer characters of the
units.  Every clause of the prescription then becomes a statement about the local behaviour of that
family of units, place by place — which is exactly the shape the arithmetic can answer.

The dictionary is: the prescribed values at a named prime are the classes of the units in the
completion at the place below it; triviality along the conjugates of a named prime is triviality of
those classes at the conjugate places; ramification of the assembled homomorphism at a prime forces
some unit of the family to have order at the place below not divisible by the exponent; and
cyclicity on a decomposition subgroup is the survival of a single coordinate there.

So the arithmetic input is a single statement about the level: given a finite level above it, a
finite family of places of the level lying in distinct orbits, and a class prescribed at each of
them in each coordinate, there is a family of units of the level which carries the prescribed
classes at the named places, dies at every proper conjugate of them, dies at a further prescribed
finite set of places the named ones avoid, and at every other place where some member has order not
divisible by the exponent either sits over a named place or has that place completely decomposed in
the given finite level with a single coordinate surviving.  That is the arithmetic input, and it
buys the prescription outright: the further finite set is taken to be the orbit of the places below
the given finite family of decomposition subgroups, and the named places avoid it exactly because no
named prime is allowed to sit over that family.  The places above the exponent are asked to be among
those, which is what makes the assembled homomorphism unramified there, and is the reason a named
place is never one of them.

## Main definitions

* `InverseGalois.Shafarevich.HasPrescribedUnits` — **a family of units of a level can be prescribed
  local classes at finitely many places at once, be a local power at a prescribed finite set of
  places the named ones avoid and at the proper conjugates of the named ones, and be confined
  elsewhere to places sitting over the named ones or completely decomposed in a given finite
  level.**

## Main results

* `InverseGalois.Shafarevich.hasKernelPrescription_of_places` — **a level carrying such
  families of units carries the sharp prescription with cyclic values.**

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, decomposition group, local class
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

/-! ### The arithmetic input -/

section Units

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **A family of units of a level can be prescribed local classes at finitely many places at once,
be a local power at a prescribed finite set of places avoided by the named ones and at the proper
conjugates of the named ones, and be confined elsewhere to places sitting over the named ones or
completely decomposed in a given finite level.**

The places are named by an arbitrary finite index type, are asked to be distinct and to stay
distinct from one another under every proper automorphism of the level, and one class modulo
exponent-th powers is prescribed at each of them in each of the coordinates the family is indexed
by.  The classes prescribed at one place are asked to lie on the line of the class of a single unit
of the level, which is what the reciprocity law leaves room for: the power residue symbol of two
coordinates over all the places is trivial and away from the named places contributes nothing, and
the symbol is alternating.  Naming the line by a unit rather than by a class is what lets the lines
at the places of one orbit be carried into one another, an automorphism of the level moving a unit
without moving the place it is read at.

The set of places at which the family is asked to be a local power is prescribed along with the
named places and is asked to avoid them, which is the only thing that keeps the two demands from
colliding: a place carrying a nontrivial class is not a place the family is a local power at.  The
places above the exponent, where the assembled homomorphism has to be unramified, are covered by
that set rather than by a clause of their own, and a named place is asked not to be one of them,
which is the same disjointness read at the exponent.

The finite level in which the leftover places are asked to be completely decomposed is part of the
demand, so that a level cutting out any prescribed finite amount of arithmetic may be named before
the family is chosen. -/
def HasPrescribedUnits (ℓ : ℕ) (K : IntermediateField k Ω) [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → K ≤ E →
    ∀ (ι : Type) [Finite ι] (w : ι → HeightOneSpectrum (𝓞 ↥K)), Function.Injective w →
      (∀ (μ ν : ι) (σ : Gal(↥K/k)), σ ≠ 1 → σ • w μ ≠ w ν) →
      ∀ Tz : Finset (HeightOneSpectrum (𝓞 ↥K)), (∀ μ : ι, w μ ∉ Tz) →
        (∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal) →
        ∀ (d : ℕ) (c : (μ : ι) → Fin d → localClasses (w μ) ℓ),
          (∀ μ : ι, ∃ u : (↥K)ˣ,
            ∀ q : Fin d, c μ q ∈ Subgroup.zpowers (localClassHom (w μ) ℓ u)) →
          ∃ z : Fin d → (↥K)ˣ,
            (∀ (q : Fin d) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz →
              localClassHom v ℓ (z q) = 1) ∧
            (∀ (μ : ι) (q : Fin d), localClassHom (w μ) ℓ (z q) = c μ q) ∧
            (∀ (μ : ι) (σ : Gal(↥K/k)), σ ≠ 1 →
              ∀ q : Fin d, localClassHom (σ • w μ) ℓ (z q) = 1) ∧
            ∀ v : HeightOneSpectrum (𝓞 ↥K), (∃ q : Fin d, ¬ (ℓ : ℤ) ∣ placeValue v (z q)) →
              (∃ (μ : ι) (σ : Gal(↥K/k)), v = σ • w μ) ∨
                ((∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
                    stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup) ∧
                  (∃ q₀ : Fin d, ∀ q : Fin d, q ≠ q₀ → localClassHom v ℓ (z q) = 1) ∧
                  ∀ σ : Gal(↥K/k), σ ≠ 1 → ∀ q : Fin d, localClassHom (σ • v) ℓ (z q) = 1)

end Units

/-! ### The prescription -/

section Places

variable {ℓ : ℕ} [Fact ℓ.Prime] {U : Type} [Group U] [Finite U] {n : ℕ} {S : Type} [Group S]
  [Finite S] {j : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] {φ : Gal(Ω/k) →* U} {t : ℕ} {D : Fin t → Subgroup Gal(Ω/k)}

attribute [local instance] genericQuotAction zmodTrivialAction

set_option maxHeartbeats 800000 in
/-- **A level carrying families of units prescribed at named places carries the sharp prescription
with cyclic values.**

A basis of the layer is named, and the homomorphism asked for is assembled out of the family of
units: its value is the product of the powers of the basis by the Kummer characters of the units.
Each clause of the prescription is then read off the family.  The values prescribed along a
decomposition subgroup are the coordinates of a character of it, and each coordinate is the Kummer
character of any unit with the right class at the place below, so prescribing the values is
prescribing those classes; the values being cyclic, the coordinates are the multiples of one
character of the subgroup and the classes are the powers of one class.  Triviality along the
conjugates of a named prime, and along the conjugates of a leftover one, is triviality of the
classes at the conjugate places.  Where the
assembled homomorphism ramifies, some unit of the family has order not divisible by the exponent at
the place below, and the confinement clause of the family then says the prime sits over a named
place — in which case it is a conjugate of the named prime, two primes with the same place below
differing by an automorphism of the level — or that its place is completely decomposed in a finite
level killing the given lift, whence the whole decomposition subgroup dies there; and the surviving
single coordinate is what makes the values on that subgroup powers of one of them.

The set of places the family of units is asked to be a local power at is the orbit of the places
below the given finite family of decomposition subgroups.  The named places avoid it because no
named prime sits over that family, and the places above the exponent are among it by hypothesis,
which is what makes the assembled homomorphism unramified there.

The finite level is the one cut out by the kernel of the given lift together with the level itself,
which is finite because the lift is smooth and the level is finite.  No shrinking is spent: the
number of letters is the one asked for and the map of layers is the identity. -/
theorem hasKernelPrescription_of_places (K : IntermediateField k Ω) [FiniteDimensional k ↥K]
    [NumberField ↥K] [IsGalois k ↥K] (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K}
    (hζ : IsPrimitiveRoot ζ ℓ) {Pr : Fin t → Ideal (𝓞 Ω)} (hPrp : ∀ ν, (Pr ν).IsPrime)
    (hPrbot : ∀ ν, Pr ν ≠ ⊥) (hDPr : ∀ ν, D ν = stabilizer Gal(Ω/k) (Pr ν))
    (hℓPr : ∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : 𝓞 ↥K) ∈ v.asIdeal →
      ∃ (σ : Gal(↥K/k)) (ν : Fin t), v = σ • placeUnder K (Pr ν) (hPrbot ν))
    (hfam : HasPrescribedUnits ℓ K) :
    HasKernelPrescription ℓ U n S j φ D := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : IsGalois ↥K Ω := IsGalois.tower_top_of_isGalois k ↥K Ω
  have hanti : ∀ E₁ E₂ : IntermediateField k Ω, E₁ ≤ E₂ →
      E₂.fixingSubgroup ≤ E₁.fixingSubgroup := fun _ _ h => fixingSubgroup_antitone h
  have hroot : ∀ x : (↥K)ˣ, ∃ β : Ωˣ, β ^ ℓ = Units.map (algebraMap ↥K Ω : ↥K →* Ω) x := by
    intro x
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Ω (x : ↥K)) hℓ.pos
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, zero_pow hℓ.ne_zero] at hy
      exact (map_ne_zero_iff _ (algebraMap ↥K Ω).injective).2 x.ne_zero hy.symm
    refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.coe_map]
    exact hy
  have hkd : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ :=
    isKummerData_zmod hζ hroot
  refine ⟨n, ?_⟩
  intro _ F ι hιfin Q A a hFsm hQp hQbot hQorb hQker _ _ hAcase hasm hacyc havoid
  haveI := hιfin
  haveI : ∀ μ, (Q μ).IsPrime := hQp
  haveI : ∀ ν, (Pr ν).IsPrime := hPrp
  -- a finite level on which the given lift and the base realization both die
  obtain ⟨E₀, hE₀fin, -, hE₀le⟩ :=
    exists_fixingSubgroup_le ((isOpenNormal_ker_of_isSmoothHom hFsm).inf
      (isOpenNormal_fixingSubgroup K))
  haveI := hE₀fin
  haveI : FiniteDimensional k ↥(E₀ ⊔ K) := inferInstance
  have hKE : K ≤ E₀ ⊔ K := le_sup_right
  have hEF : (E₀ ⊔ K).fixingSubgroup ≤ F.ker := fun x hx =>
    (Subgroup.mem_inf.1 (hE₀le (hanti E₀ (E₀ ⊔ K) le_sup_left hx))).1
  have hEK : (E₀ ⊔ K).fixingSubgroup ≤ φ.ker := by
    intro x hx
    rw [← hKker]
    exact hanti K (E₀ ⊔ K) hKE hx
  -- the places below the named primes
  have hinj : Function.Injective fun μ => placeUnder K (Q μ) (hQbot μ) :=
    placeUnder_injective_of_forall_smul hQbot hQorb
  have hconj : ∀ (μ ν : ι) (σ : Gal(↥K/k)), σ ≠ 1 →
      σ • placeUnder K (Q μ) (hQbot μ) ≠ placeUnder K (Q ν) (hQbot ν) :=
    fun μ ν σ hσ => placeUnder_smul_ne hKker hQbot hQorb hQker hσ μ ν
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
  -- the classes the prescribed values name
  have hex : ∀ μ : ι, ∃ (u₀ : (↥K)ˣ)
        (c : Fin (layerDim ℓ (Generic U n S) j) →
          localClasses (placeUnder K (Q μ) (hQbot μ)) ℓ),
      (∀ q, c q ∈ Subgroup.zpowers (localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ u₀)) ∧
      ∀ z : Fin (layerDim ℓ (Generic U n S) j) → (↥K)ˣ,
        (∀ q, localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ (z q) = c q) →
          ∀ (x : ↥(A μ)) (hx : (x : Gal(Ω/k)) ∈ φ.ker),
            kummerKernelHom hKker hkd (layerBasis ℓ (Generic U n S) j)
                layerBasis_pow_eq_one z ⟨(x : Gal(Ω/k)), hx⟩ = a μ x :=
    fun μ => exists_localClass_zpowers_forall_kummerKernelHom_eq hKker hkd
      (hasKummerCharInertiaLift hkd) hℓ (layerBasis ℓ (Generic U n S) j) layerBasis_pow_eq_one
      (χ := fun q e => layerCoord ℓ (Generic U n S) j e q) prod_layerBasis_pow_layerCoord
      (fun q e e' => layerCoord_mul e e' q) (hQbot μ) rfl (Or.inl (hAcase μ)) (a μ) (hasm μ)
      (hacyc μ)
  choose u₀ c hcline hc using hex
  have hdisjℓ : ∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (placeUnder K (Q μ) (hQbot μ)).asIdeal := by
    intro μ hmem
    obtain ⟨σ, ν, hσν⟩ := hℓPr _ hmem
    exact hdisj μ (hσν ▸ hmemTz σ ν)
  obtain ⟨z, hzT, hz2, hz3, hz4⟩ := hfam (E₀ ⊔ K) inferInstance hKE ι
    (fun μ => placeUnder K (Q μ) (hQbot μ)) hinj hconj Tz hdisj hdisjℓ
    (layerDim ℓ (Generic U n S) j) c (fun μ => ⟨u₀ μ, hcline μ⟩)
  have hz1 : ∀ (q : Fin (layerDim ℓ (Generic U n S) j)) (v : HeightOneSpectrum (𝓞 ↥K)),
      (ℓ : 𝓞 ↥K) ∈ v.asIdeal → localClassHom v ℓ (z q) = 1 := by
    intro q v hv
    obtain ⟨σ, ν, rfl⟩ := hℓPr v hv
    exact hzT q _ (hmemTz σ ν)
  refine ⟨MonoidHom.id (Generic U n S), isOperatorHom_id, Function.surjective_id,
    kummerKernelHom hKker hkd (layerBasis ℓ (Generic U n S) j) layerBasis_pow_eq_one z,
    isSmooth₁_kummerKernelHom hKker hkd _ _ z, ?_, ?_, ?_, ?_⟩
  · intro ν ρ y hy
    haveI : (ρ⁻¹ • Pr ν).IsPrime := inferInstance
    exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd _ _ z
      (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ⁻¹ • placeUnder K (Pr ν) (hPrbot ν))
      (asIdeal_smul_placeUnder K (hPrbot ν) ρ⁻¹) (fun q => hzT q _ (hmemTz _ ν))
      (mem_stabilizer_smul_iff.2 (by rw [inv_inv, ← hDPr ν]; exact hy))
  · intro μ x hx
    rw [layerSubMap_id, MonoidHom.id_apply]
    exact hc μ z (fun q => hz2 μ q) x hx
  · intro μ ρ hρ y hy
    have hσ : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ ≠ 1 := fun h0 =>
      hρ ((restrictNormalHom_eq_one_iff_mem_ker hKker ρ).1 h0)
    exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd _ _ z
      (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ • placeUnder K (Q μ) (hQbot μ))
      (asIdeal_smul_placeUnder K (hQbot μ) ρ) (fun q => hz3 μ _ hσ q) hy
  · rintro P hPp hPbot ⟨y, hyI, hyne⟩
    haveI := hPp
    obtain ⟨q, hq⟩ := exists_not_dvd_placeValue_of_kummerKernelHom_ne_one hKker hkd _ _ z hℓ
      hPbot hz1 hyI hyne
    rcases hz4 (placeUnder K P hPbot) ⟨q, hq⟩ with ⟨μ, σ, hvσ⟩ | ⟨hsplit, ⟨q₀, hq₀⟩, hconjv⟩
    · obtain ⟨ρ, hρ⟩ := restrictNormalHom_surjective_level K σ
      have hbot : ρ • Q μ ≠ ⊥ := by
        intro h0
        exact hQbot μ (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ⁻¹ • I) h0)
      have hpl : placeUnder K (ρ • Q μ) hbot = placeUnder K P hPbot := by
        refine HeightOneSpectrum.ext ?_
        rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot μ) ρ, hρ, ← hvσ]
      obtain ⟨τ, -, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot hPbot hpl
      exact Or.inl ⟨μ, τ * ρ, by rw [mul_smul]; exact hτ⟩
    · refine Or.inr ⟨fun x hx => by
          rw [MonoidHom.mem_ker.1 (hEF (hsplit P hPp hPbot rfl hx)), _root_.map_one],
        fun x hx => hEK (hsplit P hPp hPbot rfl hx), fun ρ hρ y' hy' => ?_, ?_⟩
      · have hσ : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ ≠ 1 := fun h0 =>
          hρ ((restrictNormalHom_eq_one_iff_mem_ker hKker ρ).1 h0)
        exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd _ _ z
          (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ • placeUnder K P hPbot)
          (asIdeal_smul_placeUnder K hPbot ρ) (fun s => hconjv _ hσ s) hy'
      · exact exists_forall_mem_zpowers_kummerKernelHom hKker hkd _ _ z hℓ
          (w := placeUnder K P hPbot) rfl hq₀

end Places

end InverseGalois.Shafarevich

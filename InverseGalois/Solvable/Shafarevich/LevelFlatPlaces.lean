/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.KernelPlaces
import InverseGalois.Solvable.Shafarevich.LevelFlatOrbit
import InverseGalois.Solvable.Shafarevich.LevelFlatRadicand

/-!
# The prescription at one named prime bought from a single invariant radicand

Over the field the base realization cuts out, the part of inertia at a prime away from the exponent
which that realization kills is carried by a single element modulo an open subgroup, so a
homomorphism of it into the layer is a power of a single one of its own values and is answered by
the powers of one radicand.  That is what makes the prescription at one named prime — the
prescription which asks equivariance only of the decomposition subgroup of the prime it belongs to —
cost only one unit of the level per named prime, rather than one for each coordinate of the layer.

The clause which decides the shape of the arithmetic is equivariance.  A radicand fixed by an
automorphism up to an exponent-th power has a Kummer character which that automorphism scales by
exactly the power to which it raises the roots of unity, and the homomorphism assembled out of the
powers of the radicand is then raised to that same power; comparing the two at a single element
where the character takes a unit value turns the scaling into equivariance for the operator group.
Equivariance for the whole group would ask the radicand to be rational, and the prescription could
then not be made at a single prime; asking it only along the decomposition subgroup of the named
prime asks the radicand only to be fixed by the automorphisms of the level which fix the place below
that prime, which is a genuine demand on a genuine unit.

So the arithmetic input is a single statement about the level: given a finite level above it and a
finite family of places lying in pairwise distinct orbits and away from the exponent, there is one
unit of the level for each named place, fixed up to an exponent-th power by every automorphism
fixing its place, of order at its place not divisible by the exponent, a local power at a further
prescribed finite set of places the named ones avoid, at every proper conjugate of its own place,
and at every conjugate of the other named places — and at every other place where its order is not
divisible by the exponent either sitting over a named place or having that place completely
decomposed in the given finite level.

Nothing is prescribed of the local class of the unit at its own place beyond that its order there is
prime to the exponent; the coefficient which turns the Kummer character into the prescribed
homomorphism is read off afterwards, the character of the part of inertia in question being
proportional to any of its own values which is a unit.

## Main definitions

* `InverseGalois.Shafarevich.HasInvariantRadicands` — **one unit of a level for each of finitely
  many places lying in distinct orbits, fixed up to an exponent-th power by the automorphisms
  fixing its place, of order there prime to the exponent, a local power at a prescribed finite set
  of places and at every conjugate of the named places other than its own, and confined elsewhere
  to places sitting over the named ones or completely decomposed in a given finite level.**

## Main results

* `InverseGalois.Shafarevich.hasFlatOrbitPrescription_of_places` — **a level carrying such units
  carries the prescription read one named prime at a time.**

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, radicand, inertia subgroup, equivariance
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### The arithmetic input -/

section Radicands

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **One unit of a level for each of finitely many places lying in distinct orbits, fixed up to an
exponent-th power by the automorphisms fixing its place, of order there prime to the exponent, a
local power at a prescribed finite set of places and at every conjugate of the named places other
than its own, and confined elsewhere to places sitting over the named ones or completely decomposed
in a given finite level.**

The places are named by an arbitrary finite index type and are asked to lie in pairwise distinct
orbits under the automorphisms of the level over the base, which is what keeps the demand made at
one of them from colliding with the demand made at the others.

Invariance is the clause the prescription at a single prime is bought with: the unit belonging to a
place is asked to be carried to itself, up to an exponent-th power, by every automorphism of the
level fixing that place.  It is not asked to be invariant under any more than that, and it is
exactly that much invariance which turns into equivariance of the assembled homomorphism along the
decomposition subgroup of a prime above the place.

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
smaller. -/
def HasInvariantRadicands (ℓ : ℕ) [NeZero ℓ] (K : IntermediateField k Ω) [NumberField ↥K] : Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ (ι : Type) [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K)),
      (∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν) →
      ∀ Tz : Finset (HeightOneSpectrum (𝓞 ↥K)), (∀ μ : ι, w μ ∉ Tz) →
        (∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal) →
        ∃ z : ι → (↥K)ˣ,
          (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ = w μ → ∃ s : (↥K)ˣ, σ • z μ = z μ * s ^ ℓ) ∧
          (∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → localClassHom v ℓ (z μ) = 1) ∧
          (∀ μ : ι, ¬ (ℓ : ℤ) ∣ placeValue (w μ) (z μ)) ∧
          (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ≠ w μ → localClassHom (σ • w μ) ℓ (z μ) = 1) ∧
          (∀ μ ν : ι, ν ≠ μ → ∀ σ : Gal(↥K/k), localClassHom (σ • w ν) ℓ (z μ) = 1) ∧
          ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), ¬ (ℓ : ℤ) ∣ placeValue v (z μ) →
            (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
              ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
                stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup

end Radicands

/-! ### The prescription -/

section Places

variable {ℓ : ℕ} [Fact ℓ.Prime] [NeZero ℓ] {U : Type} [Group U] [Finite U] {n : ℕ} {S : Type}
  [Group S] [Finite S] {j : ℕ} {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsAlgClosed Ω] {φ : Gal(Ω/k) →* U} {t : ℕ} {D : Fin t → Subgroup Gal(Ω/k)}

attribute [local instance] genericQuotAction zmodTrivialAction

/-- **A level carrying one invariant radicand for each named place carries the prescription read one
named prime at a time.**

A basis of the layer is named, and the homomorphism belonging to a named prime is assembled out of
the powers of the single unit belonging to the place below it: its value is the product of the
powers of the basis by the multiples of the Kummer character of that unit.  Which multiples they are
is read off the prescribed values, the character of the part of inertia the base realization kills
being proportional to the Kummer character of the unit — the unit's own character there takes a unit
value, its order at the place being prime to the exponent, and the part of inertia in question is
carried by a single element modulo an open subgroup.

Equivariance along the decomposition subgroup of the named prime is bought with the invariance of
the unit.  An automorphism fixing the prime fixes the place below it, hence carries the unit to
itself up to an exponent-th power, and so raises the assembled homomorphism to the power by which it
raises the roots of unity; evaluating that at an element of the prescribed subgroup where the
character takes the value one, and comparing with the equivariance the prescribed values already
have, identifies the power with the action of the operator group.  The two then agree everywhere,
every value being a power of the value at that element.

The remaining clauses are read off the unit place by place.  Triviality along the finite family, and
along the subgroups belonging to the other named primes, and along the decomposition subgroups of
the conjugates of the prime outside the saturation, is triviality of the local class of the unit at
the corresponding place: a conjugate of the prime whose place below is a proper conjugate of the
named place is covered by the invariance clause read backwards, an automorphism moving the place
being one the unit is a local power at.  Where the assembled homomorphism ramifies, the unit has
order at the place below not divisible by the exponent, and the confinement clause then says the
prime sits over a named place — in which case it is a conjugate of that named prime, two primes with
the same place below differing by an automorphism of the level — or that its place is completely
decomposed in a finite level killing the given lift, whence the whole decomposition subgroup dies
there.

No shrinking of the operator group is spent: the prescribed values are carried across the identity.
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
    (hrad : HasInvariantRadicands ℓ K) :
    HasFlatOrbitPrescription ℓ U n S j φ D := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  haveI : IsGalois ↥K Ω := IsGalois.tower_top_of_isGalois k ↥K Ω
  refine ⟨n, ?_⟩
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
  obtain ⟨z, hzinv, hzT, hzord, hzconj, hzother, hzram⟩ :=
    hrad E hEfin hEgal hKE ι (fun μ => placeUnder K (Q μ) (hQbot μ)) hwdist Tz hdisj hdisjℓ
  have hz1 : ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), (ℓ : 𝓞 ↥K) ∈ v.asIdeal →
      localClassHom v ℓ (z μ) = 1 := by
    intro μ v hv
    obtain ⟨σ, ν, rfl⟩ := hℓPr v hv
    exact hzT μ _ (hmemTz σ ν)
  have hzpow : ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), localClassHom v ℓ (z μ) = 1 →
      ∀ r : ℕ, localClassHom v ℓ (z μ ^ r) = 1 := by
    intro μ v hv r
    rw [_root_.map_pow, hv, one_pow]
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
      (layerSub_pow_eq_one ℓ (Generic U n S) j) (a μ) (hasm μ)
  have hdata : ∀ μ : ι, ∃ (e : ↥(A μ) → ZMod ℓ) (m : Fin (layerDim ℓ (Generic U n S) j) → ZMod ℓ),
      (∀ x y : ↥(A μ), e (x * y) = e x + e y) ∧ (∀ x : ↥(A μ), a μ x = 1 → e x = 0) ∧
        ∀ (q : Fin (layerDim ℓ (Generic U n S) j)) (x : ↥(A μ)),
          layerCoord ℓ (Generic U n S) j (a μ x) q = m q * e x :=
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
  -- the homomorphism belonging to each named prime
  obtain ⟨u, hu⟩ : ∃ u : ι → (↥(φ.ker) →* ↥(layerSub ℓ (Generic U n S) j)), ∀ μ : ι,
      u μ = kummerKernelHom hKker hkd (layerBasis ℓ (Generic U n S) j) layerBasis_pow_eq_one
        (fun q => z μ ^ ((m μ q * c μ).val)) := ⟨_, fun _ => rfl⟩
  have hap : ∀ (μ : ι) (y : ↥φ.ker), u μ y
      = (∏ q, layerBasis ℓ (Generic U n S) j q ^ ((m μ q * c μ).val)) ^
          (kummerChar hkd (z μ) (kerGalEquiv hKker y)).val := by
    intro μ y
    rw [hu μ]
    exact kummerKernelHom_units_pow_apply hKker hkd _ _ (z μ) (fun q => m μ q * c μ) y
  -- the prescribed values are reproduced
  have hfive : ∀ (μ : ι) (x : ↥(A μ)) (hx : (x : Gal(Ω/k)) ∈ φ.ker),
      u μ ⟨(x : Gal(Ω/k)), hx⟩ = a μ x := by
    intro μ x hx
    rw [hu μ]
    refine kummerKernelHom_eq_of_forall_kummerChar_eq hKker hkd _ _ _
      (χ := fun q v => layerCoord ℓ (Generic U n S) j v q) prod_layerBasis_pow_layerCoord
      fun q => ?_
    show kummerChar hkd (z μ ^ ((m μ q * c μ).val)) (kerGalEquiv hKker ⟨(x : Gal(Ω/k)), hx⟩)
      = layerCoord ℓ (Generic U n S) j (a μ x) q
    rw [kummerChar_units_pow, hcoord μ q x, hc μ x, hψ μ x hx, nsmul_eq_mul,
      ZMod.natCast_zmod_val, mul_assoc]
  -- equivariance along the decomposition subgroup of the named prime
  have htwo : ∀ (μ : ι) (g : Gal(Ω/k)), g ∈ stabilizer Gal(Ω/k) (Q μ) →
      ∀ (y : ↥(φ.ker)) (hy : g * (y : Gal(Ω/k)) * g⁻¹ ∈ φ.ker),
        u μ ⟨g * (y : Gal(Ω/k)) * g⁻¹, hy⟩ = φ g • u μ y := by
    intro μ g hg y hy
    obtain ⟨ee, hee⟩ := exists_smul_kummerRootUnit_eq_pow (hζ := hζ) g
    have hgw : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g •
        placeUnder K (Q μ) (hQbot μ) = placeUnder K (Q μ) (hQbot μ) := by
      refine HeightOneSpectrum.ext ?_
      rw [asIdeal_smul_placeUnder K (hQbot μ) g, mem_stabilizer_iff.1 hg, placeUnder_asIdeal]
    obtain ⟨s, hs⟩ := hzinv μ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g) hgw
    have hconj : ∀ (y' : ↥φ.ker) (hy' : g * (y' : Gal(Ω/k)) * g⁻¹ ∈ φ.ker),
        u μ ⟨g * (y' : Gal(Ω/k)) * g⁻¹, hy'⟩ = u μ y' ^ ee := by
      intro y' hy'
      rw [hu μ]
      exact kummerKernelHom_units_pow_conj hKker hkd _ _ (z μ) (fun q => m μ q * c μ) hee hs y' hy'
    -- the value at the normalized element is the element the homomorphism is a power of
    have hx₀k : ((x₀ μ : ↥(A μ)) : Gal(Ω/k)) ∈ φ.ker := hAker μ (x₀ μ).2
    have hcA : g * ((x₀ μ : ↥(A μ)) : Gal(Ω/k)) * g⁻¹ ∈ A μ := by
      have hmem : ((x₀ μ : ↥(A μ)) : Gal(Ω/k)) ∈ Ideal.inertia Gal(Ω/k) (Q μ) ⊓ φ.ker :=
        (hAeq μ).le (x₀ μ).2
      refine (hAeq μ).ge (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
      · have hin := mem_inertia_conj (Subgroup.mem_inf.1 hmem).1 g
        rwa [mem_stabilizer_iff.1 hg] at hin
      · refine MonoidHom.mem_ker.2 ?_
        rw [_root_.map_mul, _root_.map_mul, _root_.map_inv,
          MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hmem).2, mul_one, mul_inv_cancel]
    have hval : u μ ⟨((x₀ μ : ↥(A μ)) : Gal(Ω/k)), hx₀k⟩
        = ∏ q, layerBasis ℓ (Generic U n S) j q ^ ((m μ q * c μ).val) := by
      rw [hap μ ⟨_, hx₀k⟩, ← hψ μ (x₀ μ) hx₀k, hx₀ μ, ZMod.val_one, pow_one]
    have hV : (φ g • ∏ q, layerBasis ℓ (Generic U n S) j q ^ ((m μ q * c μ).val))
        = (∏ q, layerBasis ℓ (Generic U n S) j q ^ ((m μ q * c μ).val)) ^ ee := by
      calc (φ g • ∏ q, layerBasis ℓ (Generic U n S) j q ^ ((m μ q * c μ).val))
          = φ g • a μ (x₀ μ) := by rw [← hval, hfive μ (x₀ μ) hx₀k]
        _ = a μ ⟨g * ((x₀ μ : ↥(A μ)) : Gal(Ω/k)) * g⁻¹, hcA⟩ := (haequiv μ g (x₀ μ) hcA).symm
        _ = u μ ⟨g * ((x₀ μ : ↥(A μ)) : Gal(Ω/k)) * g⁻¹, hAker μ hcA⟩ :=
            (hfive μ ⟨g * ((x₀ μ : ↥(A μ)) : Gal(Ω/k)) * g⁻¹, hcA⟩ (hAker μ hcA)).symm
        _ = (∏ q, layerBasis ℓ (Generic U n S) j q ^ ((m μ q * c μ).val)) ^ ee := by
            rw [hconj ⟨_, hx₀k⟩ (hAker μ hcA), hval]
    rw [hconj y hy, hap μ y, smul_pow', hV, ← pow_mul, ← pow_mul,
      mul_comm (kummerChar hkd (z μ) (kerGalEquiv hKker y)).val ee]
  refine ⟨MonoidHom.id (Generic U n S), isOperatorHom_id, Function.surjective_id, u, ?_, htwo,
    ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨V, hV, hVu⟩ := exists_isOpenNormal_forall_kummerKernelHom_eq_one hKker hkd
      (layerBasis ℓ (Generic U n S) j) layerBasis_pow_eq_one
      (fun (μ : ι) q => z μ ^ ((m μ q * c μ).val))
    exact ⟨V, hV, fun μ y hy => by rw [hu μ]; exact hVu μ y hy⟩
  · intro μ ν ρ y hy
    haveI : (ρ⁻¹ • Pr ν).IsPrime := inferInstance
    rw [hu μ]
    exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd _ _ _
      (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ⁻¹ • placeUnder K (Pr ν) (hPrbot ν))
      (asIdeal_smul_placeUnder K (hPrbot ν) ρ⁻¹)
      (fun q => hzpow μ _ (hzT μ _ (hmemTz _ ν)) ((m μ q * c μ).val))
      (mem_stabilizer_smul_iff.2 (by rw [inv_inv, ← hDPr ν]; exact hy))
  · intro μ ν hνμ ρ y hy
    haveI : (ρ⁻¹ • Q ν).IsPrime := inferInstance
    rw [hu μ]
    exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd _ _ _
      (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ⁻¹ • placeUnder K (Q ν) (hQbot ν))
      (asIdeal_smul_placeUnder K (hQbot ν) ρ⁻¹)
      (fun q => hzpow μ _ (hzother μ ν hνμ _) ((m μ q * c μ).val))
      (mem_stabilizer_smul_iff.2 (by rw [inv_inv]; exact hAstab ν hy))
  · exact fun μ x hx => by rw [hfive μ x hx, layerSubMap_id, MonoidHom.id_apply]
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
    exact kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd _ _ _
      (w := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ • placeUnder K (Q μ) (hQbot μ))
      (asIdeal_smul_placeUnder K (hQbot μ) ρ)
      (fun q => hzpow μ _ (hzconj μ _ hne) ((m μ q * c μ).val)) hy
  · rintro μ P hPp hPbot ⟨y, hyI, hyne⟩
    haveI := hPp
    rw [hu μ] at hyne
    obtain ⟨q, hq⟩ := exists_not_dvd_placeValue_of_kummerKernelHom_ne_one hKker hkd _ _ _ hℓ
      hPbot (fun q' v hv => hzpow μ v (hz1 μ v hv) ((m μ q' * c μ).val)) hyI hyne
    have hq' : ¬ (ℓ : ℤ) ∣ placeValue (placeUnder K P hPbot) (z μ) := fun hdvd =>
      hq (by rw [placeValue_pow]; exact hdvd.mul_left _)
    rcases hzram μ (placeUnder K P hPbot) hq' with ⟨ν, σ, hvσ⟩ | hsplit
    · obtain ⟨ρ, hρ⟩ := restrictNormalHom_surjective_level K σ
      have hbot : ρ • Q ν ≠ ⊥ := by
        intro h0
        exact hQbot ν (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ⁻¹ • I) h0)
      have hpl : placeUnder K (ρ • Q ν) hbot = placeUnder K P hPbot := by
        refine HeightOneSpectrum.ext ?_
        rw [placeUnder_asIdeal, ← asIdeal_smul_placeUnder K (hQbot ν) ρ, hρ, ← hvσ]
      obtain ⟨τ, -, hτ⟩ := exists_mem_fixingSubgroup_smul_eq_of_placeUnder_eq K hbot hPbot hpl
      exact Or.inl ⟨ν, τ * ρ, by rw [mul_smul]; exact hτ⟩
    · refine Or.inr fun x hx => ?_
      rw [MonoidHom.mem_ker.1 (hEF (hsplit P hPp hPbot rfl hx)), _root_.map_one]

end Places

end InverseGalois.Shafarevich

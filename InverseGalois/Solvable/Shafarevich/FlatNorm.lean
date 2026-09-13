/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.FlatInvariant
import InverseGalois.Solvable.Shafarevich.LevelFlatRadicand

/-!
# The invariant tensor assembled from a whole orbit of units

The tensor the flat step asks the arithmetic for is asked to be invariant, and the cheapest way to
build an invariant tensor is to build it out of one unit at each named place.  That way is not
available.  A tensor assembled from one unit at each named place is invariant exactly when each of
those units is fixed, modulo exponent-th powers, by the automorphisms of the level fixing its own
place, and that is a demand the arithmetic cannot meet: the unit cutting out a prescribed divisor is
determined by that divisor up to the global units, so asking it to be fixed asks a class of the
divisor class group to be trivial, and there are number fields where it is not.

A tensor need not be assembled that way.  Assembled from a whole orbit — the sum, over all the
automorphisms of the level, of the conjugate of a unit tensored against the conjugate of a
coordinate of the prescribed value — the invariance is nothing but a reindexing of that sum, and
nothing whatever is asked of the unit.  The order of the assembled tensor at a named place then
collects one contribution from each automorphism fixing that place, and the value it prescribes
there comes out as the product of the conjugates, over the automorphisms fixing the place, of the
coordinate the unit was tensored against.

So the price of dropping the demand on the units is that the prescribed value must be a norm from
the subgroup fixing its place rather than merely fixed by it.  That price is zero whenever the
exponent does not divide the order of that subgroup: a fixed element is then the norm of its own
power by the inverse of that order.  What was a demand on the arithmetic of the level has become a
demand on the choice of the named places, and the named places are chosen by a density theorem.

## Main definitions

* `InverseGalois.Shafarevich.HasOrbitPrescribedUnits` — **a unit of a level can be found for each of
  finitely many reachable places lying in distinct orbits, of order there prime to the exponent, a
  local power at a prescribed finite set of places the whole orbit of each named place avoids and at
  every proper conjugate of its own place and at every conjugate of the others, and confined
  elsewhere** — the demand the flat step makes with nothing equivariant left in it.
* `InverseGalois.Shafarevich.HasTameInvariantUnitTensor` — the invariant tensor demand, made only of
  named places whose stabilizer in the automorphisms of the level has order prime to the exponent.

## Main results

* `InverseGalois.Shafarevich.hasTameInvariantUnitTensor_of_hasOrbitPrescribedUnits` — **units asked
  for nothing equivariant assemble into an invariant tensor at places whose stabilizer is prime to
  the exponent.**
* `InverseGalois.Shafarevich.hasInvariantUnitTensor_of_hasTameInvariantUnitTensor` — a level all of
  whose places have stabilizer of order prime to the exponent carries the unrestricted demand.

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, Galois orbit, norm, invariant tensor
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField TensorProduct

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

/-! ### Powers with integer exponents -/

section Zpow

variable {ℓ : ℕ}

/-- A power by a sum of integer exponents is the product of the powers. -/
theorem zpow_finset_sum {M : Type*} [CommGroup M] {T : Type*} (a : M) (s : Finset T) (f : T → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

/-- A product of powers by one integer exponent is the power of the product. -/
theorem finset_prod_zpow {M : Type*} [CommGroup M] {T : Type*} (s : Finset T) (f : T → M) (n : ℤ) :
    ∏ i ∈ s, f i ^ n = (∏ i ∈ s, f i) ^ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, mul_zpow]

/-- An element killed by the exponent is killed by every multiple of it. -/
theorem zpow_eq_one_of_pow_eq_one {M : Type*} [CommGroup M] {x : M} (hx : x ^ ℓ = 1) {A : ℤ}
    (h : (ℓ : ℤ) ∣ A) : x ^ A = 1 := by
  obtain ⟨j, rfl⟩ := h
  rw [zpow_mul, zpow_natCast, hx, one_zpow]

end Zpow

/-! ### The order and the local class of a moved unit -/

section Place

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]

/-- The order of the identity at a place is zero. -/
theorem placeValue_one_eq_zero (v : HeightOneSpectrum (𝓞 K)) : placeValue v (1 : Kˣ) = 0 := by
  have h := placeValue_mul v (1 : Kˣ) 1
  rw [one_mul] at h
  omega

/-- **The order of a product at a place is the sum of the orders.** -/
theorem placeValue_prod_eq_sum {T : Type*} (v : HeightOneSpectrum (𝓞 K)) (s : Finset T)
    (f : T → Kˣ) : placeValue v (∏ i ∈ s, f i) = ∑ i ∈ s, placeValue v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, placeValue_one_eq_zero]
  | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, placeValue_mul, ih]

/-- **The order of a conjugated unit at a place is its order at the place moved back.** -/
theorem placeValue_smul_unit (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    placeValue v (σ • a) = placeValue (σ⁻¹ • v) a := by
  rw [← galUnits_eq_smul, ← placeValue_galSmul (σ⁻¹ • v) σ a, smul_inv_smul]

/-- **A unit which is a local power at a place moved back is a local power, after conjugation, at
the place itself.** -/
theorem localClassHom_smul_eq_one (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (a : Kˣ)
    (h : localClassHom (σ⁻¹ • v) n a = 1) : localClassHom v n (σ • a) = 1 := by
  have h2 := localClassesGalEquiv_localClassHom σ (σ⁻¹ • v) n a
  rw [h, _root_.map_one, smul_inv_smul, galUnits_eq_smul] at h2
  exact h2.symm

end Place

/-! ### Complete decomposition along an orbit -/

section Decomposed

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K]

omit [NumberField ↥K] in
/-- **Complete decomposition in a Galois level is a property of the whole orbit of a place.**  A
prime of the algebraic closure above the moved place is the image of one above the place itself, so
its decomposition subgroup is the conjugate of a decomposition subgroup lying in the subgroup fixing
the level, and that subgroup is normal because the level is Galois. -/
theorem forall_stabilizer_le_fixingSubgroup_smul {E : IntermediateField k Ω} [IsGalois k ↥E]
    {v : HeightOneSpectrum (𝓞 ↥K)} (σ : Gal(↥K/k))
    (h : ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
      stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup) :
    ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = (σ • v).asIdeal →
      stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup := by
  intro P hPp hPbot hPun g hg
  haveI := hPp
  obtain ⟨ρ, hρ⟩ := restrictNormalHom_surjective_level K σ
  have hP'bot : ρ⁻¹ • P ≠ ⊥ := by
    intro h0
    exact hPbot (by simpa using congrArg (fun I : Ideal (𝓞 Ω) => ρ • I) h0)
  have hP'un : Ideal.under (𝓞 ↥K) (ρ⁻¹ • P) = v.asIdeal := by
    rw [under_smul_ringOfIntegers ↥K, hPun, _root_.map_inv, hρ, asIdeal_smul, inv_smul_smul]
  have hle := h (ρ⁻¹ • P) inferInstance hP'bot hP'un
  have hgst : ρ⁻¹ * g * ρ ∈ stabilizer Gal(Ω/k) (ρ⁻¹ • P) := by
    rw [mem_stabilizer_iff, smul_smul, mul_assoc (ρ⁻¹ * g) ρ ρ⁻¹, mul_inv_cancel, mul_one,
      ← smul_smul, mem_stabilizer_iff.1 hg]
  have hconj := (normal_fixingSubgroup E).conj_mem _ (hle hgst) ρ
  rwa [show ρ * (ρ⁻¹ * g * ρ) * ρ⁻¹ = g by group] at hconj

end Decomposed

/-! ### The demand with no equivariance in it -/

section Demand

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **A unit of a level can be found for each of finitely many reachable places lying in distinct
orbits, of order there prime to the exponent, a local power at a prescribed finite set of places the
whole orbit of each named place avoids and at every proper conjugate of its own place and at every
conjugate of the others, and confined elsewhere to places sitting over the named ones or completely
decomposed in a given finite level.**

This is the demand the flat step makes with the equivariance clause struck out.  Nothing at all is
asked of the way the automorphisms of the level move the unit; the invariance the step needs is
bought instead by summing over a whole orbit, which costs the prescribed value being a norm from the
subgroup fixing its place.

The set of places the unit is asked to be a local power at is avoided by the whole orbit of each
named place and not merely by the named place itself.  That is what the orbit sum needs: the order
of the assembled tensor at a conjugate of a named place is the conjugate of its order at the place,
so asking for a local power there would ask the value prescribed at the place to be trivial. -/
def HasOrbitPrescribedUnits (ℓ : ℕ) [NeZero ℓ] (K : IntermediateField k Ω) [NumberField ↥K] :
    Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ (ι : Type) [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K)),
      (∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν) →
      ∀ Tz : Finset (HeightOneSpectrum (𝓞 ↥K)),
        (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ∉ Tz) →
        (∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal) →
        (∀ μ : ι, IsReachablePlace ℓ K E (w μ)) →
        ∃ Z : ι → (↥K)ˣ,
          (∀ μ : ι, ¬ (ℓ : ℤ) ∣ placeValue (w μ) (Z μ)) ∧
          (∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → localClassHom v ℓ (Z μ) = 1) ∧
          (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ≠ w μ → localClassHom (σ • w μ) ℓ (Z μ) = 1) ∧
          (∀ μ ν : ι, ν ≠ μ → ∀ σ : Gal(↥K/k), localClassHom (σ • w ν) ℓ (Z μ) = 1) ∧
          ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), ¬ (ℓ : ℤ) ∣ placeValue v (Z μ) →
            (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
              ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
                stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup

/-- **A family of units of a level can be found whose tensor against a named basis of a target
killed by the exponent is invariant, of prescribed order at each of finitely many named places whose
stabilizer has order prime to the exponent, a local power at a prescribed finite set of places the
orbits of those avoid, and confined elsewhere.**

This is the invariant tensor demand restricted to named places at which the automorphisms of the
level act tamely.  The restriction is exactly what turns a value fixed by the subgroup fixing a
place into a norm from that subgroup: raised to the power inverse to the order of the subgroup, a
fixed value is the norm of its own power. -/
def HasTameInvariantUnitTensor (ℓ : ℕ) [NeZero ℓ] (K : IntermediateField k Ω) [NumberField ↥K] :
    Prop :=
  ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E →
    ∀ (M : Type) [CommGroup M] [MulDistribMulAction Gal(↥K/k) M], (∀ m : M, m ^ ℓ = 1) →
      ∀ (T : Type) [Fintype T] (b : T → M),
        (∀ m : M, ∃ d : T → ZMod ℓ, ∏ q, b q ^ (d q).val = m) →
        (∀ d : T → ZMod ℓ, ∏ q, b q ^ (d q).val = 1 → d = 0) →
        ∀ (ι : Type) [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K)) (V : ι → M),
          (∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν) →
          (∀ μ : ι, ¬ ℓ ∣ Nat.card ↥(stabilizer Gal(↥K/k) (w μ))) →
          (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ = w μ → σ • V μ = V μ) →
          ∀ Tz : Finset (HeightOneSpectrum (𝓞 ↥K)),
            (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ∉ Tz) →
            (∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal) →
            (∀ μ : ι, IsReachablePlace ℓ K E (w μ)) →
            ∃ z : T → (↥K)ˣ,
              (∀ σ : Gal(↥K/k),
                σ • (∑ q, Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (b q))
                  = ∑ q, Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (b q)) ∧
              (∀ μ : ι, ∏ q, b q ^ ((placeValue (w μ) (z q) : ZMod ℓ)).val = V μ) ∧
              (∀ (q : T) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz →
                localClassHom v ℓ (z q) = 1) ∧
              ∀ v : HeightOneSpectrum (𝓞 ↥K), (∃ q : T, ¬ (ℓ : ℤ) ∣ placeValue v (z q)) →
                (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
                  ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
                    Ideal.under (𝓞 ↥K) P = v.asIdeal →
                    stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup

end Demand

/-! ### The orbit sum -/

section Orbit

variable {ℓ : ℕ} [NeZero ℓ] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois k ↥K] [FiniteDimensional k ↥K]

/-- **Units asked for nothing equivariant assemble into an invariant tensor at the named places
whose stabilizer has order prime to the exponent.**

The tensor is the sum, over the named places and over all the automorphisms of the level, of the
conjugate of the unit belonging to the place against the conjugate of a chosen root of the value
prescribed there.  Invariance is a reindexing of that sum by translation.  Re-expanding each
conjugate root in the given basis presents the same tensor in the shape the demand asks for, the
unit attached to a basis vector being the product of the conjugate units raised to the coordinates
of the conjugate roots.

The order of the assembled tensor at a named place collects the contributions of the automorphisms
fixing that place and nothing else: at a conjugate of another named place, and at a proper conjugate
of the place itself, the units are local powers, so their orders are divisible by the exponent and
drop out.  What survives is the product of the conjugates of the root over the subgroup fixing the
place, raised to the order of the unit there, and the root is chosen to make that the prescribed
value — the tameness of the stabilizer being exactly what lets the prescribed value be divided by
the order of the subgroup. -/
theorem hasTameInvariantUnitTensor_of_hasOrbitPrescribedUnits (hℓ : ℓ.Prime)
    (h : HasOrbitPrescribedUnits ℓ K) : HasTameInvariantUnitTensor ℓ K := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  intro E hEfin hEgal hKE M _ _ hexp T _ b hspan _ ι _ w V hdist htame hVfix Tz hwTz hℓw hreach
  haveI : IsGalois k ↥E := hEgal
  -- the prescribed set of places, saturated under the automorphisms of the level
  obtain ⟨Tz', hTzle, hwTz'⟩ : ∃ Tz' : Finset (HeightOneSpectrum (𝓞 ↥K)),
      (∀ (σ : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → σ • v ∈ Tz') ∧
        ∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ∉ Tz' := by
    refine ⟨Finset.image (fun p : Gal(↥K/k) × HeightOneSpectrum (𝓞 ↥K) => p.1 • p.2)
      (Finset.univ ×ˢ Tz),
      fun σ v hv => Finset.mem_image.2 ⟨(σ, v), Finset.mem_product.2 ⟨Finset.mem_univ _, hv⟩, rfl⟩,
      ?_⟩
    intro μ σ hmem
    obtain ⟨⟨τ, v⟩, hmem', hτv⟩ := Finset.mem_image.1 hmem
    exact hwTz μ (τ⁻¹ * σ)
      (by rw [mul_smul, ← hτv, inv_smul_smul]; exact (Finset.mem_product.1 hmem').2)
  obtain ⟨Y, hYord, hYTz, hYconj, hYcross, hYconf⟩ :=
    h E hEfin hEgal hKE ι w hdist Tz' hwTz' hℓw hreach
  -- the subgroup fixing each named place, as a finite set of automorphisms
  obtain ⟨St, hStmem⟩ : ∃ St : ι → Finset Gal(↥K/k),
      ∀ (μ : ι) (σ : Gal(↥K/k)), σ ∈ St μ ↔ σ • w μ = w μ :=
    ⟨fun μ => Finset.univ.filter (fun σ => σ • w μ = w μ), fun μ σ => by simp⟩
  have hStcard : ∀ μ : ι, (((St μ).card : ℕ) : ZMod ℓ) ≠ 0 := by
    intro μ hcon
    refine htame μ ?_
    have hc : Nat.card ↥(stabilizer Gal(↥K/k) (w μ)) = (St μ).card := by
      rw [Nat.card_congr
        (Equiv.subtypeEquivRight (fun σ => (mem_stabilizer_iff.trans (hStmem μ σ).symm))),
        Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [hc]
    exact (ZMod.natCast_eq_zero_iff _ _).1 hcon
  have hocast : ∀ μ : ι, ((placeValue (w μ) (Y μ) : ℤ) : ZMod ℓ) ≠ 0 := by
    intro μ hcon
    exact hYord μ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).1 hcon)
  -- the root of the prescribed value which the orbit sum takes its norm of
  have hfin : ∀ (X : M) (a : ZMod ℓ) (i j : ℕ),
      a * ((i : ZMod ℓ) * (j : ZMod ℓ)) = 1 → ((X ^ a.val) ^ i) ^ j = X := by
    intro X a i j hij
    rw [← pow_mul, ← pow_mul]
    have hc : ((a.val * (i * j) : ℕ) : ZMod ℓ) = ((1 : ℕ) : ZMod ℓ) := by
      rw [Nat.cast_mul, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
      exact hij
    exact (pow_eq_pow_of_pow_eq_one (hexp X) hc).trans (pow_one X)
  obtain ⟨V₀, hV₀norm⟩ : ∃ V₀ : ι → M, ∀ μ : ι,
      (∏ σ ∈ St μ, σ • V₀ μ) ^ (((placeValue (w μ) (Y μ) : ℤ) : ZMod ℓ)).val = V μ := by
    refine ⟨fun μ => V μ ^ ((((St μ).card : ZMod ℓ) *
      ((placeValue (w μ) (Y μ) : ℤ) : ZMod ℓ))⁻¹).val, fun μ => ?_⟩
    have hcong : ∀ σ ∈ St μ, σ • (V μ ^ ((((St μ).card : ZMod ℓ) *
        ((placeValue (w μ) (Y μ) : ℤ) : ZMod ℓ))⁻¹).val)
          = V μ ^ ((((St μ).card : ZMod ℓ) *
            ((placeValue (w μ) (Y μ) : ℤ) : ZMod ℓ))⁻¹).val := by
      intro σ hσ
      rw [smul_pow', hVfix μ σ ((hStmem μ σ).1 hσ)]
    rw [Finset.prod_congr rfl hcong, Finset.prod_const]
    refine hfin (V μ) _ _ _ ?_
    rw [ZMod.natCast_zmod_val]
    exact inv_mul_cancel₀ (mul_ne_zero (hStcard μ) (hocast μ))
  -- the coordinates of every conjugate of every root
  choose d hd using fun (μ : ι) (σ : Gal(↥K/k)) => hspan (σ • V₀ μ)
  obtain ⟨z, hzdef⟩ : ∃ z : T → (↥K)ˣ,
      ∀ q : T, z q = ∏ μ : ι, ∏ σ : Gal(↥K/k), (σ • Y μ) ^ (d μ σ q).val :=
    ⟨_, fun _ => rfl⟩
  -- the order of the assembled units at an arbitrary place
  have hpv : ∀ (q : T) (v : HeightOneSpectrum (𝓞 ↥K)),
      placeValue v (z q)
        = ∑ ν : ι, ∑ σ : Gal(↥K/k), ((d ν σ q).val : ℤ) * placeValue (σ⁻¹ • v) (Y ν) := by
    intro q v
    rw [hzdef q, placeValue_prod_eq_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [placeValue_prod_eq_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [placeValue_pow, placeValue_smul_unit]
  -- the assembled tensor, read back as the orbit sum
  have hA : (∑ q, Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (b q)
        : Additive (↥K)ˣ ⊗[ℤ] Additive M)
      = ∑ ν : ι, ∑ σ : Gal(↥K/k),
          Additive.ofMul (σ • Y ν) ⊗ₜ[ℤ] Additive.ofMul (σ • V₀ ν) := by
    have hkey : ∀ (x : (↥K)ˣ) (y : M) (n : ℕ),
        (Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul (y ^ n) : Additive (↥K)ˣ ⊗[ℤ] Additive M)
          = Additive.ofMul (x ^ n) ⊗ₜ[ℤ] Additive.ofMul y := by
      intro x y n
      rw [← zpow_natCast y n, ← zpow_natCast x n, _root_.ofMul_zpow, _root_.ofMul_zpow]
      exact (TensorProduct.smul_tmul (R := ℤ) (n : ℤ) (Additive.ofMul x) (Additive.ofMul y)).symm
    have hr : ∀ (ν : ι) (σ : Gal(↥K/k)),
        (Additive.ofMul (σ • Y ν) ⊗ₜ[ℤ] Additive.ofMul (σ • V₀ ν)
            : Additive (↥K)ˣ ⊗[ℤ] Additive M)
          = ∑ q, Additive.ofMul ((σ • Y ν) ^ (d ν σ q).val) ⊗ₜ[ℤ] Additive.ofMul (b q) := by
      intro ν σ
      rw [← hd ν σ, _root_.ofMul_prod, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun q _ => hkey _ _ _
    have hl : ∀ q : T,
        (Additive.ofMul (z q) ⊗ₜ[ℤ] Additive.ofMul (b q) : Additive (↥K)ˣ ⊗[ℤ] Additive M)
          = ∑ ν : ι, ∑ σ : Gal(↥K/k),
              Additive.ofMul ((σ • Y ν) ^ (d ν σ q).val) ⊗ₜ[ℤ] Additive.ofMul (b q) := by
      intro q
      rw [hzdef q]
      simp only [_root_.ofMul_prod]
      rw [TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun ν _ => TensorProduct.sum_tmul _ _ _
    rw [Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => hl q,
      Finset.sum_congr rfl fun ν (_ : ν ∈ Finset.univ) =>
        Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => hr ν σ, Finset.sum_comm]
    exact Finset.sum_congr rfl fun ν _ => Finset.sum_comm
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · -- invariance, by translating the orbit sum
    intro ρ
    rw [hA, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.smul_sum]
    have hT : ∀ σ : Gal(↥K/k),
        ρ • (Additive.ofMul (σ • Y ν) ⊗ₜ[ℤ] Additive.ofMul (σ • V₀ ν)
              : Additive (↥K)ˣ ⊗[ℤ] Additive M)
          = Additive.ofMul ((ρ * σ) • Y ν) ⊗ₜ[ℤ] Additive.ofMul ((ρ * σ) • V₀ ν) := by
      intro σ
      rw [tensorSMul_tmul, mul_smul, mul_smul]
    rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => hT σ]
    exact Fintype.sum_equiv (Equiv.mulLeft ρ) _ _ fun σ => rfl
  · -- the value prescribed at each named place
    intro μ
    have hA' : ∀ (ν : ι) (σ : Gal(↥K/k)), ν ≠ μ ∨ σ ∉ St μ →
        (σ • V₀ ν) ^ (placeValue (σ⁻¹ • w μ) (Y ν)) = 1 := by
      intro ν σ hcase
      refine zpow_eq_one_of_pow_eq_one (hexp _) (dvd_placeValue_of_localClassHom_eq_one ?_)
      by_cases hνμ : ν = μ
      · subst hνμ
        refine hYconj ν σ⁻¹ fun hcon => ?_
        rcases hcase with hcase | hcase
        · exact hcase rfl
        · exact hcase ((hStmem ν σ).2 (inv_smul_eq_iff.1 hcon).symm)
      · exact hYcross ν μ (fun hcon => hνμ hcon.symm) σ⁻¹
    have hstep : ∀ q : T, b q ^ (((placeValue (w μ) (z q) : ℤ) : ZMod ℓ)).val
        = ∏ ν : ι, ∏ σ : Gal(↥K/k),
            (b q ^ (d ν σ q).val) ^ (placeValue (σ⁻¹ • w μ) (Y ν)) := by
      intro q
      rw [← zpow_eq_pow_val (hexp (b q)), hpv q (w μ), zpow_finset_sum]
      refine Finset.prod_congr rfl fun ν _ => ?_
      rw [zpow_finset_sum]
      refine Finset.prod_congr rfl fun σ _ => ?_
      rw [zpow_mul, zpow_natCast]
    rw [Finset.prod_congr rfl fun q (_ : q ∈ Finset.univ) => hstep q, Finset.prod_comm]
    have hinner : ∀ ν : ι, (∏ q : T, ∏ σ : Gal(↥K/k),
        (b q ^ (d ν σ q).val) ^ (placeValue (σ⁻¹ • w μ) (Y ν)))
          = ∏ σ : Gal(↥K/k), (σ • V₀ ν) ^ (placeValue (σ⁻¹ • w μ) (Y ν)) := by
      intro ν
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun σ _ => ?_
      rw [finset_prod_zpow, hd ν σ]
    rw [Finset.prod_congr rfl fun ν (_ : ν ∈ Finset.univ) => hinner ν,
      Finset.prod_eq_single_of_mem μ (Finset.mem_univ μ)
        (fun ν _ hν => Finset.prod_eq_one fun σ _ => hA' ν σ (Or.inl hν)),
      ← Finset.prod_subset (Finset.subset_univ (St μ))
        (fun σ _ hσ => hA' μ σ (Or.inr hσ))]
    have hfixed : ∀ σ ∈ St μ, (σ • V₀ μ) ^ (placeValue (σ⁻¹ • w μ) (Y μ))
        = (σ • V₀ μ) ^ (((placeValue (w μ) (Y μ) : ℤ) : ZMod ℓ)).val := by
      intro σ hσ
      rw [show σ⁻¹ • w μ = w μ from inv_smul_eq_iff.2 ((hStmem μ σ).1 hσ).symm,
        zpow_eq_pow_val (hexp _)]
    rw [Finset.prod_congr rfl hfixed, Finset.prod_pow]
    exact hV₀norm μ
  · -- the assembled units are local powers on the prescribed set
    intro q v hv
    rw [hzdef q, _root_.map_prod]
    refine Finset.prod_eq_one fun ν _ => ?_
    rw [_root_.map_prod]
    refine Finset.prod_eq_one fun σ _ => ?_
    rw [_root_.map_pow, localClassHom_smul_eq_one σ v ℓ (Y ν)
      (hYTz ν (σ⁻¹ • v) (hTzle σ⁻¹ v hv)), one_pow]
  · -- the remaining ramification is confined
    rintro v ⟨q, hq⟩
    have hex : ∃ (ν : ι) (σ : Gal(↥K/k)), ¬ (ℓ : ℤ) ∣ placeValue (σ⁻¹ • v) (Y ν) := by
      by_contra hcon
      push_neg at hcon
      refine hq ?_
      rw [hpv q v]
      exact Finset.dvd_sum fun ν _ => Finset.dvd_sum fun σ _ => (hcon ν σ).mul_left _
    obtain ⟨ν, σ, hνσ⟩ := hex
    rcases hYconf ν (σ⁻¹ • v) hνσ with ⟨ρ, τ, hρτ⟩ | hdec
    · exact Or.inl ⟨ρ, σ * τ, by rw [mul_smul, ← hρτ, smul_inv_smul]⟩
    · refine Or.inr ?_
      have hmov := forall_stabilizer_le_fixingSubgroup_smul (E := E) σ hdec
      rwa [smul_inv_smul] at hmov

omit [IsGalois k Ω] [IsGalois k ↥K] [FiniteDimensional k ↥K] in
/-- **A level all of whose places have stabilizer of order prime to the exponent carries the
unrestricted invariant tensor demand.** -/
theorem hasInvariantUnitTensor_of_hasTameInvariantUnitTensor
    (htame : ∀ v : HeightOneSpectrum (𝓞 ↥K), ¬ ℓ ∣ Nat.card ↥(stabilizer Gal(↥K/k) v))
    (h : HasTameInvariantUnitTensor ℓ K) : HasInvariantUnitTensor ℓ K := by
  intro E hEfin hEgal hKE M _ _ hexp T _ b hspan hindep ι _ w V hdist
  exact h E hEfin hEgal hKE M hexp T b hspan hindep ι w V hdist fun μ => htame (w μ)

end Orbit

end InverseGalois.Shafarevich

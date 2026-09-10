/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CharPlace
import InverseGalois.CFT.Profinite.KummerLevel
import InverseGalois.CFT.Units.InfiniteDecomposition
import InverseGalois.Solvable.Shafarevich.CharacterProduct
import InverseGalois.Solvable.Shafarevich.ElementaryQuotientDecomposition
import InverseGalois.Solvable.Shafarevich.LayerPi

/-!
# The character of the first rung built out of a family of units

The first rung of the ladder asks for a character of the kernel of the base map with values in the
first layer, jointly onto with its conjugates, killed on an open normal subgroup and on the
prescribed family of subgroups, and ramifying only where the rung permits.  What the arithmetic
supplies is a family of units of a finite level, one for each element of the layer, each of which
is a local power everywhere except at two places of its own, is a local power at every conjugate of
those two places, and is a local power at both places belonging to any other member of the family.
This file turns such a family into the character the rung asks for.

The dictionary is Kummer theory over the level.  Adjoining an `ℓ`-th root of a unit to the algebraic
closure gives a character of the automorphisms over the level with values in the cyclic group of
order `ℓ`, and the arithmetic of the unit is exactly the arithmetic of that character: the character
vanishes on the inertia at a prime where the unit has valuation divisible by `ℓ`, and vanishes on
the whole decomposition subgroup at a prime where the unit is a local power.  Reading the family of
units as a family of characters and multiplying the corresponding powers of the layer produces the
character of the rung, and each of the three clauses becomes a statement about one place at a time.

Generation is where the two places of each unit are used.  A unit that is not a local power at the
first of its places has a nonvanishing character somewhere in the decomposition subgroup there, and
a power of that automorphism realises the value one; every other unit is a local power at the same
place, so all the other coordinates vanish there, and the corresponding element of the layer is
obtained on the nose.  A conjugate the base map moves carries the place to a different one, where
every coordinate is a local power, so all the conjugates the generation clause has to discard do in
fact vanish.  Ramification runs the same argument backwards: a prime where the character survives is
a prime where some coordinate survives on inertia, so the unit of that coordinate is not a local
power there and the place below it must be one of the two attached to it — whereupon the other
coordinates and the other cosets vanish for the same reason as before.

## Main definitions

* `InverseGalois.Shafarevich.placeUnder` — the place of a level below a nonzero prime of the
  integers of the whole extension.

## Main results

* `InverseGalois.Shafarevich.mem_inertia_galSubHom_iff` — inertia is read the same way over the
  base field and over a level.
* `InverseGalois.Shafarevich.hasLevelOneCharacter_of_places` — **a family of units of a level, each
  failing to be a local power at exactly one place of its own and a local power at every place
  attached to any other member and at every proper conjugate of its own, gives the first rung of
  the ladder its character.**

## Tags

Shafarevich's theorem, embedding problem, Frattini layer, Kummer theory, ramification, character
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField Rigidity.RET

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### Conjugating a prime -/

section Conj

variable {G R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]

/-- A conjugate of an element of the inertia at a prime lies in the inertia at the corresponding
conjugate of the prime. -/
theorem mem_inertia_conj {P : Ideal R} {x : G} (hx : x ∈ Ideal.inertia G P) (g : G) :
    g * x * g⁻¹ ∈ Ideal.inertia G (g • P) := by
  refine AddSubgroup.mem_inertia.2 fun a => ?_
  show (g * x * g⁻¹) • a - a ∈ g • P
  refine Ideal.mem_pointwise_smul_iff_inv_smul_mem.2 ?_
  rw [smul_sub, smul_smul, show g⁻¹ * (g * x * g⁻¹) = x * g⁻¹ by group, mul_smul]
  exact AddSubgroup.mem_inertia.1 hx (g⁻¹ • a)

end Conj

section Stab

variable {G α : Type*} [Group G] [MulAction G α]

/-- A conjugate of an element of a stabiliser stabilises the corresponding translate. -/
theorem mem_stabilizer_conj {P : α} {x : G} (hx : x ∈ stabilizer G P) (g : G) :
    g * x * g⁻¹ ∈ stabilizer G (g • P) := by
  rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, mem_stabilizer_iff.1 hx]

end Stab

/-! ### Reading an automorphism over a level -/

section Bridge

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)

/-- An automorphism over a level acts on the integers of the whole extension the way it does read
over the base field. -/
theorem smul_ringOfIntegers_galSubHom (τ : Gal(Ω/↥K)) (b : 𝓞 Ω) :
    galSubHom K τ • b = τ • b := Subtype.ext rfl

/-- An automorphism over a level acts on the units of the whole extension the way it does read over
the base field. -/
theorem smul_units_galSubHom (τ : Gal(Ω/↥K)) (β : Ωˣ) : galSubHom K τ • β = τ • β :=
  Units.ext rfl

/-- Inertia at a prime is read the same way over the base field and over a level. -/
theorem mem_inertia_galSubHom_iff (τ : Gal(Ω/↥K)) (P : Ideal (𝓞 Ω)) :
    galSubHom K τ ∈ Ideal.inertia Gal(Ω/k) P ↔ τ ∈ Ideal.inertia Gal(Ω/↥K) P := by
  simp only [AddSubgroup.mem_inertia]
  exact forall_congr' fun b => by rw [smul_ringOfIntegers_galSubHom]

end Bridge

/-! ### The place below a prime -/

section Under

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
  [NumberField ↥K]

/-- The place of a level below a nonzero prime of the integers of the whole extension. -/
def placeUnder (P : Ideal (𝓞 Ω)) [P.IsPrime] (hP : P ≠ ⊥) : HeightOneSpectrum (𝓞 ↥K) where
  asIdeal := Ideal.under (𝓞 ↥K) P
  isPrime := Ideal.IsPrime.under _ P
  ne_bot := Ideal.under_ne_bot _ hP

omit [NumberField ↥K] in
@[simp]
theorem placeUnder_asIdeal (P : Ideal (𝓞 Ω)) [P.IsPrime] (hP : P ≠ ⊥) :
    (placeUnder K P hP).asIdeal = Ideal.under (𝓞 ↥K) P := rfl

end Under

/-! ### The character of the first rung -/

section Arith

variable {ℓ : ℕ} {U S : Type} [Group U] [Finite U] [Group S] [Finite S]
  {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [IsGalois k Ω]

attribute [local instance] zmodTrivialAction

/-- **A family of units of a level, each failing to be a local power at exactly one place of its
own and a local power at every place attached to any other member and at every proper conjugate of
its own, gives the first rung of the ladder its character.** -/
theorem hasLevelOneCharacter_of_places (hℓ : ℓ.Prime) (n : ℕ) {φ : Gal(Ω/k) →* U}
    (hsurj : Function.Surjective φ) (Tf : Set (Subgroup Gal(Ω/k)))
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [NumberField ↥K] [IsGalois k ↥K]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hmu : ∀ y : Ωˣ, y ^ (ℓ * ℓ) = 1 → ∀ σ ∈ φ.ker, σ • y = y)
    (Q R : ↥(layerSub ℓ (Generic U n S) 0) → HeightOneSpectrum (𝓞 ↥K))
    (z : ↥(layerSub ℓ (Generic U n S) 0) → (↥K)ˣ)
    (hpz : ∀ i, ∀ w : HeightOneSpectrum (𝓞 ↥K), (ℓ : 𝓞 ↥K) ∈ w.asIdeal →
      localClassHom w ℓ (z i) = 1)
    (hunram : ∀ i, ∀ w : HeightOneSpectrum (𝓞 ↥K), w ≠ Q i → w ≠ R i →
      (ℓ : ℤ) ∣ placeValue w (z i))
    (hramQ : ∀ i, ¬ (ℓ : ℤ) ∣ placeValue (Q i) (z i))
    (hconjQ : ∀ i, ∀ σ : Gal(↥K/k), σ ≠ 1 → localClassHom (σ • Q i) ℓ (z i) = 1)
    (hconjR : ∀ i, ∀ σ : Gal(↥K/k), σ ≠ 1 → localClassHom (σ • R i) ℓ (z i) = 1)
    (hcrossQ : ∀ i j, i ≠ j → ∀ σ : Gal(↥K/k), localClassHom (σ • Q j) ℓ (z i) = 1)
    (hcrossR : ∀ i j, i ≠ j → ∀ σ : Gal(↥K/k), localClassHom (σ • R j) ℓ (z i) = 1)
    (hstabQ : ∀ i, stabilizer Gal(↥K/k) (Q i) = ⊥)
    (hstabR : ∀ i, stabilizer Gal(↥K/k) (R i) = ⊥)
    (hTf : ∀ D ∈ Tf, ∀ x ∈ D, φ x = 1 → ∀ (g : Gal(Ω/k)) (i) (β : Ωˣ),
      β ^ ℓ = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (z i) → (g⁻¹ * x * g) • β = β) :
    HasLevelOneCharacter ℓ U S φ Tf n := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype ↥(layerSub ℓ (Generic U n S) 0) := Fintype.ofFinite _
  haveI : IsGalois ↥K Ω := IsGalois.tower_top_of_isGalois k ↥K Ω
  obtain ⟨r, hr⟩ := hsurj.hasRightInverse
  -- the Kummer data over the level
  have hroot : ∀ a : (↥K)ˣ, ∃ β : Ωˣ, β ^ ℓ = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a := by
    intro a
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ↥K Ω (a : ↥K)) hℓ.pos
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, zero_pow hℓ.ne_zero] at hx
      exact (map_ne_zero_iff _ (algebraMap ↥K Ω).injective).2 a.ne_zero hx.symm
    refine ⟨Units.mk0 x hx0, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.coe_map]
    exact hx
  have hkd : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ :=
    isKummerData_zmod hζ hroot
  -- reading an element of the kernel as an automorphism over the level
  set eK : ↥φ.ker ≃* Gal(Ω/↥K) :=
    (MulEquiv.subgroupCongr hKker).symm.trans (IntermediateField.fixingSubgroupEquiv K) with heK
  have hge : ∀ y : ↥φ.ker, galSubHom K (eK y) = (y : Gal(Ω/k)) := by
    intro y
    rw [heK]
    rw [show ((MulEquiv.subgroupCongr hKker).symm.trans
        (IntermediateField.fixingSubgroupEquiv K)) y
        = IntermediateField.fixingSubgroupEquiv K ((MulEquiv.subgroupCongr hKker).symm y) from rfl,
      ← coe_fixingSubgroupEquiv_symm, (IntermediateField.fixingSubgroupEquiv K).symm_apply_apply]
    rfl
  -- the coordinates of the character
  obtain ⟨f, hfdef⟩ : ∃ f : ↥(layerSub ℓ (Generic U n S) 0) → ↥φ.ker → ZMod ℓ,
      f = fun i y => kummerChar hkd (z i) (eK y) := ⟨_, rfl⟩
  have hf : ∀ i, ∀ x y : ↥φ.ker, f i (x * y) = f i x + f i y := by
    intro i x y
    simp only [hfdef]
    rw [_root_.map_mul eK, kummerChar_mul]
  have hvpow : ∀ i : ↥(layerSub ℓ (Generic U n S) 0), i ^ ℓ = 1 :=
    fun i => layerSub_pow_eq_one ℓ (Generic U n S) 0 i
  -- the restriction to the level
  have hρker : ∀ y : Gal(Ω/k), AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K y = 1 →
      φ y = 1 := by
    intro y hy
    have hmem : y ∈ (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K).ker :=
      MonoidHom.mem_ker.2 hy
    rw [IntermediateField.restrictNormalHom_ker, hKker] at hmem
    exact hmem
  -- the local behaviour of the coordinates at the two places attached to a member of the family
  have hgood : ∀ (i : ↥(layerSub ℓ (Generic U n S) 0)) (w : HeightOneSpectrum (𝓞 ↥K)),
      (w = Q i ∨ w = R i) →
      (∀ σ : Gal(↥K/k), σ • w.asIdeal = w.asIdeal → σ = 1) ∧
      (∀ (σ : Gal(↥K/k)) (j), (σ ≠ 1 ∨ j ≠ i) → localClassHom (σ • w) ℓ (z j) = 1) := by
    intro i w hw
    constructor
    · intro σ hσ
      have hmem : σ ∈ stabilizer Gal(↥K/k) w :=
        HeightOneSpectrum.ext (by rw [asIdeal_smul]; exact hσ)
      rcases hw with rfl | rfl
      · rw [hstabQ i] at hmem; exact hmem
      · rw [hstabR i] at hmem; exact hmem
    · intro σ j hcase
      by_cases hji : j = i
      · subst hji
        have hσ1 : σ ≠ 1 := by
          rcases hcase with h | h
          · exact h
          · exact absurd rfl h
        rcases hw with rfl | rfl
        · exact hconjQ j σ hσ1
        · exact hconjR j σ hσ1
      · rcases hw with rfl | rfl
        · exact hcrossQ j i hji σ
        · exact hcrossR j i hji σ
  -- a prime of the closure above the first of the two places attached to each member
  have hPex : ∀ i : ↥(layerSub ℓ (Generic U n S) 0), ∃ P : Ideal (𝓞 Ω), ∃ _ : P.IsPrime,
      P ≠ ⊥ ∧ Ideal.under (𝓞 ↥K) P = (Q i).asIdeal := by
    intro i
    haveI := (Q i).isPrime
    obtain ⟨P, -, hPp, hPu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (R := 𝓞 ↥K) (S := 𝓞 Ω) (Q i).asIdeal ⊥ (by simp)
    refine ⟨P, hPp, ?_, hPu⟩
    intro h
    refine (Q i).ne_bot ?_
    rw [← hPu, h, ← RingHom.ker_eq_comap_bot, RingOfIntegers.ker_algebraMap_eq_bot]
  choose P hPp hPbot hPu using hPex
  -- the roots of the chosen units, and a finite Galois level containing them
  obtain ⟨rts, hrts⟩ : ∃ rts : Set Ω, rts = Set.range fun i : ↥(layerSub ℓ (Generic U n S) 0) =>
      ((hkd.root (z i) : Ωˣ) : Ω) := ⟨_, rfl⟩
  haveI : Finite ↥rts := by rw [hrts]; exact (Set.finite_range _).to_subtype
  haveI : FiniteDimensional k ↥(IntermediateField.adjoin k rts) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional k
      ↥(normalClosure k ↥(K ⊔ IntermediateField.adjoin k rts) Ω) := inferInstance
  haveI : Normal k ↥(normalClosure k ↥(K ⊔ IntermediateField.adjoin k rts) Ω) := inferInstance
  have hKle : K ≤ normalClosure k ↥(K ⊔ IntermediateField.adjoin k rts) Ω :=
    le_trans le_sup_left (IntermediateField.le_normalClosure _)
  have hWle : (normalClosure k ↥(K ⊔ IntermediateField.adjoin k rts) Ω).fixingSubgroup
      ≤ φ.ker := by
    rw [← hKker]
    exact IntermediateField.fixingSubgroup_le hKle
  have hrle : rts ⊆ (normalClosure k ↥(K ⊔ IntermediateField.adjoin k rts) Ω : Set Ω) := by
    intro x hx
    exact le_trans le_sup_right (IntermediateField.le_normalClosure _)
      (IntermediateField.subset_adjoin k rts hx)
  refine ⟨r, hr, charProd id hvpow f hf,
    (normalClosure k ↥(K ⊔ IntermediateField.adjoin k rts) Ω).fixingSubgroup, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- generation
    refine inducedNorm_surjective_of_charProd φ r hr hvpow hf ?_
      (fun i => (stabilizer Gal(Ω/↥K) (P i)).comap eK.toMonoidHom) ?_ ?_
    · rw [Set.range_id', Subgroup.closure_univ]
    · intro i
      haveI := hPp i
      have hQi : localClassHom (Q i) ℓ (z i) ≠ 1 := fun hcon =>
        hramQ i (dvd_placeValue_of_localClassHom_eq_one hcon)
      obtain ⟨σ, hσst, hσne⟩ :=
        exists_mem_stabilizer_kummerChar_ne_zero hkd (hPu i).symm hQi
      have hcast : ((((kummerChar hkd (z i) σ)⁻¹ : ZMod ℓ).val : ℕ) : ZMod ℓ)
          = (kummerChar hkd (z i) σ)⁻¹ := ZMod.natCast_rightInverse _
      refine ⟨eK.symm (σ ^ ((kummerChar hkd (z i) σ)⁻¹ : ZMod ℓ).val), ?_, ?_, ?_⟩
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        exact Subgroup.pow_mem _ hσst _
      · simp only [hfdef, MulEquiv.apply_symm_apply]
        rw [kummerChar_pow, nsmul_eq_mul, hcast, inv_mul_cancel₀ hσne, ZMod.val_one]
      · intro j hj
        simp only [hfdef, MulEquiv.apply_symm_apply]
        refine kummerChar_eq_zero_of_mem_stabilizer hkd (hPu i).symm ?_
          (Subgroup.pow_mem _ hσst _)
        have h1 := (hgood i (Q i) (Or.inl rfl)).2 1 j (Or.inr hj)
        rwa [one_smul] at h1
    · intro g hg i y hy j
      haveI := hPp i
      have hρg : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g ≠ 1 := fun h0 =>
        hg (hρker g h0)
      have hy' : eK y ∈ stabilizer Gal(Ω/↥K) (P i) := hy
      have hyst : (y : Gal(Ω/k)) ∈ stabilizer Gal(Ω/k) (P i) := by
        rw [← hge y, mem_stabilizer_galSubHom_iff]
        exact hy'
      have hmem : eK (MulAut.conjNormal g y) ∈ stabilizer Gal(Ω/↥K) (g • P i) := by
        rw [← mem_stabilizer_galSubHom_iff, hge, MulAut.conjNormal_apply]
        exact mem_stabilizer_conj hyst g
      have hv : (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K g • Q i).asIdeal
          = Ideal.under (𝓞 ↥K) (g • P i) := by
        rw [asIdeal_smul, under_smul_ringOfIntegers ↥K, hPu i]
      simp only [hfdef]
      exact kummerChar_eq_zero_of_mem_stabilizer hkd hv
        ((hgood i (Q i) (Or.inl rfl)).2 _ j (Or.inl hρg)) hmem
  · exact isOpenNormal_fixingSubgroup _
  · -- the level lies in the kernel of the base map
    exact hWle
  · -- the level kills the character
    intro y hy
    refine (mem_inducedCharKer _ _).2 ⟨hWle hy, charProd_eq_one fun i => ?_⟩
    simp only [hfdef]
    refine (kummerChar_eq_zero_iff_smul_root_eq hkd (z i) _).2 (Units.ext ?_)
    show (y : Gal(Ω/k)) ((hkd.root (z i) : Ωˣ) : Ω) = ((hkd.root (z i) : Ωˣ) : Ω)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hy _
      (hrle (by rw [hrts]; exact ⟨i, rfl⟩))
  · -- triviality along the prescribed family
    intro D hD x hx hφ u
    have hker : (r u)⁻¹ * x * r u ∈ φ.ker := by
      rw [MonoidHom.mem_ker, _root_.map_mul, _root_.map_mul, _root_.map_inv, hφ, hr, mul_one,
        inv_mul_cancel]
    refine (mem_inducedCharKer _ _).2 ⟨hker, charProd_eq_one fun i => ?_⟩
    simp only [hfdef]
    refine (kummerChar_eq_zero_iff_smul_root_eq hkd (z i) _).2 ?_
    rw [← smul_units_galSubHom K, hge]
    exact hTf D hD x hx hφ (r u) i _ (hkd.root_pow (z i))
  · -- the ramification restriction
    refine isSplitTotallyRamifiedHom_inducedHom_charProd hℓ φ r hr hvpow hf hvpow ?_
    intro P₀ hP₀p hP₀bot x hxI hxφ hxΦ
    haveI := hP₀p
    obtain ⟨u₀, hu₀⟩ := exists_inducedCocycle_ne_one φ r _ hr hxφ hxΦ
    rw [inducedCocycle_apply] at hu₀
    have hi₀ : ∃ i₀, f i₀ ⟨cocycleArg φ r x u₀, cocycleArg_mem φ r hr x u₀⟩ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hu₀ (charProd_eq_one hcon)
    obtain ⟨i₀, hi₀ne⟩ := hi₀
    have hi₀char : kummerChar hkd (z i₀)
        (eK ⟨cocycleArg φ r x u₀, cocycleArg_mem φ r hr x u₀⟩) ≠ 0 := by
      simpa only [hfdef] using hi₀ne
    set P₁ : Ideal (𝓞 Ω) := (r u₀)⁻¹ • P₀ with hP₁def
    haveI : P₁.IsPrime := by rw [hP₁def]; infer_instance
    have hP₀eq : P₀ = r u₀ • P₁ := by rw [hP₁def, smul_inv_smul]
    have hP₁bot : P₁ ≠ ⊥ := by
      intro h0
      refine hP₀bot ?_
      rw [hP₀eq, h0, Ideal.smul_bot]
    obtain ⟨w₁, hw₁under⟩ : ∃ w₁ : HeightOneSpectrum (𝓞 ↥K),
        w₁.asIdeal = Ideal.under (𝓞 ↥K) P₁ := ⟨placeUnder K P₁ hP₁bot, rfl⟩
    have hx₁I : cocycleArg φ r x u₀ ∈ Ideal.inertia Gal(Ω/k) P₁ := by
      rw [cocycleArg_of_mem_ker φ r hxφ u₀, hP₁def]
      have h := mem_inertia_conj hxI (r u₀)⁻¹
      rwa [inv_inv] at h
    have hτ₁ : eK ⟨cocycleArg φ r x u₀, cocycleArg_mem φ r hr x u₀⟩ ∈
        Ideal.inertia Gal(Ω/↥K) P₁ := by
      rw [← mem_inertia_galSubHom_iff, hge]
      exact hx₁I
    have hℓnotin : (ℓ : 𝓞 ↥K) ∉ w₁.asIdeal := fun hin =>
      hi₀char (kummerChar_eq_zero_of_mem_stabilizer hkd hw₁under (hpz i₀ w₁ hin)
        (Ideal.inertia_le_stabilizer P₁ hτ₁))
    have hℓnotinΩ : (ℓ : 𝓞 Ω) ∉ P₁ := by
      intro hin
      refine hℓnotin ?_
      rw [hw₁under, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hin
    have hw₁mem : w₁ = Q i₀ ∨ w₁ = R i₀ := by
      by_contra hcon
      push_neg at hcon
      exact hi₀char (kummerChar_eq_zero_of_mem_inertia hkd hℓ hℓnotinΩ hw₁under
        (hunram i₀ w₁ hcon.1 hcon.2) hτ₁)
    obtain ⟨hstab₁, hloc₁⟩ := hgood i₀ w₁ hw₁mem
    have hP₀under : Ideal.under (𝓞 ↥K) P₀
        = AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (r u₀) • w₁.asIdeal := by
      rw [hw₁under]
      conv_lhs => rw [hP₀eq]
      rw [under_smul_ringOfIntegers ↥K]
    have hunderu : ∀ u : U, Ideal.under (𝓞 ↥K) ((r u)⁻¹ • P₀)
        = ((AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (r u))⁻¹ *
            AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (r u₀)) • w₁.asIdeal := by
      intro u
      rw [under_smul_ringOfIntegers ↥K, hP₀under, _root_.map_inv, smul_smul]
    have hcl1 : ∀ y ∈ stabilizer Gal(Ω/k) P₀, φ y = 1 := by
      intro y hy
      refine hρker y ?_
      have hρy : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K y •
          Ideal.under (𝓞 ↥K) P₀ = Ideal.under (𝓞 ↥K) P₀ := by
        rw [← under_smul_ringOfIntegers ↥K, mem_stabilizer_iff.1 hy]
      rw [hP₀under, smul_smul] at hρy
      have h2 : ((AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (r u₀))⁻¹ *
          (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K y *
            AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (r u₀))) • w₁.asIdeal
          = w₁.asIdeal := by
        rw [← smul_smul, hρy, inv_smul_smul]
      have h3 : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (r u₀)
          = AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K y *
            AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (r u₀) :=
        inv_mul_eq_one.1 (hstab₁ _ h2)
      refine mul_right_cancel (b := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (r u₀)) ?_
      rw [one_mul]
      exact h3.symm
    have hkey : ∀ y ∈ stabilizer Gal(Ω/k) P₀, ∀ (u : U) (j), localClassHom
        (((AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (r u))⁻¹ *
          AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K (r u₀)) • w₁) ℓ (z j) = 1 →
        f j ⟨cocycleArg φ r y u, cocycleArg_mem φ r hr y u⟩ = 0 := by
      intro y hy u j hloc
      haveI : ((r u)⁻¹ • P₀).IsPrime := inferInstance
      have harg : cocycleArg φ r y u = (r u)⁻¹ * y * r u :=
        cocycleArg_of_mem_ker φ r (hcl1 y hy) u
      have hst : (r u)⁻¹ * y * r u ∈ stabilizer Gal(Ω/k) ((r u)⁻¹ • P₀) := by
        have h := mem_stabilizer_conj hy (r u)⁻¹
        rwa [inv_inv] at h
      have hmem : eK ⟨cocycleArg φ r y u, cocycleArg_mem φ r hr y u⟩ ∈
          stabilizer Gal(Ω/↥K) ((r u)⁻¹ • P₀) := by
        rw [← mem_stabilizer_galSubHom_iff, hge]
        show cocycleArg φ r y u ∈ _
        rw [harg]
        exact hst
      simp only [hfdef]
      exact kummerChar_eq_zero_of_mem_stabilizer hkd
        (by rw [asIdeal_smul, hunderu u]) hloc hmem
    refine ⟨u₀, i₀, hcl1, ?_, ?_, ?_⟩
    · intro y hy u hu j
      refine hkey y hy u j (hloc₁ _ j (Or.inl ?_))
      intro h0
      refine hu ?_
      have h1 : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ((r u)⁻¹ * r u₀) = 1 := by
        rw [_root_.map_mul, _root_.map_inv]
        exact h0
      have h2 : φ ((r u)⁻¹ * r u₀) = 1 := hρker _ h1
      rw [_root_.map_mul, _root_.map_inv, hr, hr] at h2
      exact inv_mul_eq_one.1 h2
    · intro y hy j hj
      refine hkey y hy u₀ j ?_
      rw [inv_mul_cancel]
      exact hloc₁ 1 j (Or.inr hj)
    · intro ξ hξ y hy
      exact hmu ξ hξ y (hcl1 y hy)

end Arith

end InverseGalois.Shafarevich

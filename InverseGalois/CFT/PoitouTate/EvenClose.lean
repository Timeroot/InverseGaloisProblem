/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.EvenChain
import InverseGalois.CFT.PoitouTate.EvenPigeonhole
import InverseGalois.CFT.PoitouTate.InvolutionClaim

/-!
# Closing the recursion at the exponent two: three places and one unit ramified at all three

A unit ramified at a single place is never trivial at the nontrivial conjugates of that place, since
its value at the Frobenius automorphism there is a nontrivial root of unity.  At an odd exponent a
product of two such units can be trivial there, because the prescription at the conjugates of the
first place may ask the second unit for the inverse of the class of the first.  At the exponent two
the inverse is the class itself, so that device is unavailable: the prescription can only ask for
the class or for nothing, and no product of two units cancels.

A product of three does.  The recursion is run with a prescription reading a rule which selects one
member of each pair formed by an automorphism and its inverse, and which alternates with the number
of intervening stages carrying the same invariant.  Three stages carrying a common invariant and
following one another then give three places and three units whose product is trivial at every
nontrivial conjugate of each of the three places: at each of the three orbits one of the three units
contributes the common value and the other two contribute it or nothing according as the
automorphism, respectively its inverse, is selected by the rule.  Exactly one of the two
contributions is made unless the automorphism is its own inverse, and there the common value is
itself trivial.

## Main results

* `InverseGalois.CFT.exists_prescribed_three_places`: **three places satisfying a given splitting
  condition, and a unit ramified exactly at those three places**, realising the cube of a
  prescribed local behaviour on a fixed Galois stable set of places and trivial at every nontrivial
  conjugate of the three.

## Tags

number field, place, local class, prescription, recursion, quadratic, involution
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### Three places, and a unit ramified exactly at the three of them -/

section Close

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **Three places satisfying a given splitting condition, and a unit ramified exactly at those
three places.**  The unit realises the cube of a prescribed local behaviour on a fixed Galois
stable set of places, is a local square at every infinite place, and is trivial at every nontrivial
conjugate of any of the three.  The recursion adding one place at a time is run past twice the size
of the finite set of invariants, so that three of its stages carry a common invariant and follow
one another; the unit is the product of the three units attached to those stages. -/
theorem exists_prescribed_three_places
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ 2) {Spl : HeightOneSpectrum (𝓞 K) → Prop}
    (hSpl : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), Spl v → Spl (σ • v))
    {B T S₀ : Finset (HeightOneSpectrum (𝓞 K))}
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hBT : B ⊆ T)
    (hBstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ B → σ • v ∈ B)
    (hBwild : ∀ v : HeightOneSpectrum (𝓞 K), Pc v ∣ 2 → v ∈ B)
    (hBram : ∀ v : HeightOneSpectrum (𝓞 K), ramIdx (𝓞 k) v ≠ 1 → v ∈ B)
    (hTS : T ⊆ S₀)
    (hSstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S₀ → σ • v ∈ S₀)
    (hSsplit : ∀ v ∈ S₀, v ∉ T → Spl v)
    {g : Kˣ} (hgunr : ∀ v ∈ T, localClassHom v 2 g ∈ localUnramified v 2)
    (hgB : ∀ v ∈ B, localClassHom v 2 g = 1)
    (hstep : ∀ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S₁ →
      (∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S₁ → σ • v ∈ S₁) →
      ∀ c : (v : HeightOneSpectrum (𝓞 K)) → localClasses v 2,
        (∀ v : HeightOneSpectrum (𝓞 K), c v ∈ localUnramified v 2) →
        (∀ v ∈ T, c v = localClassHom v 2 g) →
        (∀ v ∈ S₁, v ∉ T → Spl v) →
        ∃ Q : HeightOneSpectrum (𝓞 K), Q ∉ S₁ ∧ Spl Q ∧ stabilizer Gal(K/k) Q = ⊥ ∧
          ∃ w : Kˣ, (∀ v ∈ S₁, localClassHom v 2 w = c v) ∧
            (∀ u : InfinitePlace K, infClassHom u 2 w = 1) ∧
            (∀ v : HeightOneSpectrum (𝓞 K), v ≠ Q → (2 : ℤ) ∣ placeValue v w) ∧
            (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₁ → v ≠ Q → placeValue v w = 0) ∧
            ¬ (2 : ℤ) ∣ placeValue Q w) :
    ∃ Q R S : HeightOneSpectrum (𝓞 K), Q ∉ T ∧ R ∉ T ∧ S ∉ T ∧ Spl Q ∧ Spl R ∧ Spl S ∧
      (∀ σ : Gal(K/k), Q ≠ σ • R) ∧ (∀ σ : Gal(K/k), Q ≠ σ • S) ∧
      (∀ σ : Gal(K/k), R ≠ σ • S) ∧
      stabilizer Gal(K/k) Q = ⊥ ∧ stabilizer Gal(K/k) R = ⊥ ∧ stabilizer Gal(K/k) S = ⊥ ∧
      ∃ z : Kˣ, (∀ v ∈ T, localClassHom v 2 z = localClassHom v 2 (g ^ 3)) ∧
        (∀ u : InfinitePlace K, infClassHom u 2 z = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ≠ Q → v ≠ R → v ≠ S → (2 : ℤ) ∣ placeValue v z) ∧
        ¬ (2 : ℤ) ∣ placeValue Q z ∧ ¬ (2 : ℤ) ∣ placeValue R z ∧
        ¬ (2 : ℤ) ∣ placeValue S z ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • Q) 2 z = 1) ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • R) 2 z = 1) ∧
        (∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • S) 2 z = 1) := by
  classical
  obtain ⟨L, hL1, hL2⟩ := exists_half_set Gal(K/k)
  have hfin : ((Set.univ.pi fun _ : Gal(K/k) => {x : Multiplicative QModZ | x ^ 2 = 1}) ×ˢ
      (Set.univ : Set (ZMod 2))).Finite :=
    (Set.Finite.pi fun _ => finite_setOf_pow_eq_one 2).prod Set.finite_univ
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = 2 * hfin.toFinset.card + 1 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ := exists_evenRecInv (hres := hres) (hζ := hζ) (L := L) hSpl hTstable hTS
    hSstable hSsplit hgunr
    (fun S₁ hS1 hS2 c hc1 hc2 hc3 => by
      obtain ⟨V, hV1, hV2, hV3, w, hw1, hw2, hw3, hw4, hw5⟩ := hstep S₁ hS1 hS2 c hc1 hc2 hc3
      exact ⟨V, hV1, hV2, hV3, w, hw1, hw2, fun u hu => by exact_mod_cast hw3 u hu, hw4,
        fun hc => hw5 (by exact_mod_cast hc)⟩) M
  have hclsmem : ∀ m < M, d.cls m ∈ hfin.toFinset := by
    intro m hm
    rw [hd.clsSpec m hm]
    exact hfin.mem_toFinset.2 ⟨fun _ _ => pow_placeFrobValue_eq_one hres hζ _ _, Set.mem_univ _⟩
  obtain ⟨i, j, N, hij, hjN, hNlt, hclsj, hclsN, hcij, hcjN, hciN⟩ :=
    exists_three_stages hfin.toFinset d (by rw [← hMdef]; exact hclsmem)
  have hNM : N < M := by rw [hMdef]; exact hNlt
  have hiM : i < M := lt_trans hij (lt_trans hjN hNM)
  have hjM : j < M := lt_trans hjN hNM
  -- the basic bookkeeping about the chosen places
  have hnotT0 : ∀ m < M, d.chosen m ∉ T := fun m hm hmem => hd.chosenNotMem m hm (hTS hmem)
  have hnotS : ∀ m < M, ∀ τ : Gal(K/k), τ • d.chosen m ∉ S₀ := by
    intro m hm τ hmem
    refine hd.chosenNotMem m hm ?_
    have h := hSstable τ⁻¹ _ hmem
    rwa [inv_smul_smul] at h
  have hnotT : ∀ m < M, ∀ τ : Gal(K/k), τ • d.chosen m ∉ T :=
    fun m hm τ hmem => hnotS m hm τ (hTS hmem)
  have hchar : ∀ m < M, ∀ τ : Gal(K/k), ¬ Pc (τ • d.chosen m) ∣ 2 :=
    fun m hm τ hdvd => hnotT m hm τ (hBT (hBwild _ hdvd))
  have hchar0 : ∀ m < M, ¬ Pc (d.chosen m) ∣ 2 :=
    fun m hm hdvd => hnotT0 m hm (hBT (hBwild _ hdvd))
  have hsmulne : ∀ m₁ < M, ∀ m₂ < M, m₁ ≠ m₂ → ∀ τ : Gal(K/k),
      τ • d.chosen m₁ ≠ d.chosen m₂ := by
    intro m₁ h₁ m₂ h₂ hm τ h
    exact hd.chosenNe m₂ h₂ m₁ h₁ (Ne.symm hm) τ h.symm
  have hne0 : ∀ m₁ < M, ∀ m₂ < M, m₁ ≠ m₂ → d.chosen m₁ ≠ d.chosen m₂ := by
    intro m₁ h₁ m₂ h₂ hm h
    exact hd.chosenNe m₁ h₁ m₂ h₂ hm 1 (by rw [one_smul]; exact h)
  have hsmulfix : ∀ m < M, ∀ τ : Gal(K/k), τ ≠ 1 → τ • d.chosen m ≠ d.chosen m := by
    intro m hm τ hτ h
    exact hτ ((Subgroup.eq_bot_iff_forall _).1 (hd.chosenStab m hm) τ (mem_stabilizer_iff.2 h))
  -- the basic bookkeeping about the units
  have hunram : ∀ m < M, ∀ v : HeightOneSpectrum (𝓞 K), v ≠ d.chosen m →
      (2 : ℤ) ∣ placeValue v (d.unit m) := by
    intro m hm v hv
    exact_mod_cast hd.unitUnram m hm v hv
  have hram : ∀ m < M, ¬ (2 : ℤ) ∣ placeValue (d.chosen m) (d.unit m) := by
    intro m hm h
    exact hd.unitRam m hm (by exact_mod_cast h)
  have hpos : ∀ m < M, ∀ φ : K →+* ℝ, 0 < φ ((d.unit m : Kˣ) : K) := fun m hm =>
    forall_pos_of_forall_infClassHom_eq_one dvd_rfl (hd.unitInf m hm)
  have hsq : ∀ m < M, ∀ u : HeightOneSpectrum (𝓞 K), Pc u ∣ 2 →
      ∃ c : (u.adicCompletion K)ˣ,
        c ^ 2 = Units.map (algebraMap K (u.adicCompletion K)).toMonoidHom (d.unit m) :=
    fun m hm u hu => exists_units_pow_of_localClassHom_eq_one
      ((hd.unitPres m hm u (hBT (hBwild u hu))).trans (hgB u (hBwild u hu)))
  -- the symmetry between an automorphism and its inverse, and reciprocity between two stages
  have hsym : ∀ m < M, ∀ τ : Gal(K/k), τ ≠ 1 →
      placeFrobValue hres hζ (τ • d.chosen m) (d.unit m)
        = placeFrobValue hres hζ (τ⁻¹ • d.chosen m) (d.unit m) := fun m hm τ hτ =>
    placeFrobValue_smul_eq_inv_smul_of_unramified hres hζ (hsmulfix m hm τ hτ) (hchar0 m hm)
      (hchar m hm τ) (hchar m hm τ⁻¹) (hpos m hm) (hunram m hm) (hsq m hm)
      ((Int.prime_two.coprime_iff_not_dvd).2 (hram m hm)).symm
  have hrecip : ∀ m₁ < M, ∀ m₂ < M, m₁ ≠ m₂ → ∀ τ : Gal(K/k),
      placeFrobValue hres hζ (τ • d.chosen m₂) (d.unit m₁)
        = placeFrobValue hres hζ (τ⁻¹ • d.chosen m₁) (d.unit m₂) := by
    intro m₁ h₁ m₂ h₂ hm τ
    refine placeFrobValue_smul_eq_placeFrobValue_inv_smul_of_forall_pos
      (V := d.chosen m₁) (W := d.chosen m₂) (σ := τ) (x := d.unit m₁) (y := d.unit m₂)
      (m := placeValue (d.chosen m₁) (d.unit m₁)) hres hζ ?_ (hchar0 m₁ h₁) (hchar m₁ h₁ τ⁻¹)
      (hchar m₂ h₂ τ) (hpos m₂ h₂) (hunram m₁ h₁) (hunram m₂ h₂) (hsq m₁ h₁) ?_
      (Int.ModEq.refl _) ?_
    · exact fun h => hsmulne m₂ h₂ m₁ h₁ (Ne.symm hm) τ h.symm
    · exact ((Int.prime_two.coprime_iff_not_dvd).2 (hram m₁ h₁)).symm
    · show placeValue (d.chosen m₂) (d.unit m₂) % 2
        = placeValue (d.chosen m₁) (d.unit m₁) % 2
      have hA := hram m₁ h₁
      have hB := hram m₂ h₂
      omega
  -- the three stages carry a common value at the Frobenius automorphisms of their places
  have hfrobj : ∀ τ : Gal(K/k), placeFrobValue hres hζ (τ • d.chosen j) (d.unit j)
      = placeFrobValue hres hζ (τ • d.chosen i) (d.unit i) := by
    rw [hd.clsSpec j hjM, hd.clsSpec i hiM] at hclsj
    exact congrFun (congrArg Prod.fst hclsj)
  have hfrobN : ∀ τ : Gal(K/k), placeFrobValue hres hζ (τ • d.chosen N) (d.unit N)
      = placeFrobValue hres hζ (τ • d.chosen i) (d.unit i) := by
    rw [hd.clsSpec N hNM, hd.clsSpec i hiM] at hclsN
    exact congrFun (congrArg Prod.fst hclsN)
  -- the value at an involution is trivial
  have hclaim : ∀ τ : Gal(K/k), τ ≠ 1 → τ = τ⁻¹ →
      placeFrobValue hres hζ (τ • d.chosen i) (d.unit i) = 1 := fun τ hτ hτinv =>
    placeFrobValue_eq_one_of_isInvolution hres hζ hτ (mul_eq_one_iff_eq_inv.2 hτinv) hBstable
      hBwild hBram (fun hmem => hnotT0 i hiM (hBT hmem))
      (fun w hw => (hd.unitPres i hiM w (hBT hw)).trans (hgB w hw)) (hunram i hiM) (hram i hiM)
      (hd.unitZero i hiM τ hτ) (hpos i hiM)
  -- the rule followed at the nontrivial conjugates of the three places
  have hconjQj : ∀ τ : Gal(K/k), τ ≠ 1 →
      (τ ∈ L → localClassHom (τ • d.chosen i) 2 (d.unit j)
        = localClassHom (τ • d.chosen i) 2 (d.unit i)) ∧
      (τ ∉ L → localClassHom (τ • d.chosen i) 2 (d.unit j) = 1) := by
    intro τ hτ
    have h := hd.unitConj i hiM j hjM hij τ hτ
    rw [hcij] at h
    simpa only [evenFlag_zero] using h
  have hconjQN : ∀ τ : Gal(K/k), τ ≠ 1 →
      (τ⁻¹ ∈ L → localClassHom (τ • d.chosen i) 2 (d.unit N)
        = localClassHom (τ • d.chosen i) 2 (d.unit i)) ∧
      (τ⁻¹ ∉ L → localClassHom (τ • d.chosen i) 2 (d.unit N) = 1) := by
    intro τ hτ
    have h := hd.unitConj i hiM N hNM (lt_trans hij hjN) τ hτ
    rw [hciN] at h
    simpa only [evenFlag_one] using h
  have hconjRN : ∀ τ : Gal(K/k), τ ≠ 1 →
      (τ ∈ L → localClassHom (τ • d.chosen j) 2 (d.unit N)
        = localClassHom (τ • d.chosen j) 2 (d.unit j)) ∧
      (τ ∉ L → localClassHom (τ • d.chosen j) 2 (d.unit N) = 1) := by
    intro τ hτ
    have h := hd.unitConj j hjM N hNM hjN τ hτ
    rw [hcjN] at h
    simpa only [evenFlag_zero] using h
  -- the product of the three units is unramified away from the three places
  have hprodunram : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ d.chosen i → v ≠ d.chosen j →
      v ≠ d.chosen N → (2 : ℤ) ∣ placeValue v (d.unit i * d.unit j * d.unit N) := by
    intro v h1 h2 h3
    rw [placeValue_mul, placeValue_mul]
    exact dvd_add (dvd_add (hunram i hiM v h1) (hunram j hjM v h2)) (hunram N hNM v h3)
  refine ⟨d.chosen i, d.chosen j, d.chosen N, hnotT0 i hiM, hnotT0 j hjM, hnotT0 N hNM,
    hd.split _ (hd.chosenMem i hiM) (hnotT0 i hiM), hd.split _ (hd.chosenMem j hjM)
      (hnotT0 j hjM), hd.split _ (hd.chosenMem N hNM) (hnotT0 N hNM),
    hd.chosenNe i hiM j hjM hij.ne, hd.chosenNe i hiM N hNM (lt_trans hij hjN).ne,
    hd.chosenNe j hjM N hNM hjN.ne, hd.chosenStab i hiM, hd.chosenStab j hjM,
    hd.chosenStab N hNM, d.unit i * d.unit j * d.unit N, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [_root_.map_mul, _root_.map_mul, hd.unitPres i hiM v hv, hd.unitPres j hjM v hv,
      hd.unitPres N hNM v hv, _root_.map_pow, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
  · intro u
    rw [_root_.map_mul, _root_.map_mul, hd.unitInf i hiM u, hd.unitInf j hjM u,
      hd.unitInf N hNM u]
    exact (mul_one ((1 : infClasses u 2) * 1)).trans (mul_one (1 : infClasses u 2))
  · exact hprodunram
  · rw [placeValue_mul, placeValue_mul]
    have h0 := hram i hiM
    have h1 := hunram j hjM (d.chosen i) (hne0 i hiM j hjM hij.ne)
    have h2 := hunram N hNM (d.chosen i) (hne0 i hiM N hNM (lt_trans hij hjN).ne)
    omega
  · rw [placeValue_mul, placeValue_mul]
    have h0 := hram j hjM
    have h1 := hunram i hiM (d.chosen j) (hne0 j hjM i hiM hij.ne')
    have h2 := hunram N hNM (d.chosen j) (hne0 j hjM N hNM hjN.ne)
    omega
  · rw [placeValue_mul, placeValue_mul]
    have h0 := hram N hNM
    have h1 := hunram i hiM (d.chosen N) (hne0 N hNM i hiM (lt_trans hij hjN).ne')
    have h2 := hunram j hjM (d.chosen N) (hne0 N hNM j hjM hjN.ne')
    omega
  · intro σ hσ
    have hdvd : (2 : ℤ) ∣ placeValue (σ • d.chosen i) (d.unit i * d.unit j * d.unit N) :=
      hprodunram _ (hsmulfix i hiM σ hσ) (hsmulne i hiM j hjM hij.ne σ)
        (hsmulne i hiM N hNM (lt_trans hij hjN).ne σ)
    refine localClassHom_eq_one_of_placeFrobValue_eq_one Nat.prime_two hres hζ
      (hchar i hiM σ) (by exact_mod_cast hdvd) ?_
    exact placeFrobValue_first_orbit_eq_one hres hζ hL1 hL2 (hclaim σ hσ) (hconjQj σ hσ)
      (hconjQN σ hσ)
  · intro σ hσ
    have hdvd : (2 : ℤ) ∣ placeValue (σ • d.chosen j) (d.unit i * d.unit j * d.unit N) :=
      hprodunram _ (hsmulne j hjM i hiM hij.ne' σ) (hsmulfix j hjM σ hσ)
        (hsmulne j hjM N hNM hjN.ne σ)
    refine localClassHom_eq_one_of_placeFrobValue_eq_one Nat.prime_two hres hζ
      (hchar j hjM σ) (by exact_mod_cast hdvd) ?_
    exact placeFrobValue_second_orbit_eq_one hres hζ hL1 hL2 (hsym i hiM σ hσ).symm (hfrobj σ)
      (hrecip i hiM j hjM hij.ne σ) (hclaim σ hσ) (hconjQj σ⁻¹ (inv_ne_one.2 hσ))
      (hconjRN σ hσ)
  · intro σ hσ
    have hdvd : (2 : ℤ) ∣ placeValue (σ • d.chosen N) (d.unit i * d.unit j * d.unit N) :=
      hprodunram _ (hsmulne N hNM i hiM (lt_trans hij hjN).ne' σ)
        (hsmulne N hNM j hjM hjN.ne' σ) (hsmulfix N hNM σ hσ)
    refine localClassHom_eq_one_of_placeFrobValue_eq_one Nat.prime_two hres hζ
      (hchar N hNM σ) (by exact_mod_cast hdvd) ?_
    have hzQ : (σ ∈ L → localClassHom (σ⁻¹ • d.chosen i) 2 (d.unit N)
        = localClassHom (σ⁻¹ • d.chosen i) 2 (d.unit i)) ∧
        (σ ∉ L → localClassHom (σ⁻¹ • d.chosen i) 2 (d.unit N) = 1) := by
      have h := hconjQN σ⁻¹ (inv_ne_one.2 hσ)
      rwa [inv_inv] at h
    exact placeFrobValue_third_orbit_eq_one hres hζ hL1 hL2 (hsym i hiM σ hσ).symm (hfrobN σ)
      (hfrobj σ⁻¹) (hrecip i hiM N hNM (lt_trans hij hjN).ne σ)
      (hrecip j hjM N hNM hjN.ne σ) (hclaim σ hσ) hzQ (hconjRN σ⁻¹ (inv_ne_one.2 hσ))

end Close

end InverseGalois.CFT

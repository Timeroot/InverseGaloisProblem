/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CharSurjective
import InverseGalois.CFT.PoitouTate.NamedSymbol
import InverseGalois.Solvable.Shafarevich.KernelStep
import InverseGalois.Solvable.Shafarevich.LayerDualTensor
import InverseGalois.Solvable.Shafarevich.LayerMatrix
import InverseGalois.Solvable.Shafarevich.LayerZeroChar

/-!
# The orthogonality of the naming a prescription cuts out

The values prescribed at the named primes name, through Kummer theory, one local class for each
vector of a basis of the layer, and the classes the prescription downstairs is answered with are the
matrix of a comparison map against those.  The residues of the power residue symbol against the
named classes therefore assemble into a homomorphism of the units of the level into the layer
upstairs, and what the reciprocity law is asked for is that this homomorphism die under the
comparison map on the units which become exponent-th powers in a finite level.

That is bought by the counting argument in the layers.  A character of the units of the level is a
character of the Galois group over it, and the ones which matter here are read through the lift of
the base realization, hence named by a functional on the zeroth layer of the group of the letters;
so the whole observation is a linear map out of the dual of that zeroth layer, and the naming
element of the tensor product turns it into a single vector which one surjection onto the intended
number of letters annihilates.  The number of letters is announced before anything else is chosen,
which is what the ladder asks for, and the finite level is then the one cutting out the kernel of
the lift carried across the surjection.

## Main results

* `InverseGalois.CFT.kummerChar_prod_units` — the Kummer character of a finite product of units is
  the sum of their Kummer characters.
* `InverseGalois.Shafarevich.exists_comp_eq_of_ker_le` — a homomorphism trivial on the kernel of a
  surjection is read through that surjection.
* `InverseGalois.Shafarevich.kummerChar_eq_zero_of_pow_mem` — **the Kummer character of a unit
  which becomes an exponent-th power in a level vanishes on the automorphisms fixing that level.**
* `InverseGalois.Shafarevich.isNamedOrthogonal_of_forall_layerCoord` — **the classes carried down by
  a comparison map are orthogonal to the units of a level as soon as the residues against the
  classes named upstairs are killed by the matrix of that map.**
* `Shafarevich.namedOrthogonalEP` — **the orthogonality of the naming, for every prime.**
* `Shafarevich.kernelPrescriptionEP` — **the sharp prescription made one field up, for every odd
  prime, with nothing asked of the arithmetic.**
* `Shafarevich.genericLevelStepEPRoots_of_flatPrescriptionEP` — **the step of the ladder, in
  exchange for the flattening alone.**

## Tags

Shafarevich's theorem, embedding problem, reciprocity, power residue symbol, layer, duality
-/

namespace InverseGalois.CFT

/-! ### The Kummer character of a finite product -/

section KummerProd

variable {K : Type} {Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] {n : ℕ}
  [NeZero n] {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

/-- The Kummer character of a finite product of units is the sum of their Kummer characters. -/
theorem kummerChar_prod_units {ι : Type*} (s : Finset ι) (z : ι → Kˣ) (g : Gal(Ω/K)) :
    kummerChar h (∏ t ∈ s, z t) g = ∑ t ∈ s, kummerChar h (z t) g := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, kummerChar_one_units]
  | @insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx, kummerChar_mul_units, ih]

end KummerProd

end InverseGalois.CFT

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

attribute [local instance] zmodTrivialAction

/-! ### Reading a homomorphism through a surjection -/

section Factor

/-- A homomorphism trivial on the kernel of a surjection is read through that surjection. -/
theorem exists_comp_eq_of_ker_le {G H A : Type*} [Group G] [Group H] [Group A] (f : G →* H)
    (hf : Function.Surjective f) (g : G →* A) (hker : f.ker ≤ g.ker) :
    ∃ g' : H →* A, ∀ x : G, g' (f x) = g x := by
  classical
  have hcongr : ∀ x y : G, f x = f y → g x = g y := by
    intro x y hxy
    have hmem : x * y⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, _root_.map_mul, _root_.map_inv, hxy, mul_inv_cancel]
    have hg := MonoidHom.mem_ker.1 (hker hmem)
    rw [_root_.map_mul, _root_.map_inv] at hg
    exact mul_inv_eq_one.1 hg
  have hsi : ∀ y : H, f (Function.surjInv hf y) = y := fun y => Function.surjInv_eq hf y
  refine ⟨MonoidHom.mk' (fun y => g (Function.surjInv hf y)) (fun y y' => ?_), fun x => ?_⟩
  · refine (hcongr _ (Function.surjInv hf y * Function.surjInv hf y') ?_).trans
      (_root_.map_mul g _ _)
    rw [_root_.map_mul, hsi, hsi, hsi]
  · exact hcongr _ _ (hsi (f x))

end Factor

/-! ### The units which become powers in a level -/

section Bridge

variable {ℓ : ℕ} [NeZero ℓ] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois ↥K Ω] {ζ : ↥K}
  {hζ : IsPrimitiveRoot ζ ℓ}

variable (h : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)

omit [IsGalois k Ω] [NumberField ↥K] in
/-- **The Kummer character of a unit of the level which becomes an exponent-th power in a further
level vanishes on the automorphisms fixing that further level.**

The quotient of the chosen root of the unit by the power in the further level is a root of unity
killed by the exponent, so it is fixed by every automorphism over the level; an automorphism fixing
the further level fixes the power there as well, hence fixes the chosen root, and the character
vanishes exactly where the root is fixed. -/
theorem kummerChar_eq_zero_of_pow_mem (hζ' : IsPrimitiveRoot ζ ℓ) (E : IntermediateField k Ω)
    {u : (↥K)ˣ} (hu : ∃ y : Ω, y ∈ E ∧ y ^ ℓ = algebraMap ↥K Ω (u : ↥K)) {σ : Gal(Ω/↥K)}
    (hσ : galSubHom K σ ∈ E.fixingSubgroup) : kummerChar h u σ = 0 := by
  obtain ⟨y, hyE, hy⟩ := hu
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (NeZero.ne ℓ)] at hy
    exact (map_ne_zero_iff _ (algebraMap ↥K Ω).injective).2 u.ne_zero hy.symm
  have hpowη : ((Units.mk0 y hy0 : Ωˣ) : Ω) ^ ℓ = algebraMap ↥K Ω (u : ↥K) := hy
  have hβη : h.root u ^ ℓ = Units.mk0 y hy0 ^ ℓ := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, coe_root_pow h u, hpowη]
  have hpow : (h.root u * (Units.mk0 y hy0)⁻¹) ^ ℓ = 1 := by
    rw [mul_pow, inv_pow, ← hβη, mul_inv_cancel]
  have hfixξ : σ • (h.root u * (Units.mk0 y hy0)⁻¹) = h.root u * (Units.mk0 y hy0)⁻¹ := by
    rw [← smul_units_galSubHom K σ]
    exact smul_eq_of_pow_eq_one_of_mem_fixingSubgroup K hζ'
      (galSubHom_mem_fixingSubgroup K σ) hpow
  have hfixη : σ • Units.mk0 y hy0 = Units.mk0 y hy0 := by
    refine Units.ext ?_
    show σ y = y
    have hEy := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ y hyE
    rwa [galSubHom_apply] at hEy
  have hfixβ : σ • h.root u = h.root u := by
    have hmul : σ • (h.root u * (Units.mk0 y hy0)⁻¹ * Units.mk0 y hy0)
        = h.root u * (Units.mk0 y hy0)⁻¹ * Units.mk0 y hy0 := by
      rw [smul_mul', hfixξ, hfixη]
    rwa [inv_mul_cancel_right] at hmul
  exact (kummerChar_eq_zero_iff_smul_root_eq h u σ).2 hfixβ

end Bridge

/-! ### The orthogonality read off the matrix of the comparison map -/

section Assembly

/-- **The classes carried down by a comparison map are orthogonal to the units of a level which
become exponent-th powers in a finite level, as soon as the residues of the symbol against the
classes named upstairs are killed by the matrix of that map.**

The prescription upstairs is answered, at each named prime, by a family of units of the level whose
Kummer characters are the coordinates of the prescribed value, and the one downstairs by a family
whose characters are the coordinates of the value carried across the comparison map; the two are
therefore related, coordinate by coordinate, by the matrix of the comparison map on the basis of the
layer.  A unit and a family of units of the level having the same classes at a named place have the
same Kummer characters on the decomposition subgroup there, so the classes downstairs are the
product of the powers of the classes upstairs by that matrix, and the symbol against such a product
is trivial exactly under the prescribed linear relation among the residues. -/
theorem isNamedOrthogonal_of_forall_layerCoord {ℓ : ℕ} [Fact ℓ.Prime] [NeZero ℓ] {k Ω : Type}
    [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {U : Type} [Group U] {φ : Gal(Ω/k) →* U}
    {K : IntermediateField k Ω} [NumberField ↥K] [IsGalois ↥K Ω]
    (hKker : K.fixingSubgroup = φ.ker) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hkd : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)
    {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {P₁ P₂ : Type} [Group P₁] [Finite P₁] [Group P₂] [Finite P₂] {j : ℕ} (α : P₁ →* P₂)
    {ι : Type} [Fintype ι] (Q : ι → Ideal (𝓞 Ω)) (hQp : ∀ μ, (Q μ).IsPrime)
    (hQbot : ∀ μ, Q μ ≠ ⊥) {A : ι → Subgroup Gal(Ω/k)}
    (hAcase : ∀ μ, A μ = stabilizer Gal(Ω/k) (Q μ))
    (a : (μ : ι) → ↥(A μ) →* ↥(layerSub ℓ P₁ j))
    (cN : (μ : ι) → Fin (layerDim ℓ P₁ j) → localClasses (placeUnder K (Q μ) (hQbot μ)) ℓ)
    (hcNline : ∀ μ, ∃ u₀ : (↥K)ˣ, ∀ t, cN μ t ∈
      Subgroup.zpowers (localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ u₀))
    (hcN : ∀ (μ : ι) (z : Fin (layerDim ℓ P₁ j) → (↥K)ˣ),
      (∀ t, localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ (z t) = cN μ t) →
      ∀ (x : ↥(A μ)) (hx : (x : Gal(Ω/k)) ∈ φ.ker),
        kummerKernelHom hKker hkd (layerBasis ℓ P₁ j) layerBasis_pow_eq_one z
          ⟨(x : Gal(Ω/k)), hx⟩ = a μ x)
    (c : (μ : ι) → Fin (layerDim ℓ P₂ j) → localClasses (placeUnder K (Q μ) (hQbot μ)) ℓ)
    (hcline : ∀ μ, ∃ u₀ : (↥K)ˣ, ∀ q, c μ q ∈
      Subgroup.zpowers (localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ u₀))
    (hc : ∀ (μ : ι) (z : Fin (layerDim ℓ P₂ j) → (↥K)ˣ),
      (∀ q, localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ (z q) = c μ q) →
      ∀ (x : ↥(A μ)) (hx : (x : Gal(Ω/k)) ∈ φ.ker),
        kummerKernelHom hKker hkd (layerBasis ℓ P₂ j) layerBasis_pow_eq_one z
          ⟨(x : Gal(Ω/k)), hx⟩ = layerSubMap ℓ α j (a μ x))
    (E : IntermediateField k Ω)
    (hobs : ∀ u : (↥K)ˣ, (∃ y : Ω, y ∈ E ∧ y ^ ℓ = algebraMap ↥K Ω (u : ↥K)) →
      ∀ q : Fin (layerDim ℓ P₂ j),
        ∑ t, layerCoord ℓ P₂ j (layerSubMap ℓ α j (layerBasis ℓ P₁ j t)) q *
          namedSymbolResidue hres hζ (fun μ => placeUnder K (Q μ) (hQbot μ))
            (fun μ => cN μ t) u = 0) :
    IsNamedOrthogonal ℓ K hres hζ E (fun μ => placeUnder K (Q μ) (hQbot μ)) c := by
  classical
  haveI : ∀ μ, (Q μ).IsPrime := hQp
  choose u₀ hu₀ using hcline
  choose uN huN using hcNline
  have hzex : ∀ (μ : ι) (q : Fin (layerDim ℓ P₂ j)), ∃ v : (↥K)ˣ,
      localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ v = c μ q := by
    intro μ q
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hu₀ μ q)
    exact ⟨u₀ μ ^ m, by rw [_root_.map_zpow, hm]⟩
  choose z hz using hzex
  have hzNex : ∀ (μ : ι) (t : Fin (layerDim ℓ P₁ j)), ∃ v : (↥K)ˣ,
      localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ v = cN μ t := by
    intro μ t
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (huN μ t)
    exact ⟨uN μ ^ m, by rw [_root_.map_zpow, hm]⟩
  choose zN hzN using hzNex
  intro Tn _ q u _ hpow
  refine localSymbolPiPairing_eq_one_of_sum_namedSymbolResidue_eq_zero hres hζ
    (fun μ => placeUnder K (Q μ) (hQbot μ)) (fun t μ => cN μ t)
    (fun t => layerCoord ℓ P₂ j (layerSubMap ℓ α j (layerBasis ℓ P₁ j t)) q)
    (fun μ => c μ q) ?_ ((u : (↥K)ˣ)) (hobs ((u : (↥K)ˣ)) hpow q)
  refine funext fun μ => ?_
  simp only [Finset.prod_apply, Pi.pow_apply]
  have hkey : localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ (z μ q)
      = localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ (∏ t, zN μ t ^
        (layerCoord ℓ P₂ j (layerSubMap ℓ α j (layerBasis ℓ P₁ j t)) q).val) := by
    refine localClassHom_eq_of_forall_kummerChar_eq (P := Q μ) hkd rfl fun σ hσ => ?_
    obtain ⟨y, hyσ⟩ : ∃ y : ↥φ.ker, kerGalEquiv hKker y = σ :=
      ⟨(kerGalEquiv hKker).symm σ, (kerGalEquiv hKker).apply_symm_apply σ⟩
    have hxA : (y : Gal(Ω/k)) ∈ A μ := by
      rw [hAcase μ, ← galSubHom_kerGalEquiv hKker y, hyσ]
      exact (mem_stabilizer_galSubHom_iff K σ (Q μ)).2 hσ
    have h1 : ∏ t, layerBasis ℓ P₁ j t ^ (kummerChar hkd (zN μ t) σ).val
        = a μ ⟨(y : Gal(Ω/k)), hxA⟩ := by
      rw [← hyσ, ← kummerKernelHom_apply hKker hkd (layerBasis ℓ P₁ j)
        layerBasis_pow_eq_one (zN μ) y]
      exact hcN μ (zN μ) (hzN μ) ⟨(y : Gal(Ω/k)), hxA⟩ y.2
    have h2 : ∏ q', layerBasis ℓ P₂ j q' ^ (kummerChar hkd (z μ q') σ).val
        = layerSubMap ℓ α j (a μ ⟨(y : Gal(Ω/k)), hxA⟩) := by
      rw [← hyσ, ← kummerKernelHom_apply hKker hkd (layerBasis ℓ P₂ j)
        layerBasis_pow_eq_one (z μ) y]
      exact hc μ (z μ) (hz μ) ⟨(y : Gal(Ω/k)), hxA⟩ y.2
    have hA1 : ∀ t, kummerChar hkd (zN μ t) σ
        = layerCoord ℓ P₁ j (a μ ⟨(y : Gal(Ω/k)), hxA⟩) t := by
      intro t
      rw [← h1, layerCoord_prod_layerBasis_pow]
    have hA2 : kummerChar hkd (z μ q) σ
        = layerCoord ℓ P₂ j (layerSubMap ℓ α j (a μ ⟨(y : Gal(Ω/k)), hxA⟩)) q := by
      rw [← h2, layerCoord_prod_layerBasis_pow]
    rw [hA2, layerCoord_layerSubMap, kummerChar_prod_units]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [kummerChar_units_pow, hA1 t, nsmul_eq_mul, ZMod.natCast_rightInverse, mul_comm]
  rw [← hz μ q, hkey, _root_.map_prod]
  exact Finset.prod_congr rfl fun t _ => by rw [_root_.map_pow, hzN μ t]

end Assembly

end InverseGalois.Shafarevich

namespace Shafarevich

open InverseGalois.CFT InverseGalois.Shafarevich IsDedekindDomain MulAction NumberField

open scoped Pointwise TensorProduct

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

attribute [local instance] genericQuotAction zmodTrivialAction

/-! ### The orthogonality of the naming -/

/-- **The orthogonality of the naming the prescribed values cut out, for every prime.**

The number of letters is announced first, by the counting argument in the tensor product of the
zeroth layer with the layer the values live in: a single vector there is annihilated by a surjection
onto the intended number of letters.  The prescription upstairs is then answered, at each named
prime, by a family of local classes on the line of the class of one unit of the level, and the
residues of the power residue symbol against those classes assemble into a homomorphism of the units
of the level into the layer upstairs.

That homomorphism is the observation the reciprocity law has to kill.  A functional on the zeroth
layer names a character of the group of the letters, read through the lift of the base realization
it becomes a character of the Galois group over the level, and Kummer theory presents that character
as the character of a unit of the level; the observation at that unit therefore depends only on the
functional, linearly, and the naming element of the tensor product turns the whole of it into the
single vector the counting argument annihilates.  The finite level is the one cutting out the kernel
of the lift carried across the surjection, and a unit which becomes an exponent-th power there has a
Kummer character killing that kernel, hence is one of the units the observation was shown to
annihilate. -/
theorem namedOrthogonalEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] : NamedOrthogonalEP ℓ := by
  intro S U _ _ _ _ hS k Ω _ _ _ _ _ φ n j K _ _ _ hKker ζ hζ hkd Pc Ec hres
  classical
  haveI : IsGalois ↥K Ω := IsGalois.tower_top_of_isGalois k ↥K Ω
  have hℓ : ℓ.Prime := Fact.out
  have hm : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
  obtain ⟨N, hN⟩ :=
    exists_operatorHom_tensor_eq_zero U n S hS (j := j) (t := 1) (ZMod ℓ)
  refine ⟨N, ?_⟩
  intro F ι _ Q hQp hQbot A a hFsurj hFsm hFright hAcase hasm hacyc
  haveI : ∀ μ, (Q μ).IsPrime := hQp
  -- the classes the prescribed values name at the higher level
  have hex : ∀ μ : ι, ∃ (u₀ : (↥K)ˣ) (cμ : Fin (layerDim ℓ (Generic U N S) j) →
      localClasses (placeUnder K (Q μ) (hQbot μ)) ℓ),
      (∀ t, cμ t ∈ Subgroup.zpowers (localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ u₀)) ∧
      ∀ z : Fin (layerDim ℓ (Generic U N S) j) → (↥K)ˣ,
        (∀ t, localClassHom (placeUnder K (Q μ) (hQbot μ)) ℓ (z t) = cμ t) →
          ∀ (x : ↥(A μ)) (hx : (x : Gal(Ω/k)) ∈ φ.ker),
            kummerKernelHom hKker hkd (layerBasis ℓ (Generic U N S) j)
              layerBasis_pow_eq_one z ⟨(x : Gal(Ω/k)), hx⟩ = a μ x :=
    fun μ => exists_localClass_zpowers_forall_kummerKernelHom_eq hKker hkd
      (hasKummerCharInertiaLift hkd) hℓ (layerBasis ℓ (Generic U N S) j) layerBasis_pow_eq_one
      (χ := fun t e => layerCoord ℓ (Generic U N S) j e t) prod_layerBasis_pow_layerCoord
      (fun t e e' => layerCoord_mul e e' t) (hQbot μ) rfl (Or.inl (hAcase μ))
      (a μ) (hasm μ) (hacyc μ)
  choose uN cN hcNline hcN using hex
  -- the observation: the residues of the symbol against the classes named upstairs
  have hObsAdd : ∀ t : Fin (layerDim ℓ (Generic U N S) j), ∀ v v' : (↥K)ˣ,
      namedSymbolResidue hres hζ (fun μ => placeUnder K (Q μ) (hQbot μ))
          (fun μ => cN μ t) (v * v')
        = namedSymbolResidue hres hζ (fun μ => placeUnder K (Q μ) (hQbot μ))
            (fun μ => cN μ t) v
          + namedSymbolResidue hres hζ (fun μ => placeUnder K (Q μ) (hQbot μ))
            (fun μ => cN μ t) v' :=
    fun t v v' => namedSymbolResidue_mul hres hζ _ _ v v'
  obtain ⟨Obs, hObs⟩ : ∃ Obs : (↥K)ˣ →* ↥(layerSub ℓ (Generic U N S) j),
      ∀ (t : Fin (layerDim ℓ (Generic U N S) j)) (v : (↥K)ˣ),
        layerCoord ℓ (Generic U N S) j (Obs v) t
          = namedSymbolResidue hres hζ (fun μ => placeUnder K (Q μ) (hQbot μ))
            (fun μ => cN μ t) v :=
    ⟨layerHomOfCoord (P := Generic U N S)
      (fun t v => namedSymbolResidue hres hζ (fun μ => placeUnder K (Q μ) (hQbot μ))
        (fun μ => cN μ t) v) hObsAdd,
      fun t v => layerCoord_layerHomOfCoord _ _ v t⟩
  have hObsCongr : ∀ v v' : (↥K)ˣ,
      (∀ σ : Gal(Ω/↥K), kummerChar hkd v σ = kummerChar hkd v' σ) → Obs v = Obs v' := by
    intro v v' hchar
    refine layerSub_ext fun t => ?_
    rw [hObs, hObs]
    refine namedSymbolResidue_congr hres hζ _ _ fun μ => ?_
    exact localClassHom_eq_of_forall_kummerChar_eq (P := Q μ) hkd rfl fun σ _ => hchar σ
  -- the lift, read over the level
  have hKfix : ∀ σ : Gal(Ω/↥K), galSubHom K σ ∈ φ.ker := fun σ => by
    rw [← hKker]
    exact galSubHom_mem_fixingSubgroup K σ
  have hFrightK : ∀ σ : Gal(Ω/↥K), (F (galSubHom K σ)).right = 1 := fun σ => by
    show SemidirectProduct.rightHom (F (galSubHom K σ)) = 1
    rw [hFright]
    exact hKfix σ
  obtain ⟨Fk, hFk⟩ : ∃ Fk : Gal(Ω/↥K) →*
      (Generic U N S ⧸ pCentral ℓ (Generic U N S) (j + 1)),
      ∀ σ : Gal(Ω/↥K), Fk σ = (F (galSubHom K σ)).left := by
    refine ⟨(MonoidHom.mk' (fun y : ↥φ.ker => (F (y : Gal(Ω/k))).left) (fun y y' => ?_)).comp
      (kerGalEquiv hKker).symm.toMonoidHom, fun σ => ?_⟩
    · show (F ((y : Gal(Ω/k)) * (y' : Gal(Ω/k)))).left = _
      have hy1 : SemidirectProduct.rightHom (F (y : Gal(Ω/k))) = 1 := by
        rw [hFright]
        exact y.2
      rw [_root_.map_mul, SemidirectProduct.mul_left]
      show (F (y : Gal(Ω/k))).left * (pCentralAut ℓ (genericAut U N S) (j + 1))
        (SemidirectProduct.rightHom (F (y : Gal(Ω/k)))) ((F (y' : Gal(Ω/k))).left) = _
      rw [hy1, _root_.map_one]
      rfl
    · show (F (((kerGalEquiv hKker).symm σ : ↥φ.ker) : Gal(Ω/k))).left = _
      rw [← galSubHom_kerGalEquiv hKker ((kerGalEquiv hKker).symm σ),
        MulEquiv.apply_symm_apply]
  have hFkerOpen : IsOpen ((F.ker : Subgroup Gal(Ω/k)) : Set Gal(Ω/k)) :=
    (isOpenNormal_ker_of_isSmoothHom hFsm).isOpen
  have hFksurj : Function.Surjective Fk := by
    intro p
    obtain ⟨x, hx⟩ := hFsurj ⟨p, 1⟩
    have hxker : x ∈ φ.ker := by
      refine MonoidHom.mem_ker.2 ?_
      rw [← hFright x, hx]
      rfl
    have hxfix : x ∈ K.fixingSubgroup := by
      rw [hKker]
      exact hxker
    obtain ⟨σ, hσ⟩ := exists_galSubHom_eq K hxfix
    exact ⟨σ, by rw [hFk, hσ, hx]⟩
  -- the observation, read as a linear map out of the dual of the zeroth layer
  have hΞadd : ∀ (ψ : Module.Dual (ZMod ℓ) (Layer ℓ (Generic U N S) 0)) (x y : Gal(Ω/↥K)),
      (zeroDualCharQuot ℓ ψ (j + 1) hm (Fk (x * y))).toAdd
        = (zeroDualCharQuot ℓ ψ (j + 1) hm (Fk x)).toAdd
          + (zeroDualCharQuot ℓ ψ (j + 1) hm (Fk y)).toAdd := by
    intro ψ x y
    rw [_root_.map_mul, _root_.map_mul]
    rfl
  have hΞsm : ∀ ψ : Module.Dual (ZMod ℓ) (Layer ℓ (Generic U N S) 0),
      ∃ N₀ : Subgroup Gal(Ω/↥K), IsOpen (N₀ : Set Gal(Ω/↥K)) ∧
        ∀ x ∈ N₀, (zeroDualCharQuot ℓ ψ (j + 1) hm (Fk x)).toAdd = 0 := by
    intro ψ
    refine ⟨Subgroup.comap (galSubHom K) F.ker, ?_, fun x hx => ?_⟩
    · rw [Subgroup.coe_comap]
      exact hFkerOpen.preimage (continuous_galSubHom K)
    · have hx1 : F (galSubHom K x) = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_comap.1 hx)
      rw [hFk, hx1, SemidirectProduct.one_left, _root_.map_one]
      rfl
  have huex : ∀ ψ : Module.Dual (ZMod ℓ) (Layer ℓ (Generic U N S) 0),
      ∃ v : (↥K)ˣ, ∀ σ : Gal(Ω/↥K),
        kummerChar hkd v σ = (zeroDualCharQuot ℓ ψ (j + 1) hm (Fk σ)).toAdd :=
    fun ψ => exists_units_forall_kummerChar_eq hkd _ (hΞadd ψ) (hΞsm ψ)
  choose uOf huOf using huex
  obtain ⟨W, hW⟩ : ∃ W : Module.Dual (ZMod ℓ) (Layer ℓ (Generic U N S) 0) →ₗ[ZMod ℓ]
      Layer ℓ (Generic U N S) j, ∀ ψ, Additive.toMul (W ψ) = Obs (uOf ψ) := by
    refine ⟨AddMonoidHom.toZModLinearMap ℓ
      { toFun := fun ψ => Additive.ofMul (Obs (uOf ψ))
        map_zero' := ?_
        map_add' := fun ψ ψ' => ?_ }, fun ψ => rfl⟩
    · show Additive.ofMul (Obs (uOf 0)) = Additive.ofMul (1 : ↥(layerSub ℓ (Generic U N S) j))
      refine congrArg Additive.ofMul ?_
      rw [← _root_.map_one Obs]
      refine hObsCongr _ _ fun σ => ?_
      rw [huOf, kummerChar_one_units]
      obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Fk σ)
      rw [← hy]
      rfl
    · show Additive.ofMul (Obs (uOf (ψ + ψ')))
        = Additive.ofMul (Obs (uOf ψ) * Obs (uOf ψ'))
      rw [← _root_.map_mul Obs]
      refine congrArg Additive.ofMul (hObsCongr _ _ fun σ => ?_)
      rw [huOf, kummerChar_mul_units, huOf, huOf, zeroDualCharQuot_add]
      rfl
  -- the shrinking which annihilates the observation
  obtain ⟨α, hα, hαsurj, hαzero⟩ := hN
    (fun _ : Fin 1 => dualTensorElt (Module.finBasis (ZMod ℓ)
      (Layer ℓ (Generic U N S) 0)) W)
  have hWzero : ∀ η : Module.Dual (ZMod ℓ) (Layer ℓ (Generic U n S) 0),
      layerLinear ℓ α j (W (η.comp (layerLinear ℓ α 0))) = 0 :=
    fun η => eq_zero_of_map_dualTensorElt_eq_zero _ W (layerLinear ℓ α 0) (layerLinear ℓ α j)
      (hαzero 0) η
  -- the finite level cutting out the kernel of the lift carried across the shrinking
  have hle : F.ker ≤ ((layerSemidirectMap ℓ hα (j + 1)).comp F).ker := by
    intro x hx
    refine MonoidHom.mem_ker.2 ?_
    show layerSemidirectMap ℓ hα (j + 1) (F x) = 1
    rw [MonoidHom.mem_ker.1 hx, _root_.map_one]
  obtain ⟨E, hEfin, hEgal, hEfix, hEmem⟩ :=
    exists_level_fixingSubgroup_eq (N := ((layerSemidirectMap ℓ hα (j + 1)).comp F).ker)
      ⟨inferInstance, Subgroup.isOpen_mono hle hFkerOpen⟩
  haveI := hEfin
  haveI := hEgal
  have hkerφ : ((layerSemidirectMap ℓ hα (j + 1)).comp F).ker ≤ φ.ker := by
    intro x hx
    have hx1 : layerSemidirectMap ℓ hα (j + 1) (F x) = 1 := MonoidHom.mem_ker.1 hx
    have h2 : (layerSemidirectMap ℓ hα (j + 1) (F x)).right = φ x := hFright x
    rw [hx1] at h2
    exact MonoidHom.mem_ker.2 h2.symm
  have hKE : K ≤ E := by
    intro x hx
    refine hEmem x fun σ hσ => ?_
    have hσK : σ ∈ K.fixingSubgroup := by
      rw [hKker]
      exact hkerφ hσ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσK x hx
  refine ⟨α, hα, hαsurj, E, hEfin, hEgal, hKE, le_of_eq hEfix, fun c hcline hc => ?_⟩
  refine isNamedOrthogonal_of_forall_layerCoord hKker hζ hkd hres α Q hQp hQbot hAcase a
    cN (fun μ => ⟨uN μ, hcNline μ⟩) hcN c hcline hc E fun u hu q => ?_
  -- the observation dies on the units which become powers in the level
  have hpcm : Function.Surjective (pCentralMap ℓ (j + 1) α) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨w, rfl⟩ := hαsurj y
    exact ⟨QuotientGroup.mk w, rfl⟩
  have hMker : ∀ σ : Gal(Ω/↥K),
      (pCentralMap ℓ (j + 1) α) (Fk σ) = 1 → kummerChar hkd u σ = 0 := by
    intro σ hσ
    have hΛ : layerSemidirectMap ℓ hα (j + 1) (F (galSubHom K σ)) = 1 := by
      refine SemidirectProduct.ext ?_ (hFrightK σ)
      show pCentralMap ℓ (j + 1) α (F (galSubHom K σ)).left = 1
      rw [← hFk]
      exact hσ
    have hmem : galSubHom K σ ∈ E.fixingSubgroup := by
      rw [hEfix]
      exact MonoidHom.mem_ker.2 hΛ
    exact kummerChar_eq_zero_of_pow_mem hkd hζ E hu hmem
  obtain ⟨g, hg⟩ := exists_comp_eq_of_ker_le ((pCentralMap ℓ (j + 1) α).comp Fk)
    (hpcm.comp hFksurj)
    (MonoidHom.mk' (fun σ : Gal(Ω/↥K) => Multiplicative.ofAdd (kummerChar hkd u σ))
      (fun σ σ' => by
        show Multiplicative.ofAdd (kummerChar hkd u (σ * σ'))
          = Multiplicative.ofAdd (kummerChar hkd u σ) * Multiplicative.ofAdd (kummerChar hkd u σ')
        rw [kummerChar_mul, ofAdd_add])) (by
        intro σ hσ
        refine MonoidHom.mem_ker.2 ?_
        show Multiplicative.ofAdd (kummerChar hkd u σ) = 1
        rw [hMker σ (MonoidHom.mem_ker.1 hσ)]
        rfl)
  obtain ⟨η, hη⟩ := exists_zeroDualCharQuot_eq (p := ℓ) hm g
  have hchar : ∀ σ : Gal(Ω/↥K),
      kummerChar hkd (uOf (η.comp (layerLinear ℓ α 0))) σ = kummerChar hkd u σ := by
    intro σ
    rw [huOf, zeroDualCharQuot_comp, hη]
    show (g (((pCentralMap ℓ (j + 1) α).comp Fk) σ)).toAdd = kummerChar hkd u σ
    rw [hg]
    rfl
  have hObsu : Obs u = Additive.toMul (W (η.comp (layerLinear ℓ α 0))) := by
    rw [hW]
    exact (hObsCongr _ _ hchar).symm
  have hzero1 : layerSubMap ℓ α j (Obs u) = 1 := by
    rw [hObsu]
    exact congrArg Additive.toMul (hWzero η)
  have hcoord : layerCoord ℓ (Generic U n S) j (layerSubMap ℓ α j (Obs u)) q = 0 := by
    rw [hzero1, layerCoord_one]
  rw [layerCoord_layerSubMap] at hcoord
  rw [← hcoord]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hObs]
  exact mul_comm _ _

/-- **The sharp prescription made one field up, for every odd prime, with nothing asked of the
arithmetic.** -/
theorem kernelPrescriptionEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] (hodd : 2 < ℓ) :
    KernelPrescriptionEP ℓ :=
  kernelPrescriptionEP_of_namedOrthogonalEP ℓ hodd (namedOrthogonalEP ℓ)

/-- **The step of the ladder, in exchange for the flattening alone.** -/
theorem genericLevelStepEPRoots_of_flatPrescriptionEP (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ]
    (hodd : 2 < ℓ) (hflat : FlatPrescriptionEP ℓ) : GenericLevelStepEPRoots ℓ :=
  genericLevelStepEPRoots_of_namedOrthogonalEP ℓ hodd hflat (namedOrthogonalEP ℓ)

end Shafarevich

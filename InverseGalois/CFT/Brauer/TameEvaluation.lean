/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.TameSymbol

/-!
# The kernel of the tame norm residue symbol

The tame form of the norm residue symbol pairs a chosen uniformiser with a unit of the valuation
ring built from the two arguments and their valuations.  That remaining pairing is trivial exactly
when the unit is a power, so the kernel of the symbol is completely determined.

The reason a uniformiser pairs nontrivially with a unit which is not a power is a counting
argument.  The level of a unit is a radical extension of prime degree by a unit, hence unramified,
so every unit of the valuation ring of the base is a norm from it.  A subgroup of the units of the
base which contains all units of the valuation ring and also a uniformiser is everything, because
dividing by the matching power of the uniformiser turns any element into a unit of the valuation
ring.  The norm subgroup of a cyclic extension of a local field has index the degree, so a
uniformiser can only be a norm when the level is trivial -- and the level of a unit is trivial
exactly when that unit is a power.

## Main results

* `InverseGalois.CFT.eq_top_of_units_le_of_uniformiser_mem`: a subgroup containing the units of the
  valuation ring and a uniformiser is everything.
* `InverseGalois.CFT.exists_pow_eq_of_card_gal_kummerLevel_eq_one`: a unit whose level is trivial
  is a power.
* `InverseGalois.CFT.localSymbol_uniformiser_eq_one_iff`: **the norm residue symbol of a uniformiser
  against a unit of the valuation ring is trivial exactly when that unit is a power.**
* `InverseGalois.CFT.localSymbol_eq_one_iff_isPow`: **the kernel of the tame norm residue symbol.**
* `InverseGalois.CFT.orderOf_localSymbol_uniformiser`: the symbol of a uniformiser against a unit of
  the valuation ring which is not a power has order the exponent.

## Tags

norm residue symbol, Hilbert symbol, tame symbol, local field, uniformiser, norm subgroup,
Kummer theory, class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

/-! ### Subgroups containing a uniformiser -/

section Uniformiser

variable {K : Type} [Field K] [Valued K ℤᵐ⁰] {m : ℤ}

/-- **A subgroup of the units of a discretely valued field which contains every unit of the
valuation ring and a uniformiser is everything**, because dividing an element by the matching power
of the uniformiser leaves a unit of the valuation ring. -/
theorem eq_top_of_units_le_of_uniformiser_mem (hm : IsUnitValGen K m) {N : Subgroup Kˣ}
    (hU : ∀ x : Kˣ, Valued.v (x : K) = 1 → x ∈ N) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = 1) (hmem : π ∈ N) : N = ⊤ := by
  refine eq_top_iff.mpr fun a _ => ?_
  have hprod := N.mul_mem (N.zpow_mem hmem (unitValDiv hm (Additive.ofMul a)))
    (hU _ (valued_mul_zpow_uniformiser hm hπ a))
  rwa [zpow_mul_mul_zpow_neg] at hprod

end Uniformiser

/-! ### A level of degree one -/

section Level

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] {n : ℕ} [NeZero n]
  {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

/-- **A unit whose level is trivial is a power**: the chosen root of the unit is then already a
scalar, and its exponent-th power is the unit. -/
theorem exists_pow_eq_of_card_gal_kummerLevel_eq_one (b : Kˣ)
    (hd1 : Nat.card Gal(↥(kummerLevel h b)/K) = 1) : ∃ c : Kˣ, c ^ n = b := by
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_pow_card h b
  rw [hd1, pow_one] at hc
  have hcΩ : algebraMap K Ω c = ((h.root b : Ωˣ) : Ω) := by
    refine (IsScalarTower.algebraMap_apply K ↥(kummerLevel h b) Ω c).trans ?_
    exact congrArg (algebraMap ↥(kummerLevel h b) Ω) hc
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcΩ
    exact (h.root b).ne_zero hcΩ.symm
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  refine (algebraMap K Ω).injective ?_
  rw [map_pow, hcΩ]
  exact congrArg Units.val (h.root_pow b)

end Level

/-! ### A uniformiser is not a norm from a nontrivial level -/

section KummerUniformiser

variable {K Ω : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [Field Ω] [Algebra K Ω] [IsGalois K Ω] {n : ℕ} [NeZero n] {ζ : K}
  {hζ : IsPrimitiveRoot ζ n} {m : ℤ} {p e : ℕ}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

attribute [local instance] finiteDimensional_kummerLevel isGalois_kummerLevel

/-- **Every unit of the valuation ring is a norm from the level of a unit of the valuation ring**,
that level being unramified. -/
theorem mem_normSubgroup_kummerLevel_of_valued_eq_one (hn : n.Prime) (hpn : ¬ p ∣ n)
    (hres : HasResidueChar K p e) {a b : Kˣ} (ha : Valued.v (a : K) = 1)
    (hb : Valued.v (b : K) = 1) : a ∈ normSubgroup K ↥(kummerLevel h b) :=
  (mem_normSubgroup_iff a).mpr
    ((kummerSymbolUnits_eq_one_iff_norm_kummerLevel h a b).mp
      (kummerSymbolUnits_eq_one_of_valued_eq_one h hn hpn hres ha hb))

/-- **A uniformiser is not a norm from the level of a unit of the valuation ring which is not a
power.**  The norm subgroup already contains every unit of the valuation ring, so a uniformiser in
it would make it everything, while its index is the degree of the level. -/
theorem not_mem_normSubgroup_kummerLevel (hn : n.Prime) (hpn : ¬ p ∣ n)
    (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) {b : Kˣ} (hb : Valued.v (b : K) = 1)
    (hnp : ¬ ∃ c : Kˣ, c ^ n = b) {π : Kˣ} (hπ : unitValDiv hm (Additive.ofMul π) = 1) :
    π ∉ normSubgroup K ↥(kummerLevel h b) := by
  intro hmem
  obtain ⟨σ₀, -, hgen, -, -, -⟩ := exists_generator_kummerLevel_index h b
  haveI : IsCyclic Gal(↥(kummerLevel h b)/K) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ₀, eq_top_iff.mpr fun x _ => hgen x⟩
  have htop : normSubgroup K ↥(kummerLevel h b) = ⊤ :=
    eq_top_of_units_le_of_uniformiser_mem hm
      (fun x hx => mem_normSubgroup_kummerLevel_of_valued_eq_one h hn hpn hres hx hb) hπ hmem
  have hidx := index_normSubgroup_eq_finrank_local K ↥(kummerLevel h b) hres
  rw [htop, Subgroup.index_top] at hidx
  exact hnp (exists_pow_eq_of_card_gal_kummerLevel_eq_one h b
    ((IsGalois.card_aut_eq_finrank K ↥(kummerLevel h b)).trans hidx.symm))

/-- **The power symbol of a uniformiser against a unit of the valuation ring which is not a power is
nontrivial**, the symbol being trivial exactly when its first argument is a norm from the level of
its second. -/
theorem kummerSymbolUnits_ne_one_of_uniformiser (hn : n.Prime) (hpn : ¬ p ∣ n)
    (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) {b : Kˣ} (hb : Valued.v (b : K) = 1)
    (hnp : ¬ ∃ c : Kˣ, c ^ n = b) {π : Kˣ} (hπ : unitValDiv hm (Additive.ofMul π) = 1) :
    kummerSymbolUnits h (mulZMod n) π b ≠ 1 := fun hs =>
  not_mem_normSubgroup_kummerLevel h hn hpn hres hm hb hnp hπ
    ((mem_normSubgroup_iff π).mpr ((kummerSymbolUnits_eq_one_iff_norm_kummerLevel h π b).mp hs))

end KummerUniformiser

/-! ### The norm residue symbol sees the power symbol exactly -/

section Bridge

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ}
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(AlgebraicClosure K/K) M]
  {ι : M →* Kˣ} {n : ℕ} [NeZero n] [IsSmoothAction Gal(AlgebraicClosure K/K) M]

/-- **The norm residue symbol is trivial exactly when the power symbol is**, the invariant map being
an isomorphism and an algebraic closure being closed under roots. -/
theorem localKummerSymbol_eq_one_iff_kummerSymbolUnits (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (h : IsKummerData K (AlgebraicClosure K) M ι n) (Φ : M →* M →* M)
    (a b : Kˣ) :
    localKummerSymbol hres hm h Φ a b = 1 ↔ kummerSymbolUnits h Φ a b = 1 :=
  (localKummerSymbol_eq_one_iff hres hm h Φ a b).trans
    (kummerSymbolUnits_eq_one_iff h Φ exists_units_pow_eq_self a b).symm

end Bridge

/-! ### The kernel of the tame symbol -/

section Root

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e : ℕ} {n : ℕ} [NeZero n] {ζ : K}

/-- **The norm residue symbol of a uniformiser against a unit of the valuation ring is trivial
exactly when that unit is a power.** -/
theorem localSymbol_uniformiser_eq_one_iff (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hpn : ¬ p ∣ n) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = 1) {b : Kˣ} (hb : Valued.v (b : K) = 1) :
    localSymbol hres hm hζ π b = 1 ↔ ∃ c : Kˣ, c ^ n = b := by
  refine ⟨fun hs => ?_, fun hc => localSymbol_eq_one_of_isPow_right hres hm hζ π hc⟩
  letI := zmodTrivialAction K (AlgebraicClosure K) n
  haveI : IsSmoothAction Gal(AlgebraicClosure K/K) (Multiplicative (ZMod n)) :=
    isSmoothAction_of_trivial fun _ _ => rfl
  by_contra hnp
  refine kummerSymbolUnits_ne_one_of_uniformiser
    (isKummerData_zmod (Ω := AlgebraicClosure K) hζ exists_units_pow_eq) hn hpn
    hres hm hb hnp hπ ?_
  exact (localKummerSymbol_eq_one_iff_kummerSymbolUnits hres hm
    (isKummerData_zmod hζ exists_units_pow_eq) (mulZMod n) π b).mp hs

/-- **The kernel of the tame norm residue symbol.**  Once a uniformiser is chosen, the symbol of two
elements is trivial exactly when the unit of the valuation ring built from them and their valuations
is a power. -/
theorem localSymbol_eq_one_iff_isPow (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hpn : ¬ p ∣ n) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = 1) (a b : Kˣ) :
    localSymbol hres hm hζ a b = 1 ↔
      ∃ c : Kˣ, c ^ n
        = (-1) ^ (unitValDiv hm (Additive.ofMul a) * unitValDiv hm (Additive.ofMul b))
          * b ^ unitValDiv hm (Additive.ofMul a)
          * a ^ (-unitValDiv hm (Additive.ofMul b)) := by
  rw [localSymbol_eq_uniformiser hres hm hζ hn hpn hπ a b]
  exact localSymbol_uniformiser_eq_one_iff hres hm hζ hn hpn hπ
    (valued_tame_argument_eq_one hm a b)

/-- **The norm residue symbol of a unit of the valuation ring against a uniformiser is trivial
exactly when that unit is a power**, which is the tame form read in the first argument. -/
theorem localSymbol_unit_uniformiser_eq_one_iff (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hpn : ¬ p ∣ n) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = 1) {a : Kˣ} (ha : Valued.v (a : K) = 1) :
    localSymbol hres hm hζ a π = 1 ↔ ∃ c : Kˣ, c ^ n = a := by
  have hkey := localSymbol_eq_one_iff_isPow hres hm hζ hn hpn hπ a π
  rw [unitValDiv_eq_zero_of_valued_eq_one hm ha, hπ] at hkey
  have hsimp : ((-1 : Kˣ)) ^ ((0 : ℤ) * 1) * π ^ (0 : ℤ) * a ^ (-(1 : ℤ)) = a⁻¹ := by
    rw [zero_mul, zpow_zero, zpow_zero, one_mul, one_mul, zpow_neg_one]
  rw [hkey, hsimp]
  exact ⟨fun ⟨c, hc⟩ => ⟨c⁻¹, by rw [inv_pow, hc, inv_inv]⟩,
    fun ⟨c, hc⟩ => ⟨c⁻¹, by rw [inv_pow, hc]⟩⟩

/-- **The norm residue symbol of a uniformiser against a unit of the valuation ring which is not a
power has order the exponent**, the exponent being prime and the symbol killed by it. -/
theorem orderOf_localSymbol_uniformiser (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hpn : ¬ p ∣ n) {π : Kˣ}
    (hπ : unitValDiv hm (Additive.ofMul π) = 1) {b : Kˣ} (hb : Valued.v (b : K) = 1)
    (hnp : ¬ ∃ c : Kˣ, c ^ n = b) : orderOf (localSymbol hres hm hζ π b) = n := by
  have hdvd : orderOf (localSymbol hres hm hζ π b) ∣ n :=
    orderOf_dvd_of_pow_eq_one (pow_localSymbol_eq_one hres hm hζ π b)
  rcases hn.eq_one_or_self_of_dvd _ hdvd with h1 | hself
  · exact absurd ((localSymbol_uniformiser_eq_one_iff hres hm hζ hn hpn hπ hb).mp
      (orderOf_eq_one_iff.mp h1)) hnp
  · exact hself

end Root

end InverseGalois.CFT

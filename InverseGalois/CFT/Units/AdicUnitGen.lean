/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicHerbrand
import InverseGalois.CFT.Local.AdicResidue
import InverseGalois.CFT.Local.UnitPowRoot

/-!
# One unit generates the units of a completion modulo powers

The units of the valuation ring of the completion at a finite place of a number field are, modulo
the units congruent to one, the multiplicative group of the residue field, and that group is cyclic
because the residue field is finite.  So a single unit whose residue generates the residue units,
together with the units congruent to one, generates all of them.

For an exponent prime to the residue characteristic the units congruent to one are all `n`-th
powers, by the exponential of the completion.  Combining the two, every unit of the valuation ring
is a power of the distinguished unit times an `n`-th power.

## Main results

* `InverseGalois.CFT.exists_pow_mul_pow_eq_of_unitGen`: **for an exponent prime to the residue
  characteristic, a unit whose residues generate is a generator modulo `n`-th powers.**
* `InverseGalois.CFT.exists_unitGen_adicCompletion`: **the completion at a finite place carries a
  unit whose residue generates the units of the residue field.**
* `InverseGalois.CFT.exists_unitGen_pow_mul_pow`: **every unit of the valuation ring of the
  completion is a power of one fixed unit times an `n`-th power**, for an exponent prime to the
  residue characteristic.

## Tags

number field, adic completion, residue field, unit, power
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped WithZero

/-! ### A generator modulo powers -/

section UnitGen

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] [CompleteSpace A] {p e : ℕ}

/-- **For an exponent prime to the residue characteristic, a unit whose residues generate is a
generator modulo `n`-th powers.**  Dividing by the right power of the distinguished unit leaves a
unit congruent to one, and such a unit is an `n`-th power. -/
theorem exists_pow_mul_pow_eq_of_unitGen (h : HasResidueChar A p e) {n : ℕ} (hn : n ≠ 0)
    (hpn : ¬ p ∣ n) {g : Aˣ} (hgval : Valued.v (g : A) = 1)
    (hgen : ∀ w : Aˣ, Valued.v (w : A) = 1 → ∃ m : ℕ, Valued.v ((w : A) - (g : A) ^ m) < 1)
    {u : Aˣ} (hu : Valued.v (u : A) = 1) : ∃ (m : ℕ) (y : Aˣ), u = g ^ m * y ^ n := by
  obtain ⟨m, hm⟩ := hgen u hu
  have hgm : Valued.v ((g : A) ^ m) = 1 := by rw [map_pow, hgval, one_pow]
  have hcoe : ((u * (g ^ m)⁻¹ : Aˣ) : A) - 1 = ((u : A) - (g : A) ^ m) * ((g : A) ^ m)⁻¹ := by
    have hne : ((g : A) ^ m) ≠ 0 := pow_ne_zero _ g.ne_zero
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp
  have hmem : u * (g ^ m)⁻¹ ∈ unitFiltration A 0 := by
    rw [mem_unitFiltration, hcoe]
    refine le_trans (le_of_eq ?_) (le_exp_neg_one_of_lt_one hm)
    rw [map_mul, map_inv₀, hgm, inv_one, mul_one]
  obtain ⟨y, -, hy⟩ := exists_mem_unitFiltration_zero_pow_eq h hn hpn hmem
  refine ⟨m, y, ?_⟩
  rw [hy, mul_comm u ((g ^ m)⁻¹), mul_inv_cancel_left]

end UnitGen

/-! ### The residue field of a completion -/

section AdicUnitGen

variable {K : Type*} [Field K] [NumberField K]

/-- **The completion at a place over a rational prime has that prime as its residue
characteristic.**  The prime lies in the place, so it has valuation less than one there, and it is
nonzero, so its valuation is the exponential of a negative integer. -/
theorem exists_hasResidueChar_of_mem {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    (hmem : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) : ∃ e : ℕ, HasResidueChar (v.adicCompletion K) p e := by
  have hval : Valued.v ((p : ℕ) : v.adicCompletion K)
      = v.valuation K (algebraMap (𝓞 K) K ((p : ℕ) : 𝓞 K)) := by
    rw [← map_natCast (algebraMap (𝓞 K) (v.adicCompletion K)) p,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
  have hlt : Valued.v ((p : ℕ) : v.adicCompletion K) < 1 := by
    rw [hval]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hmem
  have hne : Valued.v ((p : ℕ) : v.adicCompletion K) ≠ 0 := by
    rw [hval]
    refine (Valuation.ne_zero_iff _).mpr ?_
    simpa using hp.ne_zero
  have hlog : WithZero.log (Valued.v ((p : ℕ) : v.adicCompletion K)) < 0 :=
    (WithZero.log_lt_iff_lt_exp hne).mpr (by simpa using hlt)
  refine ⟨(-WithZero.log (Valued.v ((p : ℕ) : v.adicCompletion K))).toNat, hp, by omega, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]

variable (K) in
/-- An element of the ring of integers outside a place has valuation one in the completion
there. -/
theorem valued_algebraMap_eq_one_of_not_mem (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K}
    (hb : b ∉ v.asIdeal) :
    Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) b) = 1 := by
  have hmap : algebraMap (𝓞 K) (v.adicCompletion K) b
      = ((algebraMap (𝓞 K) K b : K) : v.adicCompletion K) := rfl
  rw [hmap, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v)]
  refine le_antisymm (v.valuation_le_one b) ?_
  by_contra hlt
  exact hb ((HeightOneSpectrum.valuation_lt_one_iff_mem v _).mp (not_le.mp hlt))

variable (K) in
/-- An element of the ring of integers inside a place has valuation less than one in the completion
there. -/
theorem valued_algebraMap_lt_one_of_mem (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K}
    (hb : b ∈ v.asIdeal) :
    Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) b) < 1 := by
  have hmap : algebraMap (𝓞 K) (v.adicCompletion K) b
      = ((algebraMap (𝓞 K) K b : K) : v.adicCompletion K) := rfl
  rw [hmap, HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v)]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hb

variable (K) in
/-- **The completion at a finite place carries a unit whose residue generates the units of the
residue field.**  The residue field is finite, so its multiplicative group is cyclic; a
representative of a generator is a unit of the completion, and every unit of the valuation ring is
congruent to a power of it, because every such unit is congruent to an element of the ring of
integers outside the place. -/
theorem exists_unitGen_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    ∃ g : (v.adicCompletion K)ˣ, Valued.v (g : v.adicCompletion K) = 1 ∧
      ∀ w : (v.adicCompletion K)ˣ, Valued.v (w : v.adicCompletion K) = 1 →
        ∃ m : ℕ, Valued.v ((w : v.adicCompletion K) - (g : v.adicCompletion K) ^ m) < 1 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := (𝓞 K ⧸ v.asIdeal)ˣ)
  obtain ⟨g₀, hg₀⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) (ζ : 𝓞 K ⧸ v.asIdeal)
  have hg₀mem : g₀ ∉ v.asIdeal := by
    intro hmem
    have hz : (Ideal.Quotient.mk v.asIdeal) g₀ = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    rw [hg₀] at hz
    exact ζ.ne_zero hz
  have hgval : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) g₀) = 1 :=
    valued_algebraMap_eq_one_of_not_mem K v hg₀mem
  have hgne : algebraMap (𝓞 K) (v.adicCompletion K) g₀ ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hgval
    exact zero_ne_one hgval
  refine ⟨Units.mk0 _ hgne, hgval, fun w hw => ?_⟩
  -- the unit is congruent to an element of the ring of integers outside the place
  obtain ⟨b, hb⟩ := exists_algebraMap_sub_le_exp_neg_one (R := 𝓞 K) K v (le_of_eq hw)
  have hexp : WithZero.exp (-1 : ℤ) < (1 : ℤᵐ⁰) := by
    simpa using WithZero.exp_lt_exp.mpr (by omega : (-1 : ℤ) < 0)
  have hblt : Valued.v ((w : v.adicCompletion K)
      - algebraMap (𝓞 K) (v.adicCompletion K) b) < 1 := lt_of_le_of_lt hb hexp
  have hbmem : b ∉ v.asIdeal := by
    intro hmem
    have hsplit : (w : v.adicCompletion K)
        = ((w : v.adicCompletion K) - algebraMap (𝓞 K) (v.adicCompletion K) b)
          + algebraMap (𝓞 K) (v.adicCompletion K) b := by ring
    have hlt : Valued.v (w : v.adicCompletion K) < 1 := by
      rw [hsplit]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _)
        (max_lt hblt (valued_algebraMap_lt_one_of_mem K v hmem))
    rw [hw] at hlt
    exact lt_irrefl _ hlt
  -- its residue is a power of the generator of the residue units
  have hbne : (Ideal.Quotient.mk v.asIdeal) b ≠ 0 := fun hz =>
    hbmem ((Ideal.Quotient.eq_zero_iff_mem).mp hz)
  obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers).mpr (hζ (Units.mk0 _ hbne))
  dsimp only at hm
  have hres : (Ideal.Quotient.mk v.asIdeal) (b - g₀ ^ m) = 0 := by
    have hcast : (Ideal.Quotient.mk v.asIdeal) (g₀ ^ m)
        = ((ζ ^ m : (𝓞 K ⧸ v.asIdeal)ˣ) : 𝓞 K ⧸ v.asIdeal) := by
      rw [map_pow, hg₀, Units.val_pow_eq_pow_val]
    rw [map_sub, sub_eq_zero, hcast, hm]
    rfl
  have hsub : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) (b - g₀ ^ m)) < 1 :=
    valued_algebraMap_lt_one_of_mem K v ((Ideal.Quotient.eq_zero_iff_mem).mp hres)
  refine ⟨m, ?_⟩
  show Valued.v ((w : v.adicCompletion K)
    - (algebraMap (𝓞 K) (v.adicCompletion K) g₀) ^ m) < 1
  have hsplit : (w : v.adicCompletion K) - (algebraMap (𝓞 K) (v.adicCompletion K) g₀) ^ m
      = ((w : v.adicCompletion K) - algebraMap (𝓞 K) (v.adicCompletion K) b)
        + algebraMap (𝓞 K) (v.adicCompletion K) (b - g₀ ^ m) := by
    rw [map_sub, map_pow]
    ring
  rw [hsplit]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hblt hsub)

variable (K) in
/-- **Every unit of the valuation ring of the completion is a power of one fixed unit times an
`n`-th power**, for an exponent prime to the residue characteristic.  The residue field is cyclic
and the units congruent to one are `n`-th powers. -/
theorem exists_unitGen_pow_mul_pow (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime)
    (hmem : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) {n : ℕ} (hn : n ≠ 0) (hpn : ¬ p ∣ n) :
    ∃ g : (v.adicCompletion K)ˣ, ∀ u : (v.adicCompletion K)ˣ,
      unitVal (Additive.ofMul u) = 0 →
        ∃ (m : ℕ) (y : (v.adicCompletion K)ˣ), u = g ^ m * y ^ n := by
  obtain ⟨e, hres⟩ := exists_hasResidueChar_of_mem hp v hmem
  obtain ⟨g, hgval, hgen⟩ := exists_unitGen_adicCompletion K v
  refine ⟨g, fun u hu => ?_⟩
  exact exists_pow_mul_pow_eq_of_unitGen hres hn hpn hgval hgen
    (mem_ker_unitVal.mp (AddMonoidHom.mem_ker.mpr hu))

end AdicUnitGen

end InverseGalois.CFT

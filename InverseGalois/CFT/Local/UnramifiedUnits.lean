/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnitHerbrandChain
import InverseGalois.CFT.Tate.CyclicHilbert90

/-!
# The units of the valuation ring of an unramified extension

A finite cyclic group acting faithfully by isometries on a valued field is called unramified when
the subfield it fixes already contains an element of valuation one step below the top, a
uniformizer.  For such an action both Tate groups of the units of the valuation ring vanish, not
merely their quotient.

Hilbert's theorem 90 writes an element of the unit group of the field whose conjugates multiply to
one as a quotient `σ y / y`, and `y` is determined only up to a factor from the fixed field.  A
uniformizer in the fixed field lets that factor absorb the valuation of `y`, so `y` may be chosen a
unit of the valuation ring; this makes `Ĥ⁻¹` of the units of the valuation ring vanish.  The
Herbrand quotient of those units is one, so `Ĥ⁰` has the same, finite, order as `Ĥ⁻¹` and vanishes
as well.

## Main results

* `InverseGalois.CFT.subsingleton_tateHm1_kerUnitValAut`: **`Ĥ⁻¹` of the units of the valuation ring
  vanishes** when the fixed field contains a uniformizer.
* `InverseGalois.CFT.subsingleton_tateH0_kerUnitValAut`: **`Ĥ⁰` of the units of the valuation ring
  vanishes** under the same hypothesis.

## Tags

unramified extension, Hilbert theorem 90, Tate cohomology, local units
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {G A : Type*} [Group G] [Fintype G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  [FaithfulSMul G A] {p e : ℕ}

variable (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

include hv

/-! ### A uniformizer in the fixed field -/

omit [Fintype G] [Valued A ℤᵐ⁰] [FaithfulSMul G A] hv in
/-- A power of a unit fixed by the group is fixed by the group. -/
theorem unitsSmulAut_zpow_eq (σ : G) {π : Aˣ} (hπ : unitsSmulAut A σ π = π) (k : ℤ) :
    unitsSmulAut A σ (π ^ k) = π ^ k := by
  rw [map_zpow, hπ]

omit [Fintype G] [FaithfulSMul G A] hv in
/-- The valuation of a power of a uniformizer is the exponent. -/
theorem unitVal_zpow (π : Aˣ) (hπ : unitVal (Additive.ofMul π) = 1) (k : ℤ) :
    unitVal (Additive.ofMul (π ^ k)) = k := by
  rw [show Additive.ofMul (π ^ k) = k • Additive.ofMul π from rfl, AddMonoidHom.map_zsmul, hπ,
    smul_eq_mul, mul_one]

/-! ### The lower Tate group of the units of the valuation ring -/

/-- **`Ĥ⁻¹` of the units of the valuation ring vanishes** when the fixed field contains a
uniformizer.  Hilbert's theorem 90 produces a quotient representation in the unit group of the
field, and the uniformizer corrects the valuation of the representative. -/
theorem subsingleton_tateHm1_kerUnitValAut {σ : G} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {d : ℕ} (hcard : Nat.card G = d) (π : Aˣ) (hπfix : ∀ g : G, g • (π : A) = (π : A))
    (hπval : unitVal (Additive.ofMul π) = 1) :
    Subsingleton (tateHm1 (kerUnitValAut hv σ) d) := by
  have hπu : unitsSmulAut A σ π = π := Units.ext (by rw [coe_unitsSmulAut]; exact hπfix σ)
  have key : ∀ c : tateHm1 (kerUnitValAut hv σ) d, c = 0 := by
    intro c
    obtain ⟨z, hz, rfl⟩ := tateHm1.mk_surjective c
    set u : Aˣ := Additive.toMul (z : Additive Aˣ) with hu
    -- the class has norm zero in the unit group of the field
    have hnorm : normHom (smulUnitsAut (R := A) σ) d (z : Additive Aˣ) = 0 := by
      have hmap := map_normHom ((unitVal (A := A)).ker.subtype)
        (fun _ => rfl : ∀ a, ((unitVal (A := A)).ker.subtype) (kerUnitValAut hv σ a)
          = smulUnitsAut σ (((unitVal (A := A)).ker.subtype) a)) d z
      rw [hz] at hmap
      exact hmap.symm
    have hprod1 : ∏ i ∈ Finset.range d, (unitsSmulAut A σ ^ i) u = 1 := by
      have h1 : normHom (addAut (unitsSmulAut A σ)) d (Additive.ofMul u)
          = Additive.ofMul (∏ i ∈ Finset.range d, (unitsSmulAut A σ ^ i) u) :=
        normHom_ofMul _ _ _
      rw [show Additive.ofMul u = (z : Additive Aˣ) from rfl] at h1
      have h2 : Additive.ofMul (∏ i ∈ Finset.range d, (unitsSmulAut A σ ^ i) u) = 0 := by
        rw [← h1]
        exact hnorm
      exact ofMul_eq_zero.mp h2
    have hprod : ∏ i ∈ Finset.range d, (σ ^ i) • (u : A) = 1 := by
      have hcoe : ((∏ i ∈ Finset.range d, (unitsSmulAut A σ ^ i) u : Aˣ) : A)
          = ∏ i ∈ Finset.range d, (((unitsSmulAut A σ ^ i) u : Aˣ) : A) :=
        map_prod (Units.coeHom A) _ _
      rw [← Finset.prod_congr rfl fun i (_ : i ∈ Finset.range d) => coe_unitsSmulAut_pow σ i u,
        ← hcoe, hprod1, Units.val_one]
    obtain ⟨y, hy⟩ := exists_smul_div_eq_of_prod_smul_eq_one hgen hcard u hprod
    -- correct the valuation of the representative by a power of the uniformizer
    set n : ℤ := unitVal (Additive.ofMul y) with hn
    set w : Aˣ := y * π ^ (-n) with hw
    have hwval : Additive.ofMul w ∈ (unitVal (A := A)).ker := by
      rw [AddMonoidHom.mem_ker, show Additive.ofMul w = Additive.ofMul y + Additive.ofMul (π ^ (-n))
        from rfl, map_add, unitVal_zpow π hπval, ← hn, add_neg_cancel]
    have hyu : unitsSmulAut A σ y / y = u := by
      refine Units.ext ?_
      rw [Units.val_div_eq_div_val, coe_unitsSmulAut]
      exact hy
    have hwu : unitsSmulAut A σ w / w = u := by
      rw [hw, map_mul, unitsSmulAut_zpow_eq σ hπu, ← hyu, mul_div_mul_comm, div_self', mul_one]
    refine (tateHm1.mk_eq_zero_iff _ _).mpr ⟨⟨Additive.ofMul w, hwval⟩, Subtype.ext ?_⟩
    show smulUnitsAut (R := A) σ (Additive.ofMul w) - Additive.ofMul w = (z : Additive Aˣ)
    rw [show smulUnitsAut (R := A) σ (Additive.ofMul w) - Additive.ofMul w
      = sigmaSubOne (addAut (unitsSmulAut A σ)) (Additive.ofMul w) from rfl, sigmaSubOne_ofMul,
      hwu]
    rfl
  exact ⟨fun a b => by rw [key a, key b]⟩

/-! ### The upper Tate group of the units of the valuation ring -/

variable [CompleteSpace A]

/-- **`Ĥ⁰` of the units of the valuation ring vanishes** when the fixed field contains a
uniformizer.  The Herbrand quotient of those units is one, so the two Tate groups have the same
finite order, and the lower one is trivial. -/
theorem subsingleton_tateH0_kerUnitValAut [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) {σ : G} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d]
    (hσ : σ ^ d = 1) (hcard : Nat.card G = d) (π : Aˣ) (hπfix : ∀ g : G, g • (π : A) = (π : A))
    (hπval : unitVal (Additive.ofMul π) = 1) :
    Subsingleton (tateH0 (kerUnitValAut hv σ) d) := by
  haveI hsub := subsingleton_tateHm1_kerUnitValAut hv hgen hcard π hπfix hπval
  obtain ⟨hf0, hfm⟩ := finite_tate_kerUnitValAut hv h hgen hσ hcard
  haveI := hf0
  haveI := hfm
  have hq : herbrand (kerUnitValAut hv σ) d = 1 := herbrand_kerUnitValAut_eq_one hv h hgen hσ hcard
  have hcm : Nat.card (tateHm1 (kerUnitValAut hv σ) d) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩
  rw [herbrand, hcm, Nat.cast_one, div_one] at hq
  have hc0 : Nat.card (tateH0 (kerUnitValAut hv σ) d) = 1 := by
    exact_mod_cast hq
  exact (Nat.card_eq_one_iff_unique.mp hc0).1

end InverseGalois.CFT

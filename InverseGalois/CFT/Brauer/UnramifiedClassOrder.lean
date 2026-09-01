/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicNorm
import InverseGalois.CFT.Local.UnitValuation
import InverseGalois.CFT.Tate.GaloisH0

/-!
# An unramified cyclic extension carries a Brauer class of its degree

The relative Brauer group of a cyclic extension is the units of the base field modulo the norms,
and that quotient is killed by the degree, because the norm of a scalar is its degree-th power.
On the other hand, when the extension is unramified the value of a norm is a degree-th power of a
value of the base field, so reading the value of a unit modulo the degree — which is possible
because a discrete valuation has a generator of its value group, and every multiple of it is a
value — gives a surjection of the quotient onto the integers modulo the degree.

An element of a group killed by the degree which maps to a generator of the integers modulo the
degree has order exactly the degree.  So an unramified cyclic extension of a discretely valued
field carries a Brauer class of order its degree.  Nothing here needs completeness, a finite
residue field, or the norm index: only the valuation of the base field.

## Main definitions

* `InverseGalois.CFT.HasUnramifiedNormValues`: the value of a norm from the extension is a
  degree-th power of a value of the base field.
* `InverseGalois.CFT.baseValInvariant`: the value of a unit of the base field, divided by a
  generator of the value group and read modulo the degree.

## Main results

* `InverseGalois.CFT.pow_finrank_eq_one_normQuotient`: the units modulo the norms are killed by the
  degree.
* `InverseGalois.CFT.finrank_dvd_unitValDiv_of_mem_normSubgroup`: the value of a norm, divided by a
  generator of the value group, is a multiple of the degree.
* `InverseGalois.CFT.normQuotientValInvariant_surjective`: **the units modulo the norms of an
  unramified extension surject onto the integers modulo the degree.**
* `InverseGalois.CFT.exists_orderOf_eq_finrank_relative`: **the relative Brauer group of an
  unramified cyclic extension of a discretely valued field contains a class of order the degree.**

## Tags

Brauer group, relative Brauer group, unramified extension, valuation, invariant map,
class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped WithZero

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-! ### The units modulo the norms are killed by the degree -/

/-- The degree-th power of a unit of the base field is a norm: it is the norm of the scalar. -/
theorem pow_finrank_mem_normSubgroup (a : Kˣ) : a ^ finrank K L ∈ normSubgroup K L :=
  (mem_normSubgroup_iff _).2 ⟨unitsAlgebraMap K L a, by
    rw [coe_unitsAlgebraMap, Algebra.norm_algebraMap, Units.val_pow_eq_pow_val]⟩

/-- **The units of the base field modulo the norms are killed by the degree.** -/
theorem pow_finrank_eq_one_normQuotient (x : Kˣ ⧸ normSubgroup K L) : x ^ finrank K L = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have h : (QuotientGroup.mk' (normSubgroup K L) a) ^ finrank K L = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact pow_finrank_mem_normSubgroup a
  exact h

/-! ### The invariant of an unramified extension -/

section Valued

variable [Valued K ℤᵐ⁰] {m : ℤ}

/-- **Unramifiedness, seen from the base field**: the value of a norm from the extension is a
degree-th power of a value of the base field. -/
def HasUnramifiedNormValues (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Valued K ℤᵐ⁰] : Prop :=
  ∀ y : Lˣ, ∃ c : Kˣ, Valued.v (Algebra.norm K (y : L)) = Valued.v (c : K) ^ finrank K L

/-- **The invariant of a unit of the base field**: its value, divided by a generator of the value
group and read modulo a given number. -/
noncomputable def baseValInvariant (hm : IsUnitValGen K m) (n : ℕ) :
    Kˣ →* Multiplicative (ZMod n) where
  toFun a := Multiplicative.ofAdd ((unitValDiv hm (Additive.ofMul a) : ZMod n))
  map_one' := by simp
  map_mul' a b := by simp only [ofMul_mul, map_add, Int.cast_add, ofAdd_add]

theorem baseValInvariant_apply (hm : IsUnitValGen K m) (n : ℕ) (a : Kˣ) :
    baseValInvariant hm n a
      = Multiplicative.ofAdd ((unitValDiv hm (Additive.ofMul a) : ZMod n)) :=
  rfl

/-- **The invariant is surjective**: a discrete valuation attains every multiple of a generator of
its value group. -/
theorem baseValInvariant_surjective (hm : IsUnitValGen K m) (n : ℕ) :
    Function.Surjective (baseValInvariant hm n) := by
  intro t
  obtain ⟨j, hj⟩ := ZMod.intCast_surjective (n := n) (Multiplicative.toAdd t)
  obtain ⟨x, hx⟩ := unitValDiv_surjective hm j
  refine ⟨Additive.toMul x, ?_⟩
  rw [baseValInvariant_apply, show Additive.ofMul (Additive.toMul x) = x from rfl, hx]
  simpa using congrArg Multiplicative.ofAdd hj

/-- **The value of a norm of an unramified extension is divisible by the degree.**  Divided by a
generator of the value group, the value of a norm is a degree-th multiple. -/
theorem finrank_dvd_unitValDiv_of_mem_normSubgroup (hur : HasUnramifiedNormValues K L)
    (hm : IsUnitValGen K m) {a : Kˣ} (ha : a ∈ normSubgroup K L) :
    (finrank K L : ℤ) ∣ unitValDiv hm (Additive.ofMul a) := by
  obtain ⟨y, hy⟩ := (mem_normSubgroup_iff a).1 ha
  obtain ⟨c, hc⟩ := hur y
  rw [hy] at hc
  have h1 : unitVal (Additive.ofMul a) = (finrank K L : ℤ) * unitVal (Additive.ofMul c) := by
    rw [unitVal_apply, unitVal_apply, hc, WithZero.log_pow, nsmul_eq_mul]
  have h2 : m * unitValDiv hm (Additive.ofMul a)
      = m * ((finrank K L : ℤ) * unitValDiv hm (Additive.ofMul c)) := by
    rw [← unitVal_eq_mul_unitValDiv hm, h1, unitVal_eq_mul_unitValDiv hm (Additive.ofMul c)]
    ring
  exact ⟨unitValDiv hm (Additive.ofMul c), mul_left_cancel₀ hm.ne_zero h2⟩

/-- **The invariant kills the norms of an unramified extension.** -/
theorem normSubgroup_le_ker_baseValInvariant (hur : HasUnramifiedNormValues K L)
    (hm : IsUnitValGen K m) :
    normSubgroup K L ≤ (baseValInvariant hm (finrank K L)).ker := by
  intro a ha
  obtain ⟨c, hc⟩ := finrank_dvd_unitValDiv_of_mem_normSubgroup hur hm ha
  rw [MonoidHom.mem_ker, baseValInvariant_apply, hc]
  simp

/-- The invariant of an unramified extension, on the units modulo the norms. -/
noncomputable def normQuotientValInvariant (hur : HasUnramifiedNormValues K L)
    (hm : IsUnitValGen K m) :
    (Kˣ ⧸ normSubgroup K L) →* Multiplicative (ZMod (finrank K L)) :=
  QuotientGroup.lift _ _ (normSubgroup_le_ker_baseValInvariant hur hm)

/-- **The units modulo the norms of an unramified extension surject onto the integers modulo the
degree.** -/
theorem normQuotientValInvariant_surjective (hur : HasUnramifiedNormValues K L)
    (hm : IsUnitValGen K m) : Function.Surjective (normQuotientValInvariant hur hm) := by
  intro t
  obtain ⟨a, ha⟩ := baseValInvariant_surjective hm (finrank K L) t
  exact ⟨QuotientGroup.mk a, ha⟩

/-- **The units modulo the norms of an unramified extension contain a class of order the degree.**
The quotient is killed by the degree, and it has an element whose invariant generates the integers
modulo the degree. -/
theorem exists_orderOf_eq_finrank_normQuotient (hur : HasUnramifiedNormValues K L)
    (hm : IsUnitValGen K m) :
    ∃ x : Kˣ ⧸ normSubgroup K L, orderOf x = finrank K L := by
  obtain ⟨x, hx⟩ := normQuotientValInvariant_surjective hur hm
    (Multiplicative.ofAdd (1 : ZMod (finrank K L)))
  refine ⟨x, Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (pow_finrank_eq_one_normQuotient x)) ?_⟩
  have hpow : normQuotientValInvariant hur hm x ^ orderOf x = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  rwa [hx, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one] at hdvd

/-! ### The Brauer class -/

/-- **The relative Brauer group of an unramified cyclic extension of a discretely valued field
contains a class of order the degree.**  It is the class of the cyclic algebra of a unit whose
value generates the value group.  This is the local ingredient of the fundamental class. -/
theorem exists_orderOf_eq_finrank_relative [IsGalois K L] {σ₀ : L ≃ₐ[K] L}
    (hσ₀ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ₀) (hur : HasUnramifiedNormValues K L)
    (hm : IsUnitValGen K m) :
    ∃ x : ↥(BrauerGroup.relative K L), orderOf x = finrank K L := by
  obtain ⟨x, hx⟩ := exists_orderOf_eq_finrank_normQuotient hur hm
  exact ⟨cyclicBrauerEquiv hσ₀ x, by rw [MulEquiv.orderOf_eq]; exact hx⟩

end Valued

end InverseGalois.CFT

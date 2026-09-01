/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicTower
import InverseGalois.CFT.Brauer.Tower
import InverseGalois.CFT.Brauer.UnramifiedClassOrder

/-!
# The invariant of a Brauer class split by an unramified cyclic extension

Let `K` be a discretely valued field and let `L / K` be a finite cyclic Galois extension which is
unramified, in the sense that the value of a norm from `L` is a degree-th power of a value of `K`.
The relative Brauer group `Br(L / K)` is the units of `K` modulo the norms from `L`, and the
value of a unit `a`, divided by a generator of the value group of `K` and by the degree `[L : K]`,
is a well-defined element of `ℚ / ℤ`.  This is the invariant of the Brauer class of the cyclic
algebra `(L / K, σ₀, a)`.

The point of dividing by the degree — rather than reading the value modulo the degree, as in
`InverseGalois.CFT.baseValInvariant` — is that the resulting invariant does not depend on the
extension used to split the class.  For a tower `K ⊆ L ⊆ L'` of cyclic extensions with a generator
`σ'` of `Gal(L' / K)` restricting to a generator `σ` of `Gal(L / K)`, the class of
`(L / K, σ, a)` is the class of `(L' / K, σ', a ^ [L' : L])`, whose invariant is
`[L' : L] · v(a) / [L' : K] = v(a) / [L : K]`.  So the invariants computed at the two levels of the
tower agree, and a compatible system of generators of the Galois groups of a tower of unramified
cyclic extensions gives a single invariant on the union of the relative Brauer groups.

## Main definitions

* `InverseGalois.CFT.QModZ`: the rationals modulo the integers.
* `InverseGalois.CFT.unitInvariant`: the value of a unit of the base field, divided by a generator
  of the value group and by a given number, read in `ℚ / ℤ`.
* `InverseGalois.CFT.brauerInvariant`: the invariant of a Brauer class split by an unramified
  cyclic extension.

## Main results

* `InverseGalois.CFT.unitInvariant_eq_zero_of_mem_normSubgroup`: the invariant kills the norms of
  an unramified extension.
* `InverseGalois.CFT.brauerInvariant_apply_cyclicBrauerHom`: the invariant of the class of a cyclic
  algebra is the invariant of its scalar.
* `InverseGalois.CFT.unitInvariant_pow_finrank` and
  `InverseGalois.CFT.brauerInvariant_tower`: **the invariant does not depend on the level of the
  tower.**

## Tags

Brauer group, relative Brauer group, unramified extension, valuation, invariant map,
class field theory
-/

open Module

namespace InverseGalois.CFT

open scoped WithZero

/-! ### The rationals modulo the integers -/

/-- **The rationals modulo the integers**, the value group of the invariant of a Brauer class of a
discretely valued field. -/
abbrev QModZ : Type := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/-- A rational vanishes modulo the integers exactly when it is an integer. -/
theorem QModZ.mk_eq_zero_iff (q : ℚ) :
    (QuotientAddGroup.mk q : QModZ) = 0 ↔ ∃ k : ℤ, (k : ℚ) = q := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
  exact exists_congr fun k => by rw [zsmul_eq_mul, mul_one]

/-- An integer vanishes modulo the integers. -/
theorem QModZ.mk_intCast (k : ℤ) : (QuotientAddGroup.mk (k : ℚ) : QModZ) = 0 :=
  (QModZ.mk_eq_zero_iff _).2 ⟨k, rfl⟩

/-! ### The integers modulo `n` inside the rationals modulo the integers -/

/-- The homomorphism of the integers into the rationals modulo the integers that divides by a given
number. -/
noncomputable def intQModZ (n : ℕ) : ℤ →+ QModZ :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).comp
    ((AddMonoidHom.mulRight ((n : ℚ))⁻¹).comp (Int.castAddHom ℚ))

theorem intQModZ_apply (n : ℕ) (k : ℤ) :
    intQModZ n k = QuotientAddGroup.mk ((k : ℚ) / (n : ℚ)) := by
  rw [div_eq_mul_inv]
  rfl

/-- Dividing the modulus by itself gives an integer. -/
theorem intQModZ_natCast_self (n : ℕ) : intQModZ n (n : ℤ) = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn]
    simp
  · have hne : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [intQModZ_apply]
    push_cast
    rw [div_self hne]
    exact (QModZ.mk_eq_zero_iff _).2 ⟨1, by norm_num⟩

/-- **The integers modulo `n`, inside the rationals modulo the integers.**  The class of `k` goes
to `k / n`. -/
noncomputable def zmodQModZ (n : ℕ) [NeZero n] : ZMod n →+ QModZ :=
  ZMod.lift n ⟨intQModZ n, intQModZ_natCast_self n⟩

theorem zmodQModZ_intCast (n : ℕ) [NeZero n] (k : ℤ) :
    zmodQModZ n (k : ZMod n) = QuotientAddGroup.mk ((k : ℚ) / (n : ℚ)) := by
  show ZMod.lift n ⟨intQModZ n, intQModZ_natCast_self n⟩ (k : ZMod n) = _
  rw [ZMod.lift_coe]
  exact intQModZ_apply n k

/-- **The embedding of the integers modulo `n` is injective.** -/
theorem zmodQModZ_injective (n : ℕ) [NeZero n] : Function.Injective (zmodQModZ n) := by
  have hne : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  show Function.Injective (ZMod.lift n ⟨intQModZ n, intQModZ_natCast_self n⟩)
  rw [ZMod.lift_injective]
  intro k hk
  have hk' : (QuotientAddGroup.mk ((k : ℚ) / (n : ℚ)) : QModZ) = 0 := by
    rw [← intQModZ_apply]
    exact hk
  obtain ⟨j, hj⟩ := (QModZ.mk_eq_zero_iff _).1 hk'
  have hkq : (k : ℚ) = (j : ℚ) * (n : ℚ) := (div_eq_iff hne).1 hj.symm
  have hkz : k = j * (n : ℤ) := by exact_mod_cast hkq
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨j, by rw [hkz, mul_comm]⟩

/-! ### The invariant of a unit -/

section Valued

variable {K : Type} [Field K] [Valued K ℤᵐ⁰] {m : ℤ}

/-- **The invariant of a unit of a discretely valued field**: its value, divided by a generator of
the value group and by a given number, read in the rationals modulo the integers. -/
noncomputable def unitInvariant (hm : IsUnitValGen K m) (n : ℕ) : Additive Kˣ →+ QModZ :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).comp
    (((AddMonoidHom.mulRight ((n : ℚ))⁻¹).comp (Int.castAddHom ℚ)).comp (unitValDiv hm))

theorem unitInvariant_apply (hm : IsUnitValGen K m) (n : ℕ) (x : Additive Kˣ) :
    unitInvariant hm n x = QuotientAddGroup.mk ((unitValDiv hm x : ℚ) / (n : ℚ)) := by
  rw [div_eq_mul_inv]
  rfl

/-- **The invariant is killed by the number one divides by.** -/
theorem nsmul_unitInvariant (hm : IsUnitValGen K m) (n : ℕ) (x : Additive Kˣ) :
    n • unitInvariant hm n x = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn, zero_smul]
  · have hne : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hq : (n : ℕ) • ((unitValDiv hm x : ℚ) / (n : ℚ)) = ((unitValDiv hm x : ℤ) : ℚ) := by
      rw [nsmul_eq_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ hne]
    calc n • unitInvariant hm n x
        = QuotientAddGroup.mk (n • ((unitValDiv hm x : ℚ) / (n : ℚ))) := by
          rw [unitInvariant_apply]
          exact (map_nsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) _ _).symm
      _ = QuotientAddGroup.mk ((unitValDiv hm x : ℚ)) := by rw [hq]
      _ = 0 := QModZ.mk_intCast _

/-- **The invariant attains the reciprocal of the number one divides by.** -/
theorem exists_unitInvariant_eq (hm : IsUnitValGen K m) (n : ℕ) :
    ∃ x : Additive Kˣ, unitInvariant hm n x = QuotientAddGroup.mk (1 / (n : ℚ)) := by
  obtain ⟨x, hx⟩ := unitValDiv_surjective hm 1
  exact ⟨x, by rw [unitInvariant_apply, hx, Int.cast_one]⟩

/-! ### The invariant of an unramified extension -/

section Extension

variable {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The invariant kills the norms of an unramified extension.** -/
theorem unitInvariant_eq_zero_of_mem_normSubgroup (hur : HasUnramifiedNormValues K L)
    (hm : IsUnitValGen K m) {a : Kˣ} (ha : a ∈ normSubgroup K L) :
    unitInvariant hm (finrank K L) (Additive.ofMul a) = 0 := by
  have hn : ((finrank K L : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp Module.finrank_pos)
  obtain ⟨c, hc⟩ := finrank_dvd_unitValDiv_of_mem_normSubgroup hur hm ha
  rw [unitInvariant_apply, hc]
  push_cast
  rw [mul_div_cancel_left₀ _ hn]
  exact QModZ.mk_intCast c

/-- The invariant of a unit of the base field, as a homomorphism into the rationals modulo the
integers written multiplicatively. -/
noncomputable def baseInvariant (hm : IsUnitValGen K m) (n : ℕ) : Kˣ →* Multiplicative QModZ where
  toFun a := Multiplicative.ofAdd (unitInvariant hm n (Additive.ofMul a))
  map_one' := by simp
  map_mul' a b := by simp only [ofMul_mul, map_add, ofAdd_add]

theorem baseInvariant_apply (hm : IsUnitValGen K m) (n : ℕ) (a : Kˣ) :
    baseInvariant hm n a = Multiplicative.ofAdd (unitInvariant hm n (Additive.ofMul a)) :=
  rfl

/-- **The invariant of an unramified extension kills the norms.** -/
theorem normSubgroup_le_ker_baseInvariant (hur : HasUnramifiedNormValues K L)
    (hm : IsUnitValGen K m) :
    normSubgroup K L ≤ (baseInvariant hm (finrank K L)).ker := by
  intro a ha
  rw [MonoidHom.mem_ker, baseInvariant_apply,
    unitInvariant_eq_zero_of_mem_normSubgroup hur hm ha]
  rfl

/-- The invariant of an unramified extension, on the units modulo the norms. -/
noncomputable def normQuotientInvariant (hur : HasUnramifiedNormValues K L)
    (hm : IsUnitValGen K m) : (Kˣ ⧸ normSubgroup K L) →* Multiplicative QModZ :=
  QuotientGroup.lift _ _ (normSubgroup_le_ker_baseInvariant hur hm)

theorem normQuotientInvariant_mk (hur : HasUnramifiedNormValues K L) (hm : IsUnitValGen K m)
    (a : Kˣ) :
    normQuotientInvariant hur hm (QuotientGroup.mk a) = baseInvariant hm (finrank K L) a :=
  rfl

/-! ### The invariant of a Brauer class -/

variable [IsGalois K L] {σ₀ : Gal(L/K)}

/-- **The invariant of a Brauer class split by an unramified cyclic extension.**  Every such class
is the class of a cyclic algebra `(L / K, σ₀, a)`, and its invariant is the value of `a`, divided
by a generator of the value group and by the degree. -/
noncomputable def brauerInvariant (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀)
    (hur : HasUnramifiedNormValues K L) (hm : IsUnitValGen K m) :
    ↥(BrauerGroup.relative K L) →* Multiplicative QModZ :=
  (normQuotientInvariant hur hm).comp (cyclicBrauerEquiv hσ₀).symm.toMonoidHom

/-- The invariant of the class of a cyclic algebra is the invariant of its scalar. -/
theorem brauerInvariant_apply_cyclicBrauerHom (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀)
    (hur : HasUnramifiedNormValues K L) (hm : IsUnitValGen K m) (a : Kˣ) :
    brauerInvariant hσ₀ hur hm ⟨cyclicBrauerHom hσ₀ a, cyclicBrauerHom_mem_relative hσ₀ a⟩
      = baseInvariant hm (finrank K L) a := by
  have h : (cyclicBrauerEquiv hσ₀) (QuotientGroup.mk a)
      = ⟨cyclicBrauerHom hσ₀ a, cyclicBrauerHom_mem_relative hσ₀ a⟩ :=
    Subtype.ext (coe_cyclicBrauerEquiv_mk hσ₀ a)
  rw [brauerInvariant, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← h,
    MulEquiv.symm_apply_apply, normQuotientInvariant_mk]

end Extension

end Valued

/-! ### Independence of the level of the tower -/

section Tower

variable {K L L' : Type} [Field K] [Field L] [Field L'] [Valued K ℤᵐ⁰] [Algebra K L]
  [Algebra K L'] [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L]
  [FiniteDimensional K L'] [IsGalois K L] [IsGalois K L'] {m : ℤ}

omit [IsGalois K L] [IsGalois K L'] in
/-- **The invariant of a scalar does not depend on the level of the tower.**  Raising the scalar to
the relative degree and dividing by the larger degree gives the same element of `ℚ / ℤ`. -/
theorem unitInvariant_pow_finrank (hm : IsUnitValGen K m) (a : Kˣ) :
    unitInvariant hm (finrank K L') (Additive.ofMul (a ^ finrank L L'))
      = unitInvariant hm (finrank K L) (Additive.ofMul a) := by
  haveI : Module.Finite L L' := FiniteDimensional.right K L L'
  have hfin : finrank K L * finrank L L' = finrank K L' := Module.finrank_mul_finrank K L L'
  have hd : ((finrank L L' : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp Module.finrank_pos)
  have hval : unitValDiv hm (Additive.ofMul (a ^ finrank L L'))
      = (finrank L L' : ℤ) * unitValDiv hm (Additive.ofMul a) := by
    have h : (Additive.ofMul (a ^ finrank L L') : Additive Kˣ)
        = (finrank L L') • (Additive.ofMul a) := rfl
    rw [h, map_nsmul, nsmul_eq_mul]
  have hq : (((finrank L L' : ℤ) * unitValDiv hm (Additive.ofMul a) : ℤ) : ℚ)
        / ((finrank K L * finrank L L' : ℕ) : ℚ)
      = ((unitValDiv hm (Additive.ofMul a) : ℤ) : ℚ) / ((finrank K L : ℕ) : ℚ) := by
    push_cast
    rw [mul_comm ((finrank K L : ℚ)) ((finrank L L' : ℚ)), mul_div_mul_left _ _ hd]
  rw [unitInvariant_apply, unitInvariant_apply, hval, ← hfin, hq]

/-- **The invariant of a Brauer class does not depend on the level of the tower.**  A class split
by the smaller extension has the same invariant computed there and computed in the larger
extension, provided the generators are compatible. -/
theorem brauerInvariant_tower {σ' : Gal(L'/K)}
    (hσ' : ∀ x : Gal(L'/K), x ∈ Subgroup.zpowers σ') (hur : HasUnramifiedNormValues K L)
    (hur' : HasUnramifiedNormValues K L') (hm : IsUnitValGen K m)
    (x : ↥(BrauerGroup.relative K L)) :
    brauerInvariant hσ' hur' hm ⟨(x : BrauerGroup K),
        BrauerGroup.relative_le_relative K L L' x.2⟩
      = brauerInvariant (forall_mem_zpowers_restrictNormal (L := L) hσ') hur hm x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨a, rfl⟩ :=
    exists_cyclicBrauerHom_eq (forall_mem_zpowers_restrictNormal (L := L) hσ') x hx
  have hsub : (⟨cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := L) hσ') a,
        BrauerGroup.relative_le_relative K L L' hx⟩ : ↥(BrauerGroup.relative K L'))
      = ⟨cyclicBrauerHom hσ' (a ^ finrank L L'),
        cyclicBrauerHom_mem_relative hσ' (a ^ finrank L L')⟩ :=
    Subtype.ext (cyclicBrauerHom_restrictNormal hσ' a)
  rw [hsub, brauerInvariant_apply_cyclicBrauerHom, brauerInvariant_apply_cyclicBrauerHom,
    baseInvariant_apply, baseInvariant_apply, unitInvariant_pow_finrank]

end Tower

end InverseGalois.CFT

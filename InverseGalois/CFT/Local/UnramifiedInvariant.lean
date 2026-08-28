/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnramifiedUnits

/-!
# The invariant of an unramified cyclic extension of a valued field

For a finite cyclic group acting faithfully by isometries on a valued field whose fixed field
contains a uniformizer, the valuation identifies the Tate group `Ĥ⁰` of the multiplicative group
with the integers modulo the order of the group.  This is the local invariant map of class field
theory in the unramified case, and it is the first piece of the reciprocity law.

The valuation is invariant, so it descends to the fixed points, and the valuation of a norm is the
order of the group times the valuation of the argument; that gives a homomorphism to the integers
modulo that order.  A uniformizer in the fixed field has valuation one, so the homomorphism is
surjective.  It is injective because an invariant unit whose valuation is divisible by the order of
the group differs from a norm by a unit of the valuation ring, and on those units the norm is
already surjective onto the invariants.

## Main results

* `InverseGalois.CFT.unramifiedInvariant`: **the invariant map**, from `Ĥ⁰` of the multiplicative
  group to the integers modulo the order of the group.
* `InverseGalois.CFT.unramifiedInvariant_surjective`: it is surjective as soon as the fixed field
  contains a uniformizer.
* `InverseGalois.CFT.unramifiedInvariant_injective`: it is injective for an unramified action.
* `InverseGalois.CFT.unramifiedInvariantEquiv`: **`Ĥ⁰` of the multiplicative group of an unramified
  cyclic extension is the integers modulo the degree.**

## Tags

unramified extension, invariant map, local class field theory, Tate cohomology, valuation
-/

namespace InverseGalois.CFT

open scoped WithZero

/-! ### The valuation of a norm -/

section Invariant

variable {G A : Type*} [Group G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]

omit [Valued A ℤᵐ⁰] in
/-- A unit of the field fixed by an automorphism is fixed by the induced additive
automorphism. -/
theorem smulUnitsAut_ofMul_eq_self {σ : G} {π : Aˣ} (hπ : σ • (π : A) = (π : A)) :
    smulUnitsAut (R := A) σ (Additive.ofMul π) = Additive.ofMul π :=
  Additive.toMul.injective (Units.ext (by rw [coe_smulUnitsAut_apply, toMul_ofMul]; exact hπ))

variable (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

include hv

/-- **The valuation of a norm is the order of the group times the valuation.**  The group acts by
isometries, so the valuation carries the norm map of the multiplicative group to multiplication by
the order of the group on the integers. -/
theorem unitVal_normHom_smulUnitsAut (σ : G) (d : ℕ) (y : Additive Aˣ) :
    unitVal (normHom (smulUnitsAut (R := A) σ) d y) = (d : ℤ) * unitVal y := by
  rw [map_normHom (σA := smulUnitsAut (R := A) σ) (σB := (1 : ℤ ≃+ ℤ)) (unitVal (A := A))
    (fun a => unitVal_smulUnitsAut hv σ a) d y, normHom_one_apply, nsmul_eq_mul]

/-- **The invariant map** of a cyclic group of isometries of a valued field: the valuation, read
modulo the order of the group, on the Tate group `Ĥ⁰` of the multiplicative group. -/
noncomputable def unramifiedInvariant (σ : G) (d : ℕ) :
    tateH0 (smulUnitsAut (R := A) σ) d →+ ZMod d :=
  QuotientAddGroup.lift _
    ((Int.castAddHom (ZMod d)).comp
      ((unitVal (A := A)).comp (sigmaSubOne (smulUnitsAut (R := A) σ)).ker.subtype))
    (by
      intro x hmem
      obtain ⟨y, hy⟩ := AddSubgroup.mem_addSubgroupOf.mp hmem
      show ((unitVal (x : Additive Aˣ) : ℤ) : ZMod d) = 0
      rw [← hy, unitVal_normHom_smulUnitsAut hv, Int.cast_mul, Int.cast_natCast,
        ZMod.natCast_self, zero_mul])

@[simp]
theorem unramifiedInvariant_mk (σ : G) (d : ℕ) (x : Additive Aˣ)
    (hx : smulUnitsAut (R := A) σ x = x) :
    unramifiedInvariant hv σ d (tateH0.mk (smulUnitsAut (R := A) σ) d x hx)
      = ((unitVal x : ℤ) : ZMod d) := rfl

/-- **The invariant map is surjective** as soon as the fixed field contains a uniformizer: the
class of the uniformizer has invariant one. -/
theorem unramifiedInvariant_surjective (σ : G) (d : ℕ) {π : Aˣ} (hπfix : σ • (π : A) = (π : A))
    (hπval : unitVal (Additive.ofMul π) = 1) :
    Function.Surjective (unramifiedInvariant hv σ d) := by
  intro a
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
  refine ⟨tateH0.mk (smulUnitsAut (R := A) σ) d (k • Additive.ofMul π)
    (by rw [map_zsmul, smulUnitsAut_ofMul_eq_self hπfix]), ?_⟩
  rw [unramifiedInvariant_mk, map_zsmul, hπval]
  simp

end Invariant

/-! ### The invariant of an unramified extension -/

section Unramified

variable {G A : Type*} [Group G] [Fintype G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  [FaithfulSMul G A] [CompleteSpace A] {p e : ℕ}

variable (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

include hv

/-- **The invariant map of an unramified cyclic extension is injective.**  An invariant unit whose
valuation is divisible by the degree differs, by a norm of a power of the uniformizer, from a unit
of the valuation ring, and there the norm map is already surjective onto the invariants. -/
theorem unramifiedInvariant_injective [∀ k : ℤ, Finite (gradedAdd A k)] (h : HasResidueChar A p e)
    {σ : G} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d] (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) (π : Aˣ) (hπfix : ∀ g : G, g • (π : A) = (π : A))
    (hπval : unitVal (Additive.ofMul π) = 1) :
    Function.Injective (unramifiedInvariant hv σ d) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, hx, rfl⟩ := tateH0.mk_surjective c
  rw [unramifiedInvariant_mk, ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
  obtain ⟨m, hm⟩ := hc
  set P := normHom (smulUnitsAut (R := A) σ) d (m • Additive.ofMul π) with hP
  have hPval : unitVal P = (d : ℤ) * m := by
    rw [hP, unitVal_normHom_smulUnitsAut hv, map_zsmul, hπval]
    simp
  have hPfix : smulUnitsAut (R := A) σ P = P :=
    (mem_ker_sigmaSubOne_iff _ _).mp
      (range_normHom_le_ker_sigmaSubOne _ (smulUnitsAut_pow_eq_one hσ) ⟨_, rfl⟩)
  have hwfix : smulUnitsAut (R := A) σ (x - P) = x - P := by rw [map_sub, hx, hPfix]
  have hwker : x - P ∈ (unitVal (A := A)).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, hm, hPval, sub_self]
  obtain ⟨y, hy⟩ := exists_normHom_kerUnitVal hv h hgen hσ hcard π hπfix hπval ⟨x - P, hwker⟩
    (Subtype.ext hwfix)
  have hyval : normHom (smulUnitsAut (R := A) σ) d (y : Additive Aˣ) = x - P := by
    have hmap := map_normHom (σA := kerUnitValAut hv σ) (σB := smulUnitsAut (R := A) σ)
      (unitVal (A := A)).ker.subtype (fun _ => rfl) d y
    rw [hy] at hmap
    exact hmap.symm
  refine (tateH0.mk_eq_zero_iff x hx).mpr ⟨(y : Additive Aˣ) + m • Additive.ofMul π, ?_⟩
  rw [map_add, hyval, ← hP, sub_add_cancel]

/-- **The Tate group `Ĥ⁰` of the multiplicative group of an unramified cyclic extension of a valued
field is the integers modulo the degree**, through the valuation. -/
noncomputable def unramifiedInvariantEquiv [∀ k : ℤ, Finite (gradedAdd A k)]
    (h : HasResidueChar A p e) {σ : G} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d]
    (hσ : σ ^ d = 1) (hcard : Nat.card G = d) (π : Aˣ) (hπfix : ∀ g : G, g • (π : A) = (π : A))
    (hπval : unitVal (Additive.ofMul π) = 1) :
    tateH0 (smulUnitsAut (R := A) σ) d ≃+ ZMod d :=
  AddEquiv.ofBijective (unramifiedInvariant hv σ d)
    ⟨unramifiedInvariant_injective hv h hgen hσ hcard π hπfix hπval,
      unramifiedInvariant_surjective hv σ d (hπfix σ) hπval⟩

end Unramified

end InverseGalois.CFT

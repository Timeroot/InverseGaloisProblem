/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.CyclicAction
import InverseGalois.CFT.Tate.OrbitTwist

/-!
# Transporting a family indexed by an orbit to a single point

A cyclic group acting transitively on a finite set carries a family of copies of a module indexed by
that set to itself, each component moving to a different index.  Choosing for every point the power
of the generator that reaches it from a fixed base point identifies all of the components with the
component at the base point, and turns the action of the generator into a shift of the index
together with a rescaling: the rescaling is trivial except at the point from which the shift wraps
around, where it is a full turn of the orbit.

This is the arithmetic of the local factor of the group of ideles at a place of the base field.  The
places above it form one orbit, and the rescaling that survives is the action of the decomposition
group of the chosen place.

## Main definitions

* `InverseGalois.CFT.orbitShift`: the permutation of the set by the inverse of a group element.
* `InverseGalois.CFT.orbitSection`: the chosen group element carrying the base point to a point.
* `InverseGalois.CFT.orbitCocycle`: **the rescaling left over after the transport.**
* `InverseGalois.CFT.orbitTurn`: a full turn of the orbit, as an element of the stabiliser.

## Main results

* `InverseGalois.CFT.orbitCocycle_of_ne`: the rescaling is trivial away from the wrap-around.
* `InverseGalois.CFT.orbitCocycle_neg_one`: at the wrap-around it is a full turn.
* `InverseGalois.CFT.herbrand_twistShiftAut_orbitCocycle`: **the Herbrand quotient of the
  transported family is the Herbrand quotient of the module at the base point under a full turn.**
* `InverseGalois.CFT.mem_zpowers_orbitTurn`: **a full turn generates the stabiliser** of the base
  point.
* `InverseGalois.CFT.exists_normHom_twistShiftAut_orbitCocycle`: **a fixed transported family is a
  norm as soon as its value at the base point is a norm for a full turn.**

## Tags

Tate cohomology, Herbrand quotient, orbit, cocycle, decomposition group, idele
-/

namespace InverseGalois.CFT

open MulAction

/-! ### The shift of an orbit -/

section Shift

variable {G X : Type*} [Group G] [MulAction G X]

variable (X) in
/-- **The permutation of a set by the inverse of a group element.** -/
def orbitShift (σ : G) : Equiv.Perm X := toPerm σ⁻¹

@[simp]
theorem orbitShift_apply (σ : G) (x : X) : orbitShift X σ x = σ⁻¹ • x := rfl

/-- A power of the shift is the inverse of the corresponding power of the group element. -/
theorem pow_orbitShift_apply (σ : G) (k : ℕ) (x : X) :
    ((orbitShift X σ) ^ k) x = (σ ^ k)⁻¹ • x := by
  rw [show orbitShift X σ = (toPerm σ⁻¹ : Equiv.Perm X) from rfl, pow_toPerm_apply, inv_pow]

end Shift

/-! ### A full turn of the orbit -/

section Turn

variable {G X : Type*} [Group G] [MulAction G X] [Fintype X] {σ : G} (x₀ : X)

omit [Fintype X] in
/-- **A full turn of the orbit fixes the base point.** -/
theorem pow_period_smul : σ ^ period (orbitShift X σ) x₀ • x₀ = x₀ := by
  have h : ((orbitShift X σ) ^ period (orbitShift X σ) x₀) x₀ = x₀ :=
    (pow_apply_eq_self_iff _ x₀).mpr dvd_rfl
  rw [pow_orbitShift_apply] at h
  exact (inv_smul_eq_iff.mp h).symm

omit [Fintype X] in
/-- **A generator reaches every point of a transitive set by a natural power of the shift.** -/
theorem exists_pow_orbitShift_apply_eq [Finite G] [IsPretransitive G X]
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (y : X) :
    ∃ k : ℕ, ((orbitShift X σ) ^ k) x₀ = y :=
  exists_pow_smul_eq (fun g => by rw [Subgroup.zpowers_inv]; exact hgen g) x₀ y

end Turn

/-! ### The section and its cocycle -/

section Cocycle

variable {G X : Type*} [Group G] [MulAction G X] [Fintype X] {σ : G} (x₀ : X)
  (htrans : ∀ y : X, ∃ k : ℕ, ((orbitShift X σ) ^ k) x₀ = y)

/-- **The index of a point of a transitive orbit.** -/
noncomputable def orbitIdx (x : X) : ZMod (period (orbitShift X σ) x₀) :=
  (orbitEquiv (orbitShift X σ) x₀ htrans).symm x

theorem orbitIdx_orbitPoint (j : ZMod (period (orbitShift X σ) x₀)) :
    orbitIdx x₀ htrans (orbitPoint (orbitShift X σ) x₀ j) = j :=
  (orbitEquiv (orbitShift X σ) x₀ htrans).symm_apply_apply j

/-- **The chosen group element carrying the base point to a point** of its orbit. -/
noncomputable def orbitSection (x : X) : G := (σ ^ (orbitIdx x₀ htrans x).val)⁻¹

theorem orbitSection_smul (x : X) : orbitSection x₀ htrans x • x₀ = x := by
  show (σ ^ (orbitIdx x₀ htrans x).val)⁻¹ • x₀ = x
  rw [← pow_orbitShift_apply]
  exact (orbitEquiv (orbitShift X σ) x₀ htrans).apply_symm_apply x

theorem orbitSection_orbitPoint (j : ZMod (period (orbitShift X σ) x₀)) :
    orbitSection x₀ htrans (orbitPoint (orbitShift X σ) x₀ j) = (σ ^ j.val)⁻¹ := by
  show (σ ^ (orbitIdx x₀ htrans (orbitPoint (orbitShift X σ) x₀ j)).val)⁻¹ = _
  rw [orbitIdx_orbitPoint]

variable (σ) in
/-- **The rescaling left over after transporting the components of the orbit to the base point.**
-/
noncomputable def orbitCocycle (x : X) : G :=
  (orbitSection x₀ htrans x)⁻¹ * σ * orbitSection x₀ htrans (σ⁻¹ • x)

/-- The rescaling fixes the base point. -/
theorem orbitCocycle_smul (x : X) : orbitCocycle σ x₀ htrans x • x₀ = x₀ := by
  show ((orbitSection x₀ htrans x)⁻¹ * σ * orbitSection x₀ htrans (σ⁻¹ • x)) • x₀ = x₀
  rw [mul_smul, mul_smul, orbitSection_smul, smul_inv_smul, inv_smul_eq_iff, orbitSection_smul]

/-- **The rescaling is trivial away from the wrap-around.** -/
theorem orbitCocycle_of_ne {j : ZMod (period (orbitShift X σ) x₀)} (hj : j ≠ -1) :
    orbitCocycle σ x₀ htrans (orbitPoint (orbitShift X σ) x₀ j) = 1 := by
  show (orbitSection x₀ htrans (orbitPoint (orbitShift X σ) x₀ j))⁻¹ * σ
    * orbitSection x₀ htrans (σ⁻¹ • orbitPoint (orbitShift X σ) x₀ j) = 1
  rw [show σ⁻¹ • orbitPoint (orbitShift X σ) x₀ j = orbitPoint (orbitShift X σ) x₀ (j + 1) from
      apply_orbitPoint (orbitShift X σ) x₀ j,
    orbitSection_orbitPoint, orbitSection_orbitPoint, val_add_one_of_ne hj, inv_inv,
    pow_succ, mul_inv_cancel]

/-- **At the wrap-around the rescaling is a full turn of the orbit.** -/
theorem orbitCocycle_neg_one :
    orbitCocycle σ x₀ htrans (orbitPoint (orbitShift X σ) x₀ (-1))
      = σ ^ period (orbitShift X σ) x₀ := by
  have hd : 0 < period (orbitShift X σ) x₀ := NeZero.pos _
  show (orbitSection x₀ htrans (orbitPoint (orbitShift X σ) x₀ (-1)))⁻¹ * σ
    * orbitSection x₀ htrans (σ⁻¹ • orbitPoint (orbitShift X σ) x₀ (-1)) = _
  rw [show σ⁻¹ • orbitPoint (orbitShift X σ) x₀ (-1)
        = orbitPoint (orbitShift X σ) x₀ (-1 + 1) from
      apply_orbitPoint (orbitShift X σ) x₀ (-1),
    neg_add_cancel, orbitSection_orbitPoint, orbitSection_orbitPoint, ZMod.val_zero, pow_zero,
    inv_one, mul_one, val_neg_one_zmod _, inv_inv, ← pow_succ, Nat.sub_add_cancel hd]

end Cocycle

/-! ### The Herbrand quotient of a transported family -/

section Herbrand

variable {G X : Type*} [Group G] [MulAction G X] [Fintype X] {σ : G} (x₀ : X)
  (htrans : ∀ y : X, ∃ k : ℕ, ((orbitShift X σ) ^ k) x₀ = y)
  {H : Subgroup G} (hH : ∀ g : G, g • x₀ = x₀ → g ∈ H)

/-- The rescaling, valued in a subgroup containing the stabiliser of the base point. -/
noncomputable def orbitCocycleSub (x : X) : ↥H :=
  ⟨orbitCocycle σ x₀ htrans x, hH _ (orbitCocycle_smul x₀ htrans x)⟩

theorem orbitCocycleSub_coe (x : X) :
    (orbitCocycleSub x₀ htrans hH x : G) = orbitCocycle σ x₀ htrans x := rfl

variable (σ) in
/-- **A full turn of the orbit**, as an element of a subgroup containing the stabiliser of the base
point. -/
noncomputable def orbitTurn : ↥H := ⟨σ ^ period (orbitShift X σ) x₀, hH _ (pow_period_smul x₀)⟩

omit [Fintype X] in
theorem orbitTurn_coe : (orbitTurn σ x₀ hH : G) = σ ^ period (orbitShift X σ) x₀ := rfl

omit [Fintype X] in
/-- A full turn has the order that a generator has. -/
theorem orbitTurn_pow {m n : ℕ} (hσ : σ ^ n = 1)
    (hn : period (orbitShift X σ) x₀ * m = n) : (orbitTurn σ x₀ hH) ^ m = 1 := by
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, orbitTurn_coe, ← pow_mul, hn, hσ]

omit [Fintype X] in
/-- **A full turn generates the stabiliser of the base point.** -/
theorem mem_zpowers_orbitTurn [Finite G] (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀) (y : ↥H) :
    y ∈ Subgroup.zpowers (orbitTurn σ x₀ hH) := by
  obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.2 (hgen (y : G))
  have hk' : σ ^ k = (y : G) := hk
  have hfix : ((orbitShift X σ) ^ k) x₀ = x₀ := by
    rw [pow_orbitShift_apply, hk', inv_smul_eq_iff, hH' y]
  obtain ⟨t, ht⟩ := (pow_apply_eq_self_iff (orbitShift X σ) x₀).mp hfix
  have hpow : (orbitTurn σ x₀ hH) ^ t = y := by
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, orbitTurn_coe, ← pow_mul, ← ht, hk']
  exact mem_powers_iff_mem_zpowers.1 ⟨t, hpow⟩

variable {B : Type*} [AddCommGroup B]

/-- **The Herbrand quotient of a family of copies of a module indexed by a transitive orbit** is the
Herbrand quotient of the module at the base point under a full turn.  Transporting the components
to the base point leaves a rescaling that is trivial except at the wrap-around, so the family is the
module induced from the stabiliser. -/
theorem herbrand_twistShiftAut_orbitCocycle (ρ : ↥H →* (B ≃+ B)) {m n : ℕ}
    (hz : (orbitTurn σ x₀ hH) ^ m = 1) (hn : period (orbitShift X σ) x₀ * m = n) :
    herbrand (twistShiftAut ρ (orbitCocycleSub x₀ htrans hH) (orbitShift X σ)) n
      = herbrand (ρ (orbitTurn σ x₀ hH)) m :=
  herbrand_twistShiftAut ρ (orbitShift X σ) x₀ htrans
    (fun _ hj => Subtype.ext (orbitCocycle_of_ne x₀ htrans hj))
    (Subtype.ext (orbitCocycle_neg_one x₀ htrans)) hz hn

/-- The upper Tate group of a family of copies of a module indexed by a transitive orbit vanishes
as soon as it vanishes for the module at the base point under a full turn. -/
theorem subsingleton_tateH0_twistShiftAut_orbitCocycle (ρ : ↥H →* (B ≃+ B)) {m n : ℕ}
    (hz : (orbitTurn σ x₀ hH) ^ m = 1) (hn : period (orbitShift X σ) x₀ * m = n)
    (h : Subsingleton (tateH0 (ρ (orbitTurn σ x₀ hH)) m)) :
    Subsingleton (tateH0 (twistShiftAut ρ (orbitCocycleSub x₀ htrans hH) (orbitShift X σ)) n) :=
  subsingleton_tateH0_twistShiftAut ρ (orbitShift X σ) x₀ htrans
    (fun _ hj => Subtype.ext (orbitCocycle_of_ne x₀ htrans hj))
    (Subtype.ext (orbitCocycle_neg_one x₀ htrans)) hz hn h

/-- **A fixed family of copies of a module indexed by a transitive orbit is a norm as soon as its
value at the base point is a norm for a full turn.** -/
theorem exists_normHom_twistShiftAut_orbitCocycle (ρ : ↥H →* (B ≃+ B)) {m n : ℕ}
    (hz : (orbitTurn σ x₀ hH) ^ m = 1) (hn : period (orbitShift X σ) x₀ * m = n)
    {f : X → B} (hf : twistShiftAut ρ (orbitCocycleSub x₀ htrans hH) (orbitShift X σ) f = f)
    (h : ∃ b, normHom (ρ (orbitTurn σ x₀ hH)) m b = f x₀) :
    ∃ u, normHom (twistShiftAut ρ (orbitCocycleSub x₀ htrans hH) (orbitShift X σ)) n u = f :=
  exists_normHom_twistShiftAut ρ (orbitShift X σ) x₀ htrans
    (fun _ hj => Subtype.ext (orbitCocycle_of_ne x₀ htrans hj))
    (Subtype.ext (orbitCocycle_neg_one x₀ htrans)) hz hn hf h

/-- The lower Tate group of a family of copies of a module indexed by a transitive orbit vanishes
as soon as it vanishes for the module at the base point under a full turn. -/
theorem subsingleton_tateHm1_twistShiftAut_orbitCocycle (ρ : ↥H →* (B ≃+ B)) {m n : ℕ}
    (hz : (orbitTurn σ x₀ hH) ^ m = 1) (hn : period (orbitShift X σ) x₀ * m = n)
    (h : Subsingleton (tateHm1 (ρ (orbitTurn σ x₀ hH)) m)) :
    Subsingleton (tateHm1 (twistShiftAut ρ (orbitCocycleSub x₀ htrans hH) (orbitShift X σ)) n) :=
  subsingleton_tateHm1_twistShiftAut ρ (orbitShift X σ) x₀ htrans
    (fun _ hj => Subtype.ext (orbitCocycle_of_ne x₀ htrans hj))
    (Subtype.ext (orbitCocycle_neg_one x₀ htrans)) hz hn h

end Herbrand

end InverseGalois.CFT

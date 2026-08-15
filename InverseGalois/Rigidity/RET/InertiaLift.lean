/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.SubUnramified

/-!
# Lifting distinguished inertia generators through a Galois subcover

A distinguished inertia element of a Galois subcover is the restriction of a distinguished inertia
element of the cover, and the lift can be prescribed exactly: the restriction map carries the
inertia group above a place onto the inertia group above the contracted place, both groups are
cyclic, and a generator of a cyclic quotient of a finite cyclic group is always the image of a
generator, because the reduction map between unit groups of `ZMod` is surjective.

## Main results

* `Rigidity.RET.exists_coprime_modEq` — a residue coprime to a divisor lifts to a residue coprime
  to the multiple.
* `Rigidity.RET.zpowers_pow_eq_of_coprime` — a power with exponent coprime to the order generates
  the same cyclic group.
* `Rigidity.RET.exists_pow_map_eq` — a generator of a finite cyclic group has a power mapping to
  any prescribed generator of its image.
* `Rigidity.RET.LineCover.exists_isInertiaGenAt` — every point of the line carries a distinguished
  inertia element.
* `Rigidity.RET.LineCover.IsInertiaGenAt.inv` and `Rigidity.RET.LineCover.IsInertiaGenAt.conj` —
  distinguished inertia elements are stable under inversion and under conjugation.
* `Rigidity.RET.LineCover.IsInertiaGenAt.exists_lift` — a distinguished inertia element of a Galois
  subcover is the restriction of a distinguished inertia element of the cover.
-/

open Polynomial
open scoped Pointwise

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

/-! ### Lifting a generator through a cyclic quotient -/

section Arith

/-- **A residue coprime to a divisor lifts to a residue coprime to the multiple.** -/
theorem exists_coprime_modEq {d m : ℕ} [NeZero m] (hdm : d ∣ m) {j : ℕ} (hj : Nat.Coprime j d) :
    ∃ i : ℕ, Nat.Coprime i m ∧ i ≡ j [MOD d] := by
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (n := d) hdm (ZMod.unitOfCoprime j hj)
  refine ⟨((u : ZMod m)).val, ZMod.val_coe_unit_coprime u, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have h1 : ((((u : ZMod m)).val : ℕ) : ZMod d) = ZMod.castHom hdm (ZMod d) (u : ZMod m) := by
    rw [ZMod.castHom_apply, ZMod.natCast_val]
  have h2 : ZMod.castHom hdm (ZMod d) (u : ZMod m)
      = ((ZMod.unitsMap hdm u : (ZMod d)ˣ) : ZMod d) := rfl
  rw [h1, h2, hu, ZMod.coe_unitOfCoprime]

/-- **A power with exponent coprime to the order generates the same cyclic group.** -/
theorem zpowers_pow_eq_of_coprime {G : Type*} [Group G] {x : G} {i : ℕ}
    (h : Nat.Coprime i (orderOf x)) : Subgroup.zpowers (x ^ i) = Subgroup.zpowers x := by
  refine le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i))
    (Subgroup.zpowers_le.mpr ?_)
  have hbez : (1 : ℤ) = (i : ℤ) * Nat.gcdA i (orderOf x)
      + (orderOf x : ℤ) * Nat.gcdB i (orderOf x) := by
    have := Nat.gcd_eq_gcd_ab i (orderOf x)
    rwa [h, Nat.cast_one] at this
  have key : x ^ ((i : ℤ) * Nat.gcdA i (orderOf x)) = x := by
    have h2 : (i : ℤ) * Nat.gcdA i (orderOf x)
        = 1 - (orderOf x : ℤ) * Nat.gcdB i (orderOf x) := by linarith
    rw [h2, zpow_sub, zpow_one, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, inv_one,
      mul_one]
  refine Subgroup.mem_zpowers_iff.mpr ⟨Nat.gcdA i (orderOf x), ?_⟩
  rw [← zpow_natCast x i, ← zpow_mul, key]

/-- **A generator of a finite cyclic group has a power mapping to any prescribed generator of its
image.** -/
theorem exists_pow_map_eq {G H : Type*} [Group G] [Finite G] [Group H] [Finite H] (f : G →* H)
    (x : G) {y : H} (hy : Subgroup.zpowers y = Subgroup.zpowers (f x)) :
    ∃ i : ℕ, Subgroup.zpowers (x ^ i) = Subgroup.zpowers x ∧ f (x ^ i) = y := by
  have hmpos : 0 < orderOf x := (isOfFinOrder_of_finite x).orderOf_pos
  haveI : NeZero (orderOf x) := ⟨hmpos.ne'⟩
  have hdm : orderOf (f x) ∣ orderOf x := orderOf_map_dvd f x
  have hdpos : 0 < orderOf (f x) := Nat.pos_of_dvd_of_pos hdm hmpos
  -- the prescribed generator is a power of the image
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (f x) ^ j = y :=
    (Submonoid.mem_powers_iff y (f x)).mp
      (mem_powers_iff_mem_zpowers.mpr (hy ▸ Subgroup.mem_zpowers y))
  -- its exponent is coprime to the order of the image
  have hcop : Nat.Coprime j (orderOf (f x)) := by
    have hord : orderOf y = orderOf (f x) := by
      rw [← Nat.card_zpowers, ← Nat.card_zpowers, hy]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [pow_zero] at hj
      have hone : orderOf (f x) = 1 := by rw [← hord, ← hj, orderOf_one]
      rw [hone]
      exact Nat.coprime_one_right _
    · have hpow : orderOf ((f x) ^ j) = orderOf (f x) / (orderOf (f x)).gcd j :=
        orderOf_pow' (f x) hjpos.ne'
      rw [hj, hord] at hpow
      have hmul : orderOf (f x) / (orderOf (f x)).gcd j * (orderOf (f x)).gcd j
          = orderOf (f x) := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
      rw [← hpow] at hmul
      have hg1 : (orderOf (f x)).gcd j = 1 :=
        Nat.eq_of_mul_eq_mul_left hdpos (hmul.trans (mul_one _).symm)
      rw [Nat.Coprime, Nat.gcd_comm]
      exact hg1
  -- lift the exponent to one coprime to the order upstairs
  obtain ⟨i, hicop, himod⟩ := exists_coprime_modEq (m := orderOf x) hdm hcop
  refine ⟨i, zpowers_pow_eq_of_coprime hicop, ?_⟩
  rw [map_pow, ← hj]
  exact pow_eq_pow_iff_modEq.mpr himod

end Arith

/-! ### Lifting a distinguished inertia element -/

namespace LineCover

variable {L : LineCover} {t : k} {σ : L.deck}

/-- A distinguished inertia element stays one when replaced by another generator of the same
cyclic group. -/
theorem IsInertiaGenAt.of_zpowers_eq (h : L.IsInertiaGenAt t σ) {σ' : L.deck}
    (hz : Subgroup.zpowers σ' = Subgroup.zpowers σ) : L.IsInertiaGenAt t σ' := by
  obtain ⟨Q, hmax, hover, hI⟩ := h
  exact ⟨Q, hmax, hover, hI.trans hz.symm⟩

/-- **Distinguished inertia elements are stable under inversion.** -/
theorem IsInertiaGenAt.inv (h : L.IsInertiaGenAt t σ) : L.IsInertiaGenAt t σ⁻¹ :=
  h.of_zpowers_eq Subgroup.zpowers_inv

/-- **Distinguished inertia elements are stable under conjugation.** -/
theorem IsInertiaGenAt.conj (h : L.IsInertiaGenAt t σ) (c : L.deck) :
    L.IsInertiaGenAt t (c * σ * c⁻¹) := by
  obtain ⟨Q, hmax, hover, hI⟩ := h
  haveI := hmax
  haveI : Q.IsPrime := hmax.isPrime
  haveI := hover
  haveI hmax' : (c • Q).IsMaximal := by
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _
      (MulSemiringAction.toRingAut L.deck (Bring L.M) c).symm.surjective
  haveI hover' : (c • Q).LiesOver (placeP t) :=
    ⟨by rw [Ideal.under_smul (Polynomial k) Q c]; exact hover.over⟩
  exact ⟨c • Q, hmax', hover', geomInertia_eq_zpowers_smul c Q hI⟩

/-- **Every point of the line carries a distinguished inertia element.** -/
theorem exists_isInertiaGenAt (L : LineCover) (t : k) : ∃ σ : L.deck, L.IsInertiaGenAt t σ := by
  obtain ⟨Q, hQmax, hQover⟩ := L.exists_place t
  haveI := hQmax
  haveI := hQover
  obtain ⟨σ, hσ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mp
    (GeomAKLB.isCyclic_geomInertia (Ω := L.M) t Q)
  exact ⟨σ, Q, hQmax, hQover, hσ.symm⟩

attribute [local instance] sub_isGalois

/-- **A distinguished inertia element of a Galois subcover is the restriction of a distinguished
inertia element of the cover.**

The two inertia groups are cyclic and the restriction maps one onto the other, so a generator
downstairs is the image of a generator upstairs. -/
theorem IsInertiaGenAt.exists_lift (L : LineCover) {E : IntermediateField (RatFunc k) L.M}
    [Normal (RatFunc k) E] {t : k} {τ : (L.sub E).deck}
    (h : (L.sub E).IsInertiaGenAt t τ) :
    ∃ σ : L.deck, L.IsInertiaGenAt t σ ∧ L.subHom E σ = τ := by
  obtain ⟨σ₀, hσ₀⟩ := L.exists_isInertiaGenAt t
  obtain ⟨c, hc⟩ := (IsInertiaGenAt.restrict L (E := E) hσ₀).exists_conj h
  obtain ⟨c', rfl⟩ := L.subHom_surjective E c
  -- conjugate the chosen inertia element so that its restriction generates the right group
  have hσ₁ : L.IsInertiaGenAt t (c' * σ₀ * c'⁻¹) := hσ₀.conj c'
  have hres : L.subHom E (c' * σ₀ * c'⁻¹)
      = L.subHom E c' * L.subHom E σ₀ * (L.subHom E c')⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [← hres] at hc
  obtain ⟨i, hzp, hmap⟩ := exists_pow_map_eq (L.subHom E) (c' * σ₀ * c'⁻¹) hc
  exact ⟨(c' * σ₀ * c'⁻¹) ^ i, hσ₁.of_zpowers_eq hzp, hmap⟩

end LineCover

end Rigidity.RET

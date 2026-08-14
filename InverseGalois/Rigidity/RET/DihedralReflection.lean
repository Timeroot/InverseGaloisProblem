/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.DihedralInfinity

/-!
# The reflection branch points of the inverted dihedral cover

The dihedral cover read in the coordinate `S = T⁻¹` is branched over `S = 0`, where the rotations
provide an inertia group of order `n`, and over the two points `S = ±1/2` inherited from the
branch points `T = ±2` of the standard model.  This file computes the local structure at those
two points.

Writing `V` for the rotation invariant and `E = 1 - V` for its complement, the coordinate satisfies
`S² = V·E`, and for a square root `a` of `1` the function

```
w = S - a·E
```

satisfies `w² = (S - a/2)·(-2a·E)`.  Away from the origin `E` is invertible, so the place over
`S = a/2` ramifies to order at least two.  In the other direction the function `z = u/(u^{2n} + 1)`
is invertible away from the origin and is scaled by a root of unity by every rotation, so no
nontrivial rotation is an inertia element there; two reflections in one inertia group differ by a
rotation, so the inertia group has order at most two.

## Main results

* `Rigidity.RET.card_geomInertia_inf_eq_two` — the inertia group over `S = ±1/2` has order two.
* `Rigidity.RET.isInertiaGenAt_dihInfCover` — a reflection generates it.
* `Rigidity.RET.branchLocus_dihInfCover` — the branch locus of the inverted cover is exactly the
  three points `0`, `1/2` and `-1/2`.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

variable {n : ℕ} [NeZero n]

/-! ### The places away from the origin -/

section Away

/-- **The coordinate is the geometric mean of the rotation invariant and its complement.** -/
theorem infS_sq (n : ℕ) [NeZero n] : (infS n) ^ 2 = infVB n * infEB n := by
  have h := infVB_quadratic n
  rw [infEB]
  linear_combination h

set_option synthInstance.maxHeartbeats 400000 in
/-- The coordinate does not lie in a place of the cover over a nonzero point of the base. -/
theorem infS_notMem (n : ℕ) [NeZero n] {c : k} (hc : c ≠ 0)
    (Q : Ideal (Bring (dihInfCover n).M)) [Q.IsMaximal] [Q.LiesOver (placeP c)] :
    infS n ∉ Q := by
  intro hS
  refine const_notMem (Ω := (dihInfCover n).M) Q hc ?_
  have hg := gen_mem_of_liesOver n c Q
  rw [map_sub] at hg
  have hsub := Ideal.sub_mem Q hS hg
  rw [infS, sub_sub_cancel] at hsub
  exact hsub

/-- **The complement of the rotation invariant is invertible away from the origin.**  Its product
with the rotation invariant is the square of the coordinate, which is invertible there. -/
theorem infEB_notMem (n : ℕ) [NeZero n] {c : k} (hc : c ≠ 0)
    (Q : Ideal (Bring (dihInfCover n).M)) [hQm : Q.IsMaximal] [Q.LiesOver (placeP c)] :
    infEB n ∉ Q := by
  haveI hQp : Q.IsPrime := hQm.isPrime
  intro hE
  refine infS_notMem n hc Q (hQp.mem_of_pow_mem 2 ?_)
  rw [infS_sq]
  exact Ideal.mul_mem_left _ _ hE

/-- **The `n`-th root of the coordinate is invertible away from the origin.** -/
theorem infZB_notMem (n : ℕ) [NeZero n] {c : k} (hc : c ≠ 0)
    (Q : Ideal (Bring (dihInfCover n).M)) [hQm : Q.IsMaximal] [Q.LiesOver (placeP c)] :
    infZB n ∉ Q := by
  haveI hQp : Q.IsPrime := hQm.isPrime
  intro hZ
  have hpow : infS n * (infEB n) ^ (n - 1) ∈ Q := by
    rw [← infZB_pow]
    exact Ideal.pow_mem_of_mem _ hZ _ (NeZero.pos n)
  rcases hQp.mem_or_mem hpow with h | h
  · exact infS_notMem n hc Q h
  · exact infEB_notMem n hc Q (hQp.mem_of_pow_mem (n - 1) h)

end Away

/-! ### No rotation is an inertia element away from the origin -/

section Rotations

variable {ζ : k}

set_option synthInstance.maxHeartbeats 400000 in
/-- A rotation of the inverted cover scales the `n`-th root of the coordinate by a root of
unity. -/
theorem smul_infZB_r (hζ : IsPrimitiveRoot ζ n) (i : ZMod n) :
    (dihInfDeckEquiv hζ (DihedralGroup.r i)) • infZB n
      = algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C (rootPow ζ i)) * infZB n := by
  have hden := dihDen_ne_zero n
  have hX : ((RatFunc.X : RatFunc k)) ≠ 0 := RatFunc.X_ne_zero
  have hζn : (rootPow ζ i) ^ (2 * n) = 1 := by
    rw [mul_comm, pow_mul, rootPow_pow hζ, one_pow]
  apply Subtype.ext
  rw [coe_smul_geom, Submonoid.coe_mul, Subalgebra.coe_algebraMap, coe_infZB]
  apply infLine_injective
  show dihedralAut hζ (DihedralGroup.r i) (infLine (infZ n))
    = infLine (algebraMap (Polynomial k) (dihInfCover n).M (C (rootPow ζ i)) * infZ n)
  have hcst : infLine (algebraMap (Polynomial k) (dihInfCover n).M (C (rootPow ζ i)))
      = algebraMap k (RatFunc k) (rootPow ζ i) := by
    rw [infLine_algebraMapPoly, Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
      AlgEquiv.commutes, AlgHom.commutes]
  have hζn' : (algebraMap k (RatFunc k) (rootPow ζ i)) ^ (2 * n) = 1 := by
    rw [← map_pow, hζn, map_one]
  rw [infLine_mul, hcst, dihedralAut_r]
  show (scaleAut (rootPow_ne_zero hζ i)) (infLine (infZ n)) = _
  simp only [infZ, infLine_ofInf, map_div₀, map_add, map_pow, map_one, scaleAut_X]
  rw [mul_pow, hζn', one_mul, mul_div_assoc]

/-- **No nontrivial rotation of the inverted cover is an inertia element away from the origin.** -/
theorem eq_zero_of_mem_geomInertia_of_r_inf (hζ : IsPrimitiveRoot ζ n) {c : k} (hc : c ≠ 0)
    (Q : Ideal (Bring (dihInfCover n).M)) [Q.IsMaximal] [Q.LiesOver (placeP c)] {i : ZMod n}
    (hmem : (dihInfDeckEquiv hζ (DihedralGroup.r i)) ∈ geomInertia (dihInfCover n).M Q) :
    i = 0 := by
  have hone : rootPow ζ i = 1 :=
    const_eq_one_of_mem_inertia (Ω := (dihInfCover n).M) Q hmem (infZB_notMem n hc Q)
      (smul_infZB_r hζ i)
  exact (rootPow_eq_one_iff hζ i).mp hone

/-- An inertia element of the inverted cover away from the origin, other than the identity, is a
reflection. -/
theorem exists_sr_of_mem_geomInertia_inf (hζ : IsPrimitiveRoot ζ n) {c : k} (hc : c ≠ 0)
    (Q : Ideal (Bring (dihInfCover n).M)) [Q.IsMaximal] [Q.LiesOver (placeP c)]
    {σ : (dihInfCover n).deck} (hmem : σ ∈ geomInertia (dihInfCover n).M Q) (hσ : σ ≠ 1) :
    ∃ j : ZMod n, σ = dihInfDeckEquiv hζ (DihedralGroup.sr j) := by
  obtain ⟨g, hg⟩ := (dihInfDeckEquiv hζ).surjective σ
  cases g with
  | r i =>
    refine absurd ?_ hσ
    have hi : i = 0 := eq_zero_of_mem_geomInertia_of_r_inf hζ hc Q (hg ▸ hmem)
    rw [← hg, hi]
    exact (dihInfDeckEquiv hζ).map_one
  | sr j => exact ⟨j, hg.symm⟩

/-- **Inertia in the inverted cover away from the origin has order at most two.**  Two reflections
in one inertia group differ by a rotation lying in that group, and no nontrivial rotation does. -/
theorem card_geomInertia_le_two_inf (n : ℕ) [NeZero n] {c : k} (hc : c ≠ 0)
    (Q : Ideal (Bring (dihInfCover n).M)) [Q.IsMaximal] [Q.LiesOver (placeP c)] :
    Nat.card (geomInertia (dihInfCover n).M Q) ≤ 2 := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_algebraicClosure n (dihPos n)
  -- an inertia group has at most one nontrivial element
  have key : ∀ σ ∈ geomInertia (dihInfCover n).M Q, ∀ τ ∈ geomInertia (dihInfCover n).M Q,
      σ ≠ 1 → τ ≠ 1 → σ = τ := by
    intro σ hσmem τ hτmem hσ hτ
    obtain ⟨j, hj⟩ := exists_sr_of_mem_geomInertia_inf hζ hc Q hσmem hσ
    obtain ⟨j', hj'⟩ := exists_sr_of_mem_geomInertia_inf hζ hc Q hτmem hτ
    have hmul : σ * τ⁻¹ ∈ geomInertia (dihInfCover n).M Q :=
      Subgroup.mul_mem _ hσmem (Subgroup.inv_mem _ hτmem)
    have hrot : σ * τ⁻¹ = dihInfDeckEquiv hζ (DihedralGroup.r (j' - j)) := by
      rw [hj, hj', ← map_inv, ← map_mul, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr]
    have hj0 : j' - j = 0 := eq_zero_of_mem_geomInertia_of_r_inf hζ hc Q (hrot ▸ hmul)
    rw [hj, hj', (sub_eq_zero.mp hj0).symm]
  -- hence "is the identity" separates its elements
  have hcard2 : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  refine le_trans (Nat.card_le_card_of_injective
    (fun σ : geomInertia (dihInfCover n).M Q =>
      decide ((σ : (dihInfCover n).deck) = 1)) ?_) (le_of_eq hcard2)
  rintro ⟨σ, hσm⟩ ⟨τ, hτm⟩ h
  simp only [decide_eq_decide] at h
  by_cases hσ1 : σ = 1
  · exact Subtype.ext (hσ1.trans (h.mp hσ1).symm)
  · exact Subtype.ext (key σ hσm τ hτm hσ1 fun hc' => hσ1 (h.mpr hc'))

end Rotations

/-! ### The two reflection points -/

section Branch

/-- The function `S - a·E`, whose square is the generator of the place over `S = a/2` up to a
factor invertible away from the origin. -/
def infWB (n : ℕ) [NeZero n] (a : k) : Bring (dihInfCover n).M :=
  infS n - algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C a) * infEB n

/-- A square root of `1` is nonzero. -/
theorem ne_zero_of_sq_eq_one {a : k} (ha : a ^ 2 = 1) : a ≠ 0 := by
  intro h
  rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at ha
  exact zero_ne_one ha

/-- The ring identity behind the degeneration: if `V + E = 1`, `V² - V + S² = 0`, `A² = 1` and
`2H = 1`, then `S - A·E` is a square root of `(S - A·H)·(-2A·E)`. -/
theorem sq_sub_mul_aux {R : Type*} [CommRing R] (S V E A H : R) (hVE : V + E = 1)
    (hq : V ^ 2 - V + S ^ 2 = 0) (hA2 : A ^ 2 = 1) (hH2 : 2 * H = 1) :
    (S - A * E) ^ 2 = (S - A * H) * (-(2 * A) * E) := by
  linear_combination (E ^ 2 - 2 * H * E) * hA2 + hq + (E - V) * hVE + (-E) * hH2

set_option synthInstance.maxHeartbeats 400000 in
/-- **The degeneration of the inverted dihedral equation at a reflection point.** -/
theorem infWB_sq (n : ℕ) [NeZero n] {a : k} (ha : a ^ 2 = 1) :
    (infWB n a) ^ 2
      = algebraMap (Polynomial k) (Bring (dihInfCover n).M) (X - C (a * 2⁻¹))
          * (algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C (-(2 * a))) * infEB n) := by
  have key : ∀ x y : k, algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C (x * y))
      = algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C x)
        * algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C y) := fun x y => by
    rw [map_mul, map_mul]
  have hTwo : algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C (2 : k))
      = (2 : Bring (dihInfCover n).M) := by
    rw [map_ofNat, map_ofNat]
  have hA2 : (algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C a)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ha, map_one, map_one]
  have hH2 : 2 * algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C (2⁻¹ : k)) = 1 := by
    rw [← hTwo, ← key, mul_inv_cancel₀ (two_ne_zero), map_one, map_one]
  have hAm : algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C (-(2 * a)))
      = -(2 * algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C a)) := by
    rw [map_neg, map_neg, key, hTwo]
  have hgen : algebraMap (Polynomial k) (Bring (dihInfCover n).M) (X - C (a * 2⁻¹))
      = infS n - algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C a)
          * algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C (2⁻¹ : k)) := by
    rw [map_sub, key, infS]
  rw [hgen, hAm, infWB]
  exact sq_sub_mul_aux (infS n) (infVB n) (infEB n)
    (algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C a))
    (algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C (2⁻¹ : k)))
    (infVB_add_infEB n) (infVB_quadratic n) hA2 hH2

/-- **The place over a reflection point of the inverted cover ramifies to order at least two.** -/
theorem dihInf_sq_dvd (n : ℕ) [NeZero n] {a : k} (ha : a ^ 2 = 1)
    (Q : Ideal (Bring (dihInfCover n).M)) [hQm : Q.IsMaximal]
    [Q.LiesOver (placeP (a * 2⁻¹))] :
    Q ^ 2 ∣ Ideal.map (algebraMap (Polynomial k) (Bring (dihInfCover n).M))
      (placeP (a * 2⁻¹)) := by
  have ha0 : a ≠ 0 := ne_zero_of_sq_eq_one ha
  have hane : a * 2⁻¹ ≠ 0 := mul_ne_zero ha0 (inv_ne_zero (two_ne_zero))
  refine dihInf_pow_dvd_gen n (a * 2⁻¹) Q (y := infWB n a) (infWB_sq n ha) ?_
  have hunit : IsUnit (algebraMap (Polynomial k) (Bring (dihInfCover n).M) (C (-(2 * a)))) :=
    (Polynomial.isUnit_C.mpr
      (neg_ne_zero.mpr (mul_ne_zero (two_ne_zero) ha0)).isUnit).map _
  rw [Ideal.unit_mul_mem_iff_mem Q hunit]
  exact infEB_notMem n hane Q

/-- **Inertia over a reflection point of the inverted cover has order exactly two.** -/
theorem card_geomInertia_inf_eq_two (n : ℕ) [NeZero n] {a : k} (ha : a ^ 2 = 1)
    (Q : Ideal (Bring (dihInfCover n).M)) [Q.IsMaximal] [Q.LiesOver (placeP (a * 2⁻¹))] :
    Nat.card (geomInertia (dihInfCover n).M Q) = 2 := by
  have hane : a * 2⁻¹ ≠ 0 :=
    mul_ne_zero (ne_zero_of_sq_eq_one ha) (inv_ne_zero (two_ne_zero))
  exact le_antisymm (card_geomInertia_le_two_inf n hane Q)
    (le_card_geomInertia_of_pow_dvd (a * 2⁻¹) Q (dihInf_sq_dvd n ha Q))

/-- **A reflection generates the inertia group at each of the two reflection points of the inverted
cover.** -/
theorem isInertiaGenAt_dihInfCover (n : ℕ) [NeZero n] {a : k} (ha : a ^ 2 = 1) :
    ∃ σ : (dihInfCover n).deck, σ ≠ 1 ∧ orderOf σ = 2
      ∧ (dihInfCover n).IsInertiaGenAt (a * 2⁻¹) σ := by
  obtain ⟨Q, hQmax, hQover⟩ := exists_Q_over_placeP (dihInfCover n).M (a * 2⁻¹)
  haveI := hQmax
  haveI := hQover
  have hcard := card_geomInertia_inf_eq_two n ha Q
  -- pick a nontrivial element of the inertia group
  have hne : ∃ σ ∈ geomInertia (dihInfCover n).M Q, σ ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : geomInertia (dihInfCover n).M Q = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hsub, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨σ, hσmem, hσ⟩ := hne
  have hord : orderOf σ = 2 := by
    have hdvd : orderOf σ ∣ 2 := by
      have h1 : orderOf (⟨σ, hσmem⟩ : geomInertia (dihInfCover n).M Q)
          ∣ Nat.card (geomInertia (dihInfCover n).M Q) := orderOf_dvd_natCard _
      rwa [hcard, Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσ
    · exact h
  refine ⟨σ, hσ, hord, Q, hQmax, hQover, ?_⟩
  refine (Subgroup.eq_of_le_of_card_le' (H := Subgroup.zpowers σ)
    (Subgroup.zpowers_le.mpr hσmem) ?_).symm
  rw [hcard, Nat.card_zpowers, hord]

end Branch

/-! ### The branch locus, exactly -/

/-- **The branch locus of the inverted dihedral cover is exactly the three points `0`, `1/2` and
`-1/2`.** -/
theorem branchLocus_dihInfCover (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    (dihInfCover n).branchLocus = ({0, 2⁻¹, -2⁻¹} : Set k) := by
  refine subset_antisymm (branchLocus_dihInfCover_subset n) ?_
  rintro t (rfl | rfl | rfl)
  · obtain ⟨σ, hord, hgen⟩ := isInertiaGenAt_zero_dihInfCover n hn
    have hσ : σ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord
      omega
    exact ⟨σ, hσ, hgen.isInertiaAt⟩
  · obtain ⟨σ, hσ, -, hgen⟩ := isInertiaGenAt_dihInfCover n (a := 1) (one_pow 2)
    exact ⟨σ, hσ, by simpa using hgen.isInertiaAt⟩
  · obtain ⟨σ, hσ, -, hgen⟩ := isInertiaGenAt_dihInfCover n (a := -1) neg_one_sq
    refine ⟨σ, hσ, ?_⟩
    have hrw : (-1 : k) * 2⁻¹ = -2⁻¹ := by ring
    rw [hrw] at hgen
    exact hgen.isInertiaAt

end Rigidity.RET

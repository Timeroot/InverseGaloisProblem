/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.DihedralBranch
import InverseGalois.Rigidity.RET.MultiKummerInertia
import InverseGalois.Rigidity.RET.InertiaGen

/-!
# Inertia in the dihedral cover of the line

The dihedral cover `T = u^n + u^{-n}` of the line is the first cover with a non-abelian deck group
whose local structure can be read off the equation directly.  Its parameter `u` satisfies
`u^{2n} - T·u^n + 1 = 0`, so `u` is a *unit* of the integral model: the constant term of the
equation is `1`.  That single fact drives everything here.

Because `u` is a unit, the rotations — which scale `u` by a root of unity — can never lie in a
geometric inertia group, since an inertia element fixes a unit modulo the place and a root of unity
congruent to `1` at a place of a `k`-algebra is `1`.  So every inertia group of the cover consists
of the identity and reflections, and two reflections in one inertia group differ by a rotation in
it, hence coincide: inertia is of order at most two everywhere.

At `T = ±2` the equation degenerates: `T - 2a = u^{-n}(u^n - a)^2` whenever `a^2 = 1`, so the place
`X - 2a` becomes a square in the cover and inertia has order at least two there.  The two bounds
meet, and the branch locus of the dihedral cover is exactly `{2, -2}`, with a reflection generating
the inertia group at each of the two points.

## Main definitions

* `Rigidity.RET.dihU` — the parameter of the dihedral cover, inside its integral model.

## Main results

* `Rigidity.RET.isUnit_dihU` — the parameter is a unit of the integral model.
* `Rigidity.RET.card_geomInertia_le_two` — every inertia group of the dihedral cover has order at
  most two, and `Rigidity.RET.eq_one_of_mem_geomInertia_of_r` says no nontrivial rotation is an
  inertia element.
* `Rigidity.RET.card_geomInertia_eq_two` — at a place over `T = ±2` the inertia group has order
  exactly two, and `Rigidity.RET.isInertiaGenAt_dihLineCover` produces a distinguished generator.
* `Rigidity.RET.branchLocus_dihLineCover` — the branch locus is exactly `{2, -2}`.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

/-! ### The parameter as a unit of the integral model -/

section Unit

variable {n : ℕ} [NeZero n]

/-- The parameter of the dihedral cover is integral over the coordinate ring of the base. -/
theorem dihParam_isIntegral (n : ℕ) [NeZero n] : IsIntegral (Polynomial k) (dihParam n) :=
  ⟨dihedralPoly (Polynomial.X : Polynomial k) n, dihedralPoly_monic _ (dihPos n), by
    rw [← Polynomial.aeval_def]; exact aeval_param_dihedralPolyX n⟩

/-- **The parameter of the dihedral cover**, as an element of its integral model. -/
def dihU (n : ℕ) [NeZero n] : Bring (DihCover n) := ⟨dihParam n, dihParam_isIntegral n⟩

@[simp] theorem coe_dihU : ((dihU n : Bring (DihCover n)) : DihCover n) = dihParam n := rfl

/-- The coordinate of the base, inside the integral model of the dihedral cover. -/
def dihT (n : ℕ) [NeZero n] : Bring (DihCover n) :=
  algebraMap (Polynomial k) (Bring (DihCover n)) Polynomial.X

@[simp] theorem coe_dihT :
    ((dihT n : Bring (DihCover n)) : DihCover n)
      = algebraMap (Polynomial k) (DihCover n) Polynomial.X := rfl

/-- The dihedral equation, on the covering line. -/
theorem dihParam_pow_sq (n : ℕ) [NeZero n] :
    ((dihParam n) ^ n) ^ 2
      = algebraMap (Polynomial k) (DihCover n) Polynomial.X * (dihParam n) ^ n - 1 := by
  have h := aeval_param_dihedralPolyX n
  simp only [dihedralPoly, map_add, map_neg, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, map_one] at h
  rw [← pow_mul, mul_comm n 2]
  linear_combination h

/-- **The dihedral equation** in the integral model: the constant term is `1`. -/
theorem dihU_pow_sq (n : ℕ) [NeZero n] :
    ((dihU n) ^ n) ^ 2 = dihT n * (dihU n) ^ n - 1 := by
  apply Subtype.ext
  push_cast [coe_dihT, coe_dihU]
  exact dihParam_pow_sq n

/-- **The parameter is a unit of the integral model**, because the dihedral equation has constant
term `1`. -/
theorem isUnit_dihU (n : ℕ) [NeZero n] : IsUnit (dihU n) := by
  have hpos := dihPos n
  have h1 : dihU n * (dihU n) ^ (n - 1) = (dihU n) ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  refine IsUnit.of_mul_eq_one
    (dihT n * (dihU n) ^ (n - 1) - (dihU n) ^ n * (dihU n) ^ (n - 1)) ?_
  calc dihU n * (dihT n * (dihU n) ^ (n - 1) - (dihU n) ^ n * (dihU n) ^ (n - 1))
      = dihT n * (dihU n * (dihU n) ^ (n - 1))
        - (dihU n) ^ n * (dihU n * (dihU n) ^ (n - 1)) := by ring
    _ = dihT n * (dihU n) ^ n - ((dihU n) ^ n) ^ 2 := by rw [h1]; ring
    _ = 1 := by rw [dihU_pow_sq]; ring

/-- A power of the parameter is a unit. -/
theorem isUnit_dihU_pow (n : ℕ) [NeZero n] (m : ℕ) : IsUnit ((dihU n) ^ m) :=
  (isUnit_dihU n).pow m

/-- The parameter is invertible at every place, so it lies in none of them. -/
theorem dihU_notMem (Q : Ideal (Bring (DihCover n))) [hQ : Q.IsMaximal] : dihU n ∉ Q :=
  fun hmem => hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (isUnit_dihU n))

end Unit

/-! ### No rotation is an inertia element -/

section Rotations

variable {n : ℕ} [NeZero n] {ζ : k}

set_option synthInstance.maxHeartbeats 400000 in
/-- A rotation of the dihedral cover scales the parameter by a root of unity. -/
theorem smul_dihU_r (hζ : IsPrimitiveRoot ζ n) (i : ZMod n) :
    (dihCoverAutHom hζ (DihedralGroup.r i)) • dihU n
      = algebraMap (Polynomial k) (Bring (DihCover n)) (C (rootPow ζ i)) * dihU n := by
  apply Subtype.ext
  rw [coe_smul_geom, Submonoid.coe_mul, Subalgebra.coe_algebraMap, coe_dihU]
  apply LineSubst.toLine_injective
  rw [dihCoverAutHom_apply hζ, LineSubst.toLine_mul, LineSubst.toLine_param,
    LineSubst.toLine_algebraMap_poly, dihedralAut_r, scaleAut_X, Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply, AlgHom.commutes]

/-- **No nontrivial rotation of the dihedral cover is an inertia element.**  A rotation scales the
parameter, which is a unit of the integral model, by a root of unity; an inertia element fixes a
unit modulo its place, so the root of unity is `1`. -/
theorem eq_one_of_mem_geomInertia_of_r (hζ : IsPrimitiveRoot ζ n)
    (Q : Ideal (Bring (DihCover n))) [Q.IsMaximal] {i : ZMod n}
    (hmem : (dihCoverAutHom hζ (DihedralGroup.r i)) ∈ geomInertia (DihCover n) Q) :
    i = 0 := by
  have hone : rootPow ζ i = 1 :=
    const_eq_one_of_mem_inertia (Ω := DihCover n) Q hmem (dihU_notMem Q) (smul_dihU_r hζ i)
  exact (rootPow_eq_one_iff hζ i).mp hone

/-- An inertia element of the dihedral cover that is not the identity is a reflection. -/
theorem exists_sr_of_mem_geomInertia (hζ : IsPrimitiveRoot ζ n)
    (Q : Ideal (Bring (DihCover n))) [Q.IsMaximal]
    {σ : DihCover n ≃ₐ[RatFunc k] DihCover n} (hmem : σ ∈ geomInertia (DihCover n) Q)
    (hσ : σ ≠ 1) : ∃ j : ZMod n, σ = dihCoverAutHom hζ (DihedralGroup.sr j) := by
  obtain ⟨g, hg⟩ := (dihCoverAutHom_bijective hζ).surjective σ
  cases g with
  | r i =>
    refine absurd ?_ hσ
    have hi : i = 0 := eq_one_of_mem_geomInertia_of_r hζ Q (hg ▸ hmem)
    rw [← hg, hi]
    exact (dihCoverAutHom hζ).map_one
  | sr j => exact ⟨j, hg.symm⟩

/-- **Inertia in the dihedral cover has order at most two.**  Two reflections in one inertia group
differ by a rotation lying in that group, and no nontrivial rotation does. -/
theorem card_geomInertia_le_two (n : ℕ) [NeZero n] (Q : Ideal (Bring (DihCover n)))
    [Q.IsMaximal] : Nat.card (geomInertia (DihCover n) Q) ≤ 2 := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_algebraicClosure n (dihPos n)
  -- an inertia group has at most one nontrivial element
  have key : ∀ σ ∈ geomInertia (DihCover n) Q, ∀ τ ∈ geomInertia (DihCover n) Q,
      σ ≠ 1 → τ ≠ 1 → σ = τ := by
    intro σ hσmem τ hτmem hσ hτ
    obtain ⟨j, hj⟩ := exists_sr_of_mem_geomInertia hζ Q hσmem hσ
    obtain ⟨j', hj'⟩ := exists_sr_of_mem_geomInertia hζ Q hτmem hτ
    have hmul : σ * τ⁻¹ ∈ geomInertia (DihCover n) Q :=
      Subgroup.mul_mem _ hσmem (Subgroup.inv_mem _ hτmem)
    have hrot : σ * τ⁻¹ = dihCoverAutHom hζ (DihedralGroup.r (j' - j)) := by
      rw [hj, hj', ← map_inv, ← map_mul, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr]
    have hj0 : j' - j = 0 := eq_one_of_mem_geomInertia_of_r hζ Q (hrot ▸ hmul)
    rw [hj, hj', (sub_eq_zero.mp hj0).symm]
  -- hence "is the identity" separates its elements
  have hcard2 : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  refine le_trans (Nat.card_le_card_of_injective
    (fun σ : geomInertia (DihCover n) Q =>
      decide ((σ : DihCover n ≃ₐ[RatFunc k] DihCover n) = 1)) ?_) (le_of_eq hcard2)
  rintro ⟨σ, hσm⟩ ⟨τ, hτm⟩ h
  simp only [decide_eq_decide] at h
  by_cases hσ1 : σ = 1
  · exact Subtype.ext (hσ1.trans (h.mp hσ1).symm)
  · exact Subtype.ext (key σ hσm τ hτm hσ1 fun hc => hσ1 (h.mpr hc))

end Rotations

/-! ### The two branch points -/

section Branch

variable {n : ℕ} [NeZero n]

/-- **The place `X - 2a` becomes a square in the dihedral cover**, for `a` a square root of `1`:
this is the degeneration `T - 2a = u^{-n}(u^n - a)^2` of the dihedral equation. -/
theorem dihedral_degenerate (n : ℕ) [NeZero n] {a : k} (ha : a ^ 2 = 1) :
    algebraMap (Polynomial k) (Bring (DihCover n)) (Polynomial.X - C (2 * a)) * (dihU n) ^ n
      = ((dihU n) ^ n - algebraMap (Polynomial k) (Bring (DihCover n)) (C a)) ^ 2 := by
  have hA2 : (algebraMap (Polynomial k) (Bring (DihCover n)) (C a)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ha, map_one, map_one]
  have hC : (C (2 * a) : Polynomial k) = 2 * C a := by rw [C_mul, map_ofNat]
  have hmap : algebraMap (Polynomial k) (Bring (DihCover n)) (Polynomial.X - C (2 * a))
      = dihT n - 2 * algebraMap (Polynomial k) (Bring (DihCover n)) (C a) := by
    rw [map_sub, hC, map_mul, map_ofNat, dihT]
  rw [hmap]
  linear_combination -(dihU_pow_sq n) - hA2

/-- The square of a place over `T = ±2` divides the extension of that place to the dihedral
cover. -/
theorem dihedral_sq_dvd (n : ℕ) [NeZero n] {a : k} (ha : a ^ 2 = 1)
    (Q : Ideal (Bring (DihCover n))) [hQ : Q.IsMaximal] [Q.LiesOver (placeP (2 * a))] :
    Q ^ 2 ∣ Ideal.map (algebraMap (Polynomial k) (Bring (DihCover n))) (placeP (2 * a)) := by
  haveI := hQ.isPrime
  -- the image of the place is in `Q`
  have hover : placeP (2 * a) = Q.comap (algebraMap (Polynomial k) (Bring (DihCover n))) :=
    Ideal.LiesOver.over
  have hXmem : algebraMap (Polynomial k) (Bring (DihCover n)) (Polynomial.X - C (2 * a)) ∈ Q := by
    have hmem : (Polynomial.X - C (2 * a)) ∈ placeP (2 * a) := Ideal.mem_span_singleton_self _
    rw [hover, Ideal.mem_comap] at hmem
    exact hmem
  -- hence the square of `u^n - a` is in `Q`, so `u^n - a` is
  have hy2 : ((dihU n) ^ n - algebraMap (Polynomial k) (Bring (DihCover n)) (C a)) ^ 2 ∈ Q := by
    rw [← dihedral_degenerate n ha]
    exact Ideal.mul_mem_right _ _ hXmem
  have hyQ : (dihU n) ^ n - algebraMap (Polynomial k) (Bring (DihCover n)) (C a) ∈ Q := by
    rcases Ideal.IsPrime.mem_or_mem ‹Q.IsPrime› (by rw [← sq]; exact hy2) with h | h <;> exact h
  -- and the image of the place differs from that square by a unit
  obtain ⟨v, hv⟩ := (isUnit_dihU_pow n n).exists_right_inv
  have hmem : algebraMap (Polynomial k) (Bring (DihCover n)) (Polynomial.X - C (2 * a)) ∈ Q ^ 2 := by
    have hrw : algebraMap (Polynomial k) (Bring (DihCover n)) (Polynomial.X - C (2 * a))
        = (algebraMap (Polynomial k) (Bring (DihCover n)) (Polynomial.X - C (2 * a))
            * (dihU n) ^ n) * v := by
      rw [mul_assoc, hv, mul_one]
    rw [hrw, dihedral_degenerate n ha]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hyQ 2)
  rw [Ideal.dvd_iff_le, placeP, Ideal.map_span, Ideal.span_le, Set.image_singleton,
    Set.singleton_subset_iff]
  exact hmem

/-- **Inertia over `T = ±2` in the dihedral cover has order exactly two.** -/
theorem card_geomInertia_eq_two (n : ℕ) [NeZero n] {a : k} (ha : a ^ 2 = 1)
    (Q : Ideal (Bring (DihCover n))) [Q.IsMaximal] [Q.LiesOver (placeP (2 * a))] :
    Nat.card (geomInertia (DihCover n) Q) = 2 :=
  le_antisymm (card_geomInertia_le_two n Q)
    (le_card_geomInertia_of_pow_dvd (2 * a) Q (dihedral_sq_dvd n ha Q))

/-- **A reflection generates the inertia group at each of the two branch points.** -/
theorem isInertiaGenAt_dihLineCover (n : ℕ) [NeZero n] {a : k} (ha : a ^ 2 = 1) :
    ∃ σ : (dihLineCover n).deck, σ ≠ 1 ∧ (dihLineCover n).IsInertiaGenAt (2 * a) σ := by
  obtain ⟨Q, hQmax, hQover⟩ := exists_Q_over_placeP (Ω := DihCover n) (2 * a)
  haveI := hQmax
  haveI := hQover
  have hcard := card_geomInertia_eq_two n ha Q
  -- pick a nontrivial element of the inertia group
  have hne : ∃ σ ∈ geomInertia (DihCover n) Q, σ ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : geomInertia (DihCover n) Q = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hsub, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨σ, hσmem, hσ⟩ := hne
  have hord : orderOf σ = 2 := by
    have hdvd : orderOf σ ∣ 2 := by
      have h1 : orderOf (⟨σ, hσmem⟩ : geomInertia (DihCover n) Q)
          ∣ Nat.card (geomInertia (DihCover n) Q) := orderOf_dvd_natCard _
      rwa [hcard, Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσ
    · exact h
  refine ⟨σ, hσ, Q, hQmax, hQover, ?_⟩
  refine (Subgroup.eq_of_le_of_card_le' (H := Subgroup.zpowers σ) ?_ ?_).symm
  · exact Subgroup.zpowers_le.mpr hσmem
  · exact le_of_eq (by rw [hcard, Nat.card_zpowers, hord])

end Branch

/-! ### The branch locus, exactly -/

section Locus

variable {n : ℕ} [NeZero n]

/-- **The branch locus of the dihedral cover is exactly the two points `T = ±2`.** -/
theorem branchLocus_dihLineCover (n : ℕ) [NeZero n] :
    (dihLineCover n).branchLocus = ({2, -2} : Set k) := by
  refine subset_antisymm (branchLocus_dihLineCover_subset n) ?_
  rintro t (rfl | rfl)
  · obtain ⟨σ, hσ, hgen⟩ := isInertiaGenAt_dihLineCover n (a := 1) (one_pow 2)
    exact ⟨σ, hσ, by simpa using hgen.isInertiaAt⟩
  · obtain ⟨σ, hσ, hgen⟩ := isInertiaGenAt_dihLineCover n (a := -1) (neg_one_sq)
    exact ⟨σ, hσ, by simpa using hgen.isInertiaAt⟩

/-- **The dihedral cover has exactly two affine branch points.** -/
theorem ncard_branchLocus_dihLineCover (n : ℕ) [NeZero n] :
    (dihLineCover n).branchLocus.ncard = 2 := by
  rw [branchLocus_dihLineCover n]
  rw [Set.ncard_pair]
  intro h
  have : (4 : k) = 0 := by linear_combination h
  norm_num at this

end Locus

end Rigidity.RET

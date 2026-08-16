/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Separating

/-!
# From functions that see the deck group to one function that separates a fibre

The Galois correspondence for a covering runs on the weakest form of the analytic input: for each
nontrivial deck transformation, one function of moderate growth that it moves somewhere.  The
stronger form — one function of moderate growth taking distinct values at all the points of one
fibre — looks like more, but on a connected covering it is not.

Two elementary steps bridge them.  A function moved by a deck transformation `c` differs from its
`c`-translate, so the difference is a nonzero element of the ring of functions of the covering; on
a connected covering that ring is a domain, so a finite product of such differences and their
translates is again nonzero, and one point of the total space avoids the zeros of all of them at
once.  There, every chosen function separates its own deck transformation on the whole fibre.  A
generic linear combination of the chosen functions then separates them all simultaneously: the
coefficients that fail are the roots of a nonzero polynomial, and the plane has more points than
that.

## Main results

* `Rigidity.RET.exists_forall_smul_ne` — one point of the covering at which each chosen function
  is moved by its own deck transformation, everywhere along the fibre.
* `Rigidity.RET.hasSeparatingFunction_of_forall_ne` — a connected covering whose functions of
  moderate growth see its deck group carries a single function of moderate growth separating the
  points of a fibre.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

section Combine

universe u

variable {Y : Type u} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
variable {S : Finset ℂ}
variable {H : Type*} [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]

omit [Nonempty Y] [PreconnectedSpace Y] in
/-- **The constants are functions of moderate growth on the covering.** -/
theorem const_mem_coverRing (hf : IsLocalHomeomorph f) (S : Finset ℂ) (v : ℂ) :
    (fun _ : Y => v) ∈ coverRing hf S :=
  ⟨fun y => isHoloAt_const hf v y, isModerate_const f S v⟩

/-- **One point of the covering sees every deck transformation at once.**

Choosing, for each nontrivial deck transformation, a function of moderate growth that it moves,
there is a single point of the total space at which every one of the chosen functions is moved by
its own deck transformation — and at every point of the fibre through it. -/
theorem exists_forall_smul_ne (hf : IsLocalHomeomorph f) [IsOverBase H f]
    (hne : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    ∃ (Fc : H → ↥(coverRing hf S)) (y₀ : Y), ∀ c b : H, c ≠ 1 →
      (Fc c : Y → ℂ) (b • y₀) ≠ (Fc c : Y → ℂ) ((c * b) • y₀) := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have key : ∀ c : H, ∃ F : ↥(coverRing hf S), c ≠ 1 →
      ∃ y : Y, (F : Y → ℂ) (c • y) ≠ (F : Y → ℂ) y := by
    intro c
    by_cases hc : c = 1
    · exact ⟨0, fun h => absurd hc h⟩
    · obtain ⟨F, hF, y, hy⟩ := hne c hc
      exact ⟨⟨F, hF⟩, fun _ => ⟨y, hy⟩⟩
  choose Fc hFc using key
  -- the difference between a chosen function and its translate, evaluated
  have hGval : ∀ (c : H) (y : Y),
      ((Fc c - c⁻¹ • Fc c : ↥(coverRing hf S)) : Y → ℂ) y
        = (Fc c : Y → ℂ) y - (Fc c : Y → ℂ) (c • y) := by
    intro c y
    show ((Fc c : Y → ℂ) - ((c⁻¹ • Fc c : ↥(coverRing hf S)) : Y → ℂ)) y = _
    rw [Pi.sub_apply, coverRing_smul_coe, inv_inv]
  -- each such difference, and each of its translates, is a nonzero element of the ring
  have hGne : ∀ c : H, c ≠ 1 → (Fc c - c⁻¹ • Fc c : ↥(coverRing hf S)) ≠ 0 := by
    intro c hc h0
    obtain ⟨y, hy⟩ := hFc c hc
    have h1 : ((Fc c - c⁻¹ • Fc c : ↥(coverRing hf S)) : Y → ℂ) y = 0 := by
      rw [h0]; rfl
    rw [hGval] at h1
    exact hy (sub_eq_zero.1 h1).symm
  have hTne : ∀ c b : H, c ≠ 1 →
      (b⁻¹ • (Fc c - c⁻¹ • Fc c) : ↥(coverRing hf S)) ≠ 0 := by
    intro c b hc
    rw [Ne, smul_eq_zero_iff_eq]
    exact hGne c hc
  -- a point avoiding the zeros of the whole finite family
  set T : Finset (H × H) := Finset.univ.filter (fun p : H × H => p.1 ≠ 1) with hT
  set P : ↥(coverRing hf S) :=
    ∏ p ∈ T, (p.2⁻¹ • (Fc p.1 - p.1⁻¹ • Fc p.1)) with hP
  have hPne : P ≠ 0 := by
    rw [hP]
    refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
    exact hTne p.1 p.2 (by simpa [hT] using hp)
  have hPfun : (P : Y → ℂ) ≠ 0 := fun h => hPne (Subtype.ext h)
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 hPfun
  rw [Pi.zero_apply] at hy₀
  refine ⟨Fc, y₀, fun c b hc h => ?_⟩
  -- at that point every factor of the product is nonzero
  have hcoe : (P : Y → ℂ) y₀
      = ∏ p ∈ T, ((p.2⁻¹ • (Fc p.1 - p.1⁻¹ • Fc p.1) : ↥(coverRing hf S)) : Y → ℂ) y₀ := by
    have hprod : ((P : ↥(coverRing hf S)) : Y → ℂ)
        = ∏ p ∈ T, ((p.2⁻¹ • (Fc p.1 - p.1⁻¹ • Fc p.1) : ↥(coverRing hf S)) : Y → ℂ) := by
      rw [hP]; exact SubmonoidClass.coe_finset_prod _ _
    rw [hprod, Finset.prod_apply]
  rw [hcoe] at hy₀
  have hmem : (c, b) ∈ T := by simp [hT, hc]
  have hfac := Finset.prod_ne_zero_iff.1 hy₀ (c, b) hmem
  rw [coverRing_smul_coe, inv_inv, hGval, ← mul_smul] at hfac
  exact hfac (sub_eq_zero.2 h)

/-- **A connected covering whose functions of moderate growth see its deck group carries a
separating function.**

A generic linear combination of the functions chosen for the individual deck transformations takes
distinct values at all the points of one fibre: the coefficients for which it fails are roots of a
nonzero polynomial. -/
theorem hasSeparatingFunction_of_forall_ne (hf : IsLocalHomeomorph f) [IsOverBase H f]
    (hne : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    HasSeparatingFunction hf S H := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨Fc, y₀, hy₀⟩ := exists_forall_smul_ne hf hne
  -- an enumeration of the group by exponents
  set e : H ≃ Fin (Fintype.card H) := Fintype.equivFin H with he
  set deg : H → ℕ := fun c => (e c : ℕ) with hdeg
  have hdeginj : Function.Injective deg := by
    intro c c' h
    exact e.injective (Fin.ext h)
  -- the values to be separated, and the polynomial recording them
  set v : H → H → H → ℂ :=
    fun a b c => (Fc c : Y → ℂ) (a • y₀) - (Fc c : Y → ℂ) (b • y₀) with hv
  set p : H → H → ℂ[X] := fun a b => ∑ c : H, C (v a b c) * X ^ deg c with hp
  have hcoeff : ∀ a b c₀ : H, (p a b).coeff (deg c₀) = v a b c₀ := by
    intro a b c₀
    rw [hp]
    rw [finset_sum_coeff]
    rw [Finset.sum_eq_single c₀]
    · simp [coeff_C_mul, coeff_X_pow]
    · intro c _ hcc
      have : deg c₀ ≠ deg c := fun h => hcc (hdeginj h.symm)
      simp [coeff_C_mul, coeff_X_pow, this]
    · intro h
      exact absurd (Finset.mem_univ c₀) h
  have hpne : ∀ a b : H, a ≠ b → p a b ≠ 0 := by
    intro a b hab hzero
    have hc : a * b⁻¹ ≠ 1 := fun h => hab (by
      have := mul_inv_eq_one.1 h
      exact this)
    have hmove := hy₀ (a * b⁻¹) b hc
    rw [inv_mul_cancel_right] at hmove
    have hvne : v a b (a * b⁻¹) ≠ 0 := by
      rw [hv]
      exact fun h => hmove (sub_eq_zero.1 h).symm
    apply hvne
    rw [← hcoeff a b (a * b⁻¹), hzero, coeff_zero]
  -- a coefficient avoiding every failure
  set Q : ℂ[X] := ∏ q ∈ Finset.univ.filter (fun q : H × H => q.1 ≠ q.2), p q.1 q.2 with hQ
  have hQne : Q ≠ 0 := by
    rw [hQ]
    refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    exact hpne q.1 q.2 (by simpa using hq)
  obtain ⟨t, ht⟩ := ((Polynomial.finite_setOf_isRoot hQne).infinite_compl).nonempty
  have hteval : ∀ a b : H, a ≠ b → (p a b).eval t ≠ 0 := by
    intro a b hab hzero
    apply ht
    show Q.IsRoot t
    rw [IsRoot, hQ, eval_prod]
    refine Finset.prod_eq_zero (i := (a, b)) (by simp [hab]) hzero
  -- the linear combination
  set Fsum : ↥(coverRing hf S) :=
    ∑ c : H, (⟨fun _ => t ^ deg c, const_mem_coverRing hf S _⟩ * Fc c) with hFsum
  have hval : ∀ y : Y, (Fsum : Y → ℂ) y = ∑ c : H, t ^ deg c * (Fc c : Y → ℂ) y := by
    intro y
    have hsum : ((Fsum : ↥(coverRing hf S)) : Y → ℂ)
        = ∑ c : H, ((⟨fun _ => t ^ deg c, const_mem_coverRing hf S _⟩ *
          Fc c : ↥(coverRing hf S)) : Y → ℂ) := by
      rw [hFsum]; exact AddSubmonoidClass.coe_finset_sum _ _
    rw [hsum, Finset.sum_apply]
    rfl
  refine ⟨(Fsum : Y → ℂ), Fsum.2, y₀, fun a b hab => ?_⟩
  by_contra hne'
  refine hteval a b hne' ?_
  rw [hp, eval_finset_sum]
  rw [hval, hval] at hab
  have hdiff : ∑ c : H, t ^ deg c * (Fc c : Y → ℂ) (a • y₀)
      - ∑ c : H, t ^ deg c * (Fc c : Y → ℂ) (b • y₀) = 0 := sub_eq_zero.2 hab
  rw [← Finset.sum_sub_distrib] at hdiff
  calc ∑ c : H, (C (v a b c) * X ^ deg c).eval t
      = ∑ c : H, (t ^ deg c * (Fc c : Y → ℂ) (a • y₀)
          - t ^ deg c * (Fc c : Y → ℂ) (b • y₀)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [eval_mul, eval_C, eval_pow, eval_X, hv]
        ring
    _ = 0 := hdiff

end Combine

end Rigidity.RET

end

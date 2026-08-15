/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Analytic.GermKummer

/-!
# The place cut out by a Kummer germ, and its ramification index

A ring `B` integral over `ℂ[X]`, together with a ring map to the meromorphic germs at the origin
extending the Kummer substitution `X ↦ s + u ^ d`, carries a distinguished place: the elements
whose germ vanishes at the origin.  Integrality is what makes the construction work — no element of
`B` acquires a pole, so the map lands in the valuation ring of germs, and the vanishing germs pull
back to a prime ideal lying over the point `s` of the line.

The point of the construction is the bound it gives on the ramification index.  The uniformizer
`X - s` pulls back to `u ^ d`, which vanishes to order exactly `d`, while an element of the
`(d+1)`-st power of the place would have to vanish to order at least `d + 1`.  So the place is
ramified to order at most `d`: an upper bound on ramification obtained from a single analytic
branch, with no comparison of the analytic and algebraic normalizations.

## Main definitions

* `Rigidity.RET.Analytic.germInt` — the Kummer substitution, corestricted to the valuation ring.
* `Rigidity.RET.Analytic.germPlace` — the place cut out by the germ.

## Main results

* `Rigidity.RET.Analytic.comap_germPlace` — the place lies over the point `s`.
* `Rigidity.RET.Analytic.ramificationIdx_germPlace_le` — its ramification index is at most the
  Kummer exponent.
-/

open Filter Topology Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

open MeroGerm

theorem ord_kummerHom_nonneg (s : ℂ) (d : ℕ) (p : Polynomial ℂ) :
    0 ≤ ord (kummerHom s d p) := by
  rw [kummerHom_apply]
  exact ord_nonneg_of_analyticAt (analyticAt_kummerComp s d p)

section

variable {B : Type*} [CommRing B] [Algebra (Polynomial ℂ) B] {s : ℂ} {d : ℕ}
  {Ψ : B →+* MeroGerm (0 : ℂ)}

/-- A germ in the image of a ring integral over the polynomial ring has no pole. -/
theorem ord_nonneg_of_kummer (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) (b : B) : 0 ≤ ord (Ψ b) := by
  obtain ⟨q, hq, hqb⟩ := hint b
  refine ord_nonneg_of_eval₂_eq_zero (kummerHom s d) (ord_kummerHom_nonneg s d) hq ?_
  have hcomp : Ψ.comp (algebraMap (Polynomial ℂ) B) = kummerHom s d := RingHom.ext hΨ
  have h := congrArg Ψ hqb
  rw [Polynomial.hom_eval₂, map_zero, hcomp] at h
  exact h

/-- The Kummer substitution, restricted to a ring integral over the polynomial ring, lands in the
valuation ring of germs without poles. -/
def germInt (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) : B →+* meroInt (0 : ℂ) :=
  Ψ.codRestrict _ fun b => mem_meroInt.2 (ord_nonneg_of_kummer hΨ hint b)

@[simp] theorem germInt_apply (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) (b : B) :
    ((germInt hΨ hint b : meroInt (0 : ℂ)) : MeroGerm (0 : ℂ)) = Ψ b := rfl

/-- **The place cut out by a Kummer germ**: the elements of the integral model whose germ vanishes
at the origin of the Kummer coordinate. -/
def germPlace (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) : Ideal B :=
  Ideal.comap (germInt hΨ hint) (meroMax (0 : ℂ))

theorem mem_germPlace {hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p}
    {hint : ∀ b : B, IsIntegral (Polynomial ℂ) b} {b : B} :
    b ∈ germPlace hΨ hint ↔ 0 < ord (Ψ b) := Iff.rfl

instance germPlace_isPrime (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) : (germPlace hΨ hint).IsPrime :=
  Ideal.IsPrime.comap _

theorem one_notMem_germPlace (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) : (1 : B) ∉ germPlace hΨ hint := by
  rw [mem_germPlace]
  simp

theorem X_sub_C_mem_germPlace (hd : d ≠ 0)
    (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) :
    algebraMap (Polynomial ℂ) B (X - C s) ∈ germPlace hΨ hint := by
  rw [mem_germPlace, hΨ, ord_kummerHom_X_sub_C]
  exact_mod_cast Int.natCast_pos.2 (Nat.pos_of_ne_zero hd)

/-- The place cut out by the germ lies over the point `s` of the line. -/
theorem comap_germPlace (hd : d ≠ 0)
    (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) :
    Ideal.comap (algebraMap (Polynomial ℂ) B) (germPlace hΨ hint)
      = Ideal.span {(X - C s : Polynomial ℂ)} := by
  have hmax : (Ideal.span {(X - C s : Polynomial ℂ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C _)
  refine (hmax.eq_of_le ?_ ?_).symm
  · intro h
    exact one_notMem_germPlace hΨ hint (by simpa using (Ideal.eq_top_iff_one _).1 h)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact X_sub_C_mem_germPlace hd hΨ hint

theorem le_ord_of_mem_germPlace_pow {hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p}
    {hint : ∀ b : B, IsIntegral (Polynomial ℂ) b} {n : ℕ} {b : B}
    (hb : b ∈ germPlace hΨ hint ^ n) : (n : WithTop ℤ) ≤ ord (Ψ b) := by
  have hmap : Ideal.map (germInt hΨ hint) (germPlace hΨ hint ^ n) ≤ meroMax (0 : ℂ) ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' Ideal.map_comap_le n
  exact le_ord_of_mem_pow (hmap (Ideal.mem_map_of_mem _ hb))

/-- **The ramification index of the germ place is at most the Kummer exponent.**

The uniformizer `X - s` pulls back to the germ `u ^ d`, which vanishes to order exactly `d`; an
element of the `(d+1)`-st power of the place vanishes to order at least `d + 1`. -/
theorem ramificationIdx_germPlace_le
    (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) :
    Ideal.ramificationIdx (algebraMap (Polynomial ℂ) B) (Ideal.span {(X - C s : Polynomial ℂ)})
      (germPlace hΨ hint) ≤ d := by
  refine Nat.lt_succ_iff.1 (Ideal.ramificationIdx_lt ?_)
  intro hle
  have hmem : algebraMap (Polynomial ℂ) B (X - C s) ∈ germPlace hΨ hint ^ (d + 1) :=
    hle (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))
  have hord := le_ord_of_mem_germPlace_pow hmem
  rw [hΨ, ord_kummerHom_X_sub_C] at hord
  have : ((d : ℤ) : WithTop ℤ) < ((d + 1 : ℕ) : WithTop ℤ) := by
    exact_mod_cast Int.lt_succ (d : ℤ)
  exact absurd hord (not_le.2 this)

end

end Rigidity.RET.Analytic

end

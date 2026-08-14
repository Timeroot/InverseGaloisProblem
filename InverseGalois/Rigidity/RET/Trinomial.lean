/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.EquationCover

/-!
# The trinomial family and its cover

A cover of the line branched at a point where *every* sheet comes together is the local picture of a
cyclic branch cycle of maximal length; the family that produces it is a trinomial

`Y ^ (m + 1) - c X ^ m Y - X ^ m`

read over the line with coordinate `X`.  Away from `X = 0` the fibre is `m + 1` distinct points,
while at `X = 0` the equation degenerates to `Y ^ (m + 1) = 0`.

Separability of the generic fibre is what makes the family define a cover at all, and for a
trinomial it is elementary: the combination `(m+1) f - Y f'` is linear in `Y`, so the unique root of
that linear polynomial converts the division algorithm into an explicit Bézout identity between `f`
and `f'`, whose only obstruction is the value of `f'` at that root.  For this family the root is a
constant while `f'` has a genuinely non-constant term, so the obstruction never occurs.

## Main definitions

* `Rigidity.RET.ramTrinomial` — the family `Y ^ (m + 1) - c X ^ m Y - X ^ m`.
* `Rigidity.RET.ramTrinomialCover` — the cover of the line it defines.

## Main results

* `Rigidity.RET.separable_trinomial` — a Bézout criterion for separability of `Y ^ (m+1) - bY - a`.
* `Rigidity.RET.genericPoly_ramTrinomial_separable` — the generic fibre of the family is separable.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-! ### Separability of a trinomial -/

section Field

variable {K : Type*} [Field K]

/-- **A Bézout criterion for the separability of a trinomial.**  The combination
`(m+1) f - Y f'` is linear in `Y`, vanishing at a single point `β`; dividing `f'` by `Y - β` then
expresses the constant `f'(β)` as a combination of `f` and `f'`, so the two are coprime as soon as
that constant is nonzero. -/
theorem separable_trinomial {m : ℕ} {a b β : K} (hm : (m : K) ≠ 0) (hb : b ≠ 0)
    (hβdef : (m : K) * b * β = -(((m + 1 : ℕ) : K) * a))
    (hβ : ((m + 1 : ℕ) : K) * β ^ m ≠ b) :
    (X ^ (m + 1) - C b * X - C a : Polynomial K).Separable := by
  set n : K := ((m + 1 : ℕ) : K) with hn
  set f : Polynomial K := X ^ (m + 1) - C b * X - C a with hf
  have hderiv : derivative f = C n * X ^ m - C b := by simp [hf, hn]
  set u : K := -((m : K) * b) with hu
  have hu0 : u ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hm hb)
  have hub : u * β = n * a := by rw [hu]; linear_combination -hβdef
  have hu' : (C u : Polynomial K) = C b - C n * C b := by
    rw [← C_mul, ← C_sub]
    congr 1
    rw [hu, hn]
    push_cast
    ring
  have hRHS : (C u : Polynomial K) * (X - C β) = C u * X - C (n * a) := by
    rw [mul_sub, ← C_mul, hub]
  have h1 : C n * f - X * derivative f = C u * (X - C β) := by
    rw [hRHS, hderiv, hf, hu', C_mul]
    ring
  set γ₀ : K := (derivative f).eval β with hγ₀
  have hγ₀val : γ₀ = n * β ^ m - b := by rw [hγ₀, hderiv]; simp
  have hγ₀0 : γ₀ ≠ 0 := by rw [hγ₀val]; exact sub_ne_zero.mpr hβ
  obtain ⟨D, hD⟩ : (X - C β) ∣ (derivative f - C γ₀) := by
    rw [dvd_iff_isRoot]
    simp [IsRoot, hγ₀]
  have step : C u * derivative f - C (u * γ₀) = (C n * f - X * derivative f) * D := by
    rw [h1, C_mul]
    linear_combination (C u : Polynomial K) * hD
  have key : C (u * γ₀) = (C u + X * D) * derivative f - (C n * D) * f := by
    linear_combination -step
  have hinv : (C ((u * γ₀)⁻¹) : Polynomial K) * C (u * γ₀) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ (mul_ne_zero hu0 hγ₀0), C_1]
  exact ⟨-(C ((u * γ₀)⁻¹) * (C n * D)), C ((u * γ₀)⁻¹) * (C u + X * D), by
    linear_combination (-(C ((u * γ₀)⁻¹) : Polynomial K)) * key + hinv⟩

end Field

/-! ### The trinomial family over the line -/

/-- The **trinomial family** `Y ^ (m + 1) - c X ^ m Y - X ^ m` over the line with coordinate `X`. -/
def ramTrinomial (m : ℕ) (c : k) : Polynomial (Polynomial k) :=
  X ^ (m + 1) - C (Polynomial.C c * Polynomial.X ^ m) * X - C (Polynomial.X ^ m)

/-- The trinomial family, written as `Y ^ (m+1)` minus its lower-order part. -/
theorem ramTrinomial_eq (m : ℕ) (c : k) : ramTrinomial m c
    = X ^ (m + 1) - (C (Polynomial.C c * Polynomial.X ^ m) * X + C (Polynomial.X ^ m)) := by
  rw [ramTrinomial]; ring

/-- The lower-order part of the trinomial family has degree at most `m`. -/
theorem degree_ramTrinomial_tail {m : ℕ} (hm : 1 ≤ m) (c : k) :
    (C (Polynomial.C c * Polynomial.X ^ m) * X
      + C (Polynomial.X ^ m) : Polynomial (Polynomial k)).degree ≤ (m : WithBot ℕ) := by
  refine le_trans (degree_add_le _ _) (max_le (le_trans (degree_mul_le _ _) ?_) ?_)
  · refine le_trans (add_le_add degree_C_le degree_X_le) ?_
    simpa using Nat.one_le_cast.mpr hm
  · exact le_trans degree_C_le (by exact_mod_cast Nat.cast_nonneg m)

/-- The trinomial family is monic. -/
theorem ramTrinomial_monic {m : ℕ} (hm : 1 ≤ m) (c : k) : (ramTrinomial m c).Monic := by
  rw [ramTrinomial_eq]
  exact monic_X_pow_sub
    (lt_of_le_of_lt (degree_ramTrinomial_tail hm c) (by exact_mod_cast Nat.lt_succ_self m))

/-- The trinomial family has degree `m + 1`. -/
theorem ramTrinomial_natDegree {m : ℕ} (hm : 1 ≤ m) (c : k) :
    (ramTrinomial m c).natDegree = m + 1 := by
  rw [ramTrinomial_eq, natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_pow]
  exact lt_of_le_of_lt (natDegree_le_iff_degree_le.mpr (degree_ramTrinomial_tail hm c))
    (Nat.lt_succ_self m)

/-! ### The generic fibre of the trinomial family -/

/-- The generic fibre of the trinomial family, read over the function field of the line. -/
theorem genericPoly_ramTrinomial (m : ℕ) (c : k) :
    genericPoly (ramTrinomial m c)
      = X ^ (m + 1)
        - C (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c * Polynomial.X ^ m)) * X
        - C (algebraMap (Polynomial k) (RatFunc k) (Polynomial.X ^ m)) := by
  simp [genericPoly, ramTrinomial]

/-- **The generic fibre of the trinomial family is separable.**  The linear combination
`(m+1) f - Y f'` vanishes at a *constant* `β`, while `f'(β)` differs from a constant by
`c X ^ m`, which is not constant. -/
theorem genericPoly_ramTrinomial_separable {m : ℕ} (hm : 1 ≤ m) {c : k} (hc : c ≠ 0) :
    (genericPoly (ramTrinomial m c)).Separable := by
  set A := algebraMap (Polynomial k) (RatFunc k) with hA
  have hAinj : Function.Injective A := IsFractionRing.injective (Polynomial k) (RatFunc k)
  have htower : ∀ x : k, algebraMap k (RatFunc k) x = A (Polynomial.C x) := fun x =>
    IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k) x
  have hmk : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set β₀ : k := -(((m + 1 : ℕ) : k)) / ((m : k) * c) with hβ₀
  have hβ₀def : (m : k) * c * β₀ = -(((m + 1 : ℕ) : k)) := by
    rw [hβ₀]
    field_simp
  rw [genericPoly_ramTrinomial]
  refine separable_trinomial (β := algebraMap k (RatFunc k) β₀) ?_ ?_ ?_ ?_
  · exact_mod_cast Nat.cast_ne_zero.mpr (by omega : m ≠ 0)
  · refine fun h => hc ?_
    have := hAinj (h.trans (map_zero A).symm)
    simpa [hc] using congrArg (fun p => Polynomial.coeff p m) this
  · have hC : (Polynomial.C ((m : k)) * Polynomial.C c * Polynomial.C β₀
        : Polynomial k) = -(Polynomial.C (((m + 1 : ℕ) : k))) := by
      simpa only [map_mul, map_neg] using congrArg (Polynomial.C (R := k)) hβ₀def
    rw [htower, ← map_natCast A m, ← map_natCast A (m + 1), ← map_mul, ← map_mul, ← map_mul,
      ← map_neg]
    congr 1
    rw [← map_natCast (Polynomial.C (R := k)) m, ← map_natCast (Polynomial.C (R := k)) (m + 1)]
    linear_combination (Polynomial.X ^ m : Polynomial k) * hC
  · intro h
    rw [htower, ← map_natCast (algebraMap k (RatFunc k)) (m + 1), htower, ← map_pow,
      ← map_mul] at h
    have h2 := hAinj h
    rw [← map_pow, ← map_mul] at h2
    have hdeg := congrArg Polynomial.natDegree h2
    rw [Polynomial.natDegree_C, Polynomial.natDegree_C_mul_X_pow m c hc] at hdeg
    omega

/-- The **cover of the line defined by the trinomial family**. -/
def ramTrinomialCover {m : ℕ} (hm : 1 ≤ m) {c : k} (hc : c ≠ 0) : LineCover :=
  eqCover (ramTrinomial m c) (genericPoly_ramTrinomial_separable hm hc)

@[simp] theorem ramTrinomialCover_M {m : ℕ} (hm : 1 ≤ m) {c : k} (hc : c ≠ 0) :
    (ramTrinomialCover hm hc).M = (genericPoly (ramTrinomial m c)).SplittingField := rfl

/-- The trinomial cover splits the trinomial family. -/
theorem ramTrinomialCover_isSplittingField {m : ℕ} (hm : 1 ≤ m) {c : k} (hc : c ≠ 0) :
    Polynomial.IsSplittingField (RatFunc k) (ramTrinomialCover hm hc).M
      (genericPoly (ramTrinomial m c)) :=
  eqCover_isSplittingField _ _

end Rigidity.RET

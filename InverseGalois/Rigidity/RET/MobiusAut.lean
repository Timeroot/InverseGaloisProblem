/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.Luroth
import InverseGalois.Rigidity.RET.RatFuncSubst

/-!
# Fractional linear automorphisms of the line

The substitutions `u ↦ (a·u + b)/(c·u + d)` with `a·d - b·c ≠ 0` are automorphisms of `K(u)` over
`K`, and they compose by matrix multiplication.  This file builds them from the substitution
machinery of `RatFuncSubst`: a fractional linear function is transcendental over `K` precisely
because it is not a constant — a constant value `e` forces `a = e·c` and `b = e·d`, hence
`a·d - b·c = 0` — and the substitution with the adjugate matrix inverts it, the product of a
matrix with its adjugate being the determinant times the identity.

The composition rule is the reason for the whole file: once it is available, a group of
fractional linear substitutions can be recognized from a matrix computation, with no rational
function manipulation left to do.  Note the order: substituting `g` into `g'` composes the
matrices with the substituted matrix on the right, so `u ↦ M·u` and `u ↦ M'·u` compose to
`u ↦ (M'·M)·u`.

## Main definitions and results

* `Rigidity.RET.mobius` — the fractional linear function `(a·u + b)/(c·u + d)`.
* `Rigidity.RET.transcendental_mobius` — it is transcendental when `a·d - b·c ≠ 0`.
* `Rigidity.RET.subst_mobius` — substitution composes fractional linear functions by matrix
  multiplication.
* `Rigidity.RET.mobiusAut` — the automorphism `u ↦ (a·u + b)/(c·u + d)` of `K(u)`.
* `Rigidity.RET.mobiusAut_mul` — the automorphisms compose by matrix multiplication.
* `Rigidity.RET.mobiusAut_mul_eq` — the composition rule with the product matrix normalized up to
  a scalar.
* `Rigidity.RET.mobiusAut_scalar` — a scalar matrix gives the identity automorphism.
* `Rigidity.RET.mobius_minors` — two equal fractional linear functions have proportional
  matrices, so `Rigidity.RET.mobiusAut_ne` distinguishes automorphisms by their matrices.
* `Rigidity.RET.mobiusRingAut` — the same automorphism with the base field forgotten, together
  with the same composition and separation rules.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

variable {K : Type*} [Field K]

/-! ## Linear and fractional linear functions of the parameter -/

/-- The linear function `a·u + b` of the parameter. -/
def lin (a b : K) : RatFunc K := RatFunc.C a * RatFunc.X + RatFunc.C b

/-- The fractional linear function `(a·u + b)/(c·u + d)` of the parameter. -/
def mobius (a b c d : K) : RatFunc K := lin a b / lin c d

theorem lin_eq_algebraMap (a b : K) :
    lin a b = algebraMap K[X] (RatFunc K) (Polynomial.C a * Polynomial.X + Polynomial.C b) := by
  rw [map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rfl

/-- A linear function with a nonzero coefficient is a nonzero rational function. -/
theorem lin_ne_zero {a b : K} (h : ¬ (a = 0 ∧ b = 0)) : lin a b ≠ 0 := by
  rw [lin_eq_algebraMap]
  intro hz
  have hp : (Polynomial.C a * Polynomial.X + Polynomial.C b : K[X]) = 0 :=
    (injective_iff_map_eq_zero _).mp (IsFractionRing.injective (K[X]) (RatFunc K)) _ hz
  refine h ⟨?_, ?_⟩
  · have := congrArg (fun p => Polynomial.coeff p 1) hp
    simpa using this
  · have := congrArg (fun p => Polynomial.coeff p 0) hp
    simpa using this

/-- The denominator of a fractional linear function with invertible matrix is nonzero. -/
theorem den_ne_zero {a b c d : K} (h : a * d - b * c ≠ 0) : lin c d ≠ 0 := by
  refine lin_ne_zero ?_
  rintro ⟨rfl, rfl⟩
  simp at h

/-- **A fractional linear function with invertible matrix is not a constant**: a constant value
`e` would force `a = e·c` and `b = e·d`, and then the determinant vanishes. -/
theorem mobius_not_mem_bot {a b c d : K} (h : a * d - b * c ≠ 0) :
    mobius a b c d ∉ (⊥ : IntermediateField K (RatFunc K)) := by
  rw [RatFunc.mem_bot_iff]
  rintro ⟨e, he⟩
  rw [mobius, eq_div_iff (den_ne_zero h)] at he
  have hC : RatFunc.C e = algebraMap K[X] (RatFunc K) (Polynomial.C e) :=
    (RatFunc.algebraMap_C e).symm
  rw [lin_eq_algebraMap, lin_eq_algebraMap, hC, ← map_mul] at he
  have hp := (IsFractionRing.injective (K[X]) (RatFunc K)) he
  have h1 := congrArg (fun p => Polynomial.coeff p 1) hp
  have h0 := congrArg (fun p => Polynomial.coeff p 0) hp
  simp at h1 h0
  exact h (by rw [← h1, ← h0]; ring)

/-- A fractional linear function with invertible matrix is transcendental, so it may be
substituted for the parameter. -/
theorem transcendental_mobius {a b c d : K} (h : a * d - b * c ≠ 0) :
    Transcendental K (mobius a b c d) :=
  RatFunc.transcendental_of_not_mem_bot _ (mobius_not_mem_bot h)

/-! ## Composition -/

/-- Substitution turns a linear function into a linear function of the substituted function. -/
theorem subst_lin {a b c d : K} (h : a * d - b * c ≠ 0) (a' b' : K) :
    ratFuncSubst (mobius a b c d) (transcendental_mobius h) (lin a' b')
      = RatFunc.C a' * mobius a b c d + RatFunc.C b' := by
  rw [lin, map_add, map_mul, ratFuncSubst_X, ← RatFunc.algebraMap_eq_C, AlgHom.commutes,
    AlgHom.commutes]

/-- A linear function of a fractional linear function, written over the common denominator. -/
theorem lin_comb {a b c d : K} (hd : lin c d ≠ 0) (a' b' : K) :
    RatFunc.C a' * mobius a b c d + RatFunc.C b'
      = lin (a' * a + b' * c) (a' * b + b' * d) / lin c d := by
  have key : RatFunc.C a' * lin a b + RatFunc.C b' * lin c d
      = lin (a' * a + b' * c) (a' * b + b' * d) := by
    simp only [lin, map_add, map_mul]; ring
  rw [mobius, ← key, ← mul_div_assoc, div_add' _ _ _ hd]

/-- **Substituting one fractional linear function into another multiplies the matrices**, with
the substituted matrix on the right. -/
theorem subst_mobius {a b c d a' b' c' d' : K} (h : a * d - b * c ≠ 0)
    (h' : a' * d' - b' * c' ≠ 0) :
    ratFuncSubst (mobius a b c d) (transcendental_mobius h) (mobius a' b' c' d')
      = mobius (a' * a + b' * c) (a' * b + b' * d) (c' * a + d' * c) (c' * b + d' * d) := by
  have hd : lin c d ≠ 0 := den_ne_zero h
  have hdet : (a' * a + b' * c) * (c' * b + d' * d) - (a' * b + b' * d) * (c' * a + d' * c)
      = (a' * d' - b' * c') * (a * d - b * c) := by ring
  have hd2 : lin (c' * a + d' * c) (c' * b + d' * d) ≠ 0 := by
    refine den_ne_zero (a := a' * a + b' * c) (b := a' * b + b' * d) ?_
    rw [hdet]
    exact mul_ne_zero h' h
  calc ratFuncSubst (mobius a b c d) (transcendental_mobius h) (mobius a' b' c' d')
      = (RatFunc.C a' * mobius a b c d + RatFunc.C b')
        / (RatFunc.C c' * mobius a b c d + RatFunc.C d') := by
        rw [show mobius a' b' c' d' = lin a' b' / lin c' d' from rfl, map_div₀, subst_lin h,
          subst_lin h]
    _ = (lin (a' * a + b' * c) (a' * b + b' * d) / lin c d)
        / (lin (c' * a + d' * c) (c' * b + d' * d) / lin c d) := by
        rw [lin_comb hd, lin_comb hd]
    _ = mobius (a' * a + b' * c) (a' * b + b' * d) (c' * a + d' * c) (c' * b + d' * d) := by
        rw [mobius]
        field_simp

/-- A nonzero constant is a nonzero rational function. -/
theorem C_ne_zero {e : K} (he : e ≠ 0) : RatFunc.C e ≠ 0 := by
  rw [← RatFunc.algebraMap_eq_C]
  exact fun hz => he ((algebraMap K (RatFunc K)).injective (by simpa using hz))

/-- A scalar matrix gives back the parameter. -/
theorem mobius_scalar {e : K} (he : e ≠ 0) : mobius e 0 0 e = RatFunc.X := by
  have h1 : lin e 0 = RatFunc.C e * RatFunc.X := by simp [lin]
  have h2 : lin (0 : K) e = RatFunc.C e := by simp [lin]
  rw [mobius, h1, h2]
  exact mul_div_cancel_left₀ _ (C_ne_zero he)

/-- Scaling a linear function scales its coefficients. -/
theorem lin_smul (e a b : K) : lin (e * a) (e * b) = RatFunc.C e * lin a b := by
  simp only [lin, map_mul]
  ring

/-- **A fractional linear function only depends on its matrix up to a scalar.** -/
theorem mobius_smul {e : K} (he : e ≠ 0) (a b c d : K) :
    mobius (e * a) (e * b) (e * c) (e * d) = mobius a b c d := by
  rw [mobius, mobius, lin_smul, lin_smul, mul_div_mul_left _ _ (C_ne_zero he)]

/-! ## The automorphism -/

/-- The determinant of the adjugate matrix is again nonzero. -/
theorem det_adj {a b c d : K} (h : a * d - b * c ≠ 0) : d * a - -b * -c ≠ 0 := by
  intro hz
  exact h (by linear_combination hz)

/-- **The automorphism `u ↦ (a·u + b)/(c·u + d)` of `K(u)`**, for an invertible matrix.  Its
inverse is the substitution with the adjugate matrix, the two composites being the substitutions
with the determinant times the identity matrix. -/
def mobiusAut {a b c d : K} (h : a * d - b * c ≠ 0) : RatFunc K ≃ₐ[K] RatFunc K :=
  ratFuncSubstEquiv (transcendental_mobius h) (transcendental_mobius (det_adj h))
    (by
      rw [subst_mobius h (det_adj h)]
      convert mobius_scalar h using 2 <;> ring)
    (by
      rw [subst_mobius (det_adj h) h]
      convert mobius_scalar h using 2 <;> ring)

theorem mobiusAut_apply {a b c d : K} (h : a * d - b * c ≠ 0) (x : RatFunc K) :
    mobiusAut h x = ratFuncSubst (mobius a b c d) (transcendental_mobius h) x := rfl

@[simp] theorem mobiusAut_X {a b c d : K} (h : a * d - b * c ≠ 0) :
    mobiusAut h RatFunc.X = mobius a b c d := by
  rw [mobiusAut_apply, ratFuncSubst_X]

/-- **Two automorphisms of `K(u)` over `K` agreeing at the parameter are equal.** -/
theorem mobiusAut_ext {f g : RatFunc K ≃ₐ[K] RatFunc K} (h : f RatFunc.X = g RatFunc.X) : f = g :=
  AlgEquiv.coe_algHom_injective (ratFunc_algHom_ext h)

/-- **The fractional linear automorphisms compose by matrix multiplication.** -/
theorem mobiusAut_mul {a b c d a' b' c' d' : K} (h : a * d - b * c ≠ 0)
    (h' : a' * d' - b' * c' ≠ 0)
    (h'' : (a' * a + b' * c) * (c' * b + d' * d) - (a' * b + b' * d) * (c' * a + d' * c) ≠ 0) :
    mobiusAut h * mobiusAut h' = mobiusAut h'' := by
  refine mobiusAut_ext ?_
  rw [AlgEquiv.mul_apply, mobiusAut_X, mobiusAut_X, mobiusAut_apply, subst_mobius h h']

/-- **Proportional matrices give the same automorphism.** -/
theorem mobiusAut_eq {p q r s A B C D e : K} (hbase : p * s - q * r ≠ 0)
    (hscaled : A * D - B * C ≠ 0) (he : e ≠ 0) (hA : A = e * p) (hB : B = e * q) (hC : C = e * r)
    (hD : D = e * s) : mobiusAut hscaled = mobiusAut hbase := by
  subst hA hB hC hD
  exact mobiusAut_ext (by rw [mobiusAut_X, mobiusAut_X, mobius_smul he])

/-- **The composition rule in normalized form**: the product of the matrices is recognized as a
scalar multiple of a matrix presented in whatever form is convenient. -/
theorem mobiusAut_mul_eq {a b c d a' b' c' d' p q r s e : K} (h : a * d - b * c ≠ 0)
    (h' : a' * d' - b' * c' ≠ 0) (hdet : p * s - q * r ≠ 0) (he : e ≠ 0)
    (hp : a' * a + b' * c = e * p) (hq : a' * b + b' * d = e * q)
    (hr : c' * a + d' * c = e * r) (hs : c' * b + d' * d = e * s) :
    mobiusAut h * mobiusAut h' = mobiusAut hdet := by
  have hraw : (a' * a + b' * c) * (c' * b + d' * d) - (a' * b + b' * d) * (c' * a + d' * c)
      ≠ 0 := by
    rw [hp, hq, hr, hs, show (e * p) * (e * s) - (e * q) * (e * r) = e * e * (p * s - q * r) from
      by ring]
    exact mul_ne_zero (mul_ne_zero he he) hdet
  rw [mobiusAut_mul h h' hraw]
  exact mobiusAut_eq hdet hraw he hp hq hr hs

/-- A scalar matrix gives the identity automorphism. -/
theorem mobiusAut_scalar {e : K} (he : e ≠ 0) (h : e * e - 0 * 0 ≠ 0) : mobiusAut h = 1 := by
  refine mobiusAut_ext ?_
  rw [mobiusAut_X, mobius_scalar he]
  rfl

/-! ## Forgetting the base field -/

/-- **An automorphism of `K(u)` over `K`, read as a ring automorphism.**  Presenting a group of
substitutions this way keeps the base field out of the type, which is what an action on `K(u)`
needs. -/
def ratFuncAlgEquivToRingAut : (RatFunc K ≃ₐ[K] RatFunc K) →* RingAut (RatFunc K) where
  toFun := AlgEquiv.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ratFuncAlgEquivToRingAut_injective :
    Function.Injective (ratFuncAlgEquivToRingAut (K := K)) :=
  fun _ _ h => AlgEquiv.ext fun x => congrArg (fun e : RingAut (RatFunc K) => e x) h

/-- **The fractional linear automorphism as a ring automorphism of `K(u)`.** -/
def mobiusRingAut {a b c d : K} (h : a * d - b * c ≠ 0) : RingAut (RatFunc K) :=
  ratFuncAlgEquivToRingAut (mobiusAut h)

/-- A scalar matrix gives the identity ring automorphism. -/
theorem mobiusRingAut_scalar {e : K} (he : e ≠ 0) (h : e * e - 0 * 0 ≠ 0) :
    mobiusRingAut h = 1 := by
  rw [mobiusRingAut, mobiusAut_scalar he, map_one]

/-- The composition rule, with the product matrix normalized up to a scalar. -/
theorem mobiusRingAut_mul_eq {a b c d a' b' c' d' p q r s e : K} (h : a * d - b * c ≠ 0)
    (h' : a' * d' - b' * c' ≠ 0) (hdet : p * s - q * r ≠ 0) (he : e ≠ 0)
    (hp : a' * a + b' * c = e * p) (hq : a' * b + b' * d = e * q)
    (hr : c' * a + d' * c = e * r) (hs : c' * b + d' * d = e * s) :
    mobiusRingAut h * mobiusRingAut h' = mobiusRingAut hdet := by
  rw [mobiusRingAut, mobiusRingAut, mobiusRingAut, ← map_mul,
    mobiusAut_mul_eq h h' hdet he hp hq hr hs]

/-! ## Distinguishing fractional linear functions -/

/-- **Equal fractional linear functions have proportional matrices**: the three `2 × 2` minors of
the two matrices stacked side by side vanish. -/
theorem mobius_minors {a b c d a' b' c' d' : K} (h : lin c d ≠ 0) (h' : lin c' d' ≠ 0)
    (heq : mobius a b c d = mobius a' b' c' d') :
    a * c' = a' * c ∧ a * d' + b * c' = a' * d + b' * c ∧ b * d' = b' * d := by
  rw [mobius, mobius, div_eq_div_iff h h'] at heq
  rw [lin_eq_algebraMap, lin_eq_algebraMap, lin_eq_algebraMap, lin_eq_algebraMap, ← map_mul,
    ← map_mul] at heq
  have hp := (IsFractionRing.injective (K[X]) (RatFunc K)) heq
  have expand : ∀ p q r s : K,
      (Polynomial.C p * Polynomial.X + Polynomial.C q)
          * (Polynomial.C r * Polynomial.X + Polynomial.C s)
        = Polynomial.C (p * r) * Polynomial.X ^ 2 + Polynomial.C (p * s + q * r) * Polynomial.X
          + Polynomial.C (q * s) := by
    intro p q r s
    simp only [map_mul, map_add]
    ring
  rw [expand, expand] at hp
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun p => Polynomial.coeff p 2) hp
    simpa [-map_mul] using this
  · have := congrArg (fun p => Polynomial.coeff p 1) hp
    simpa [-map_mul] using this
  · have := congrArg (fun p => Polynomial.coeff p 0) hp
    simpa [-map_mul] using this

/-- **Automorphisms with non-proportional matrices are distinct.** -/
theorem mobiusAut_ne {a b c d a' b' c' d' : K} (h : a * d - b * c ≠ 0)
    (h' : a' * d' - b' * c' ≠ 0)
    (hne : ¬ (a * c' = a' * c ∧ a * d' + b * c' = a' * d + b' * c ∧ b * d' = b' * d)) :
    mobiusAut h ≠ mobiusAut h' := by
  intro heq
  refine hne (mobius_minors (den_ne_zero h) (den_ne_zero h') ?_)
  have hX : mobiusAut h RatFunc.X = mobiusAut h' RatFunc.X := by rw [heq]
  rwa [mobiusAut_X, mobiusAut_X] at hX

/-- Ring automorphisms with non-proportional matrices are distinct. -/
theorem mobiusRingAut_ne {a b c d a' b' c' d' : K} (h : a * d - b * c ≠ 0)
    (h' : a' * d' - b' * c' ≠ 0)
    (hne : ¬ (a * c' = a' * c ∧ a * d' + b * c' = a' * d + b' * c ∧ b * d' = b' * d)) :
    mobiusRingAut h ≠ mobiusRingAut h' :=
  fun heq => mobiusAut_ne h h' hne (ratFuncAlgEquivToRingAut_injective heq)

end Rigidity.RET

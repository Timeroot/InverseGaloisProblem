/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Analytic.GermScale

/-!
# The rotation of the Kummer coordinate, as an automorphism of the extension

A branch of a finite extension `M` of `ℂ(T)`, read in the Kummer coordinate `T = s + u ^ d`, is a
`ℂ(T)`-embedding `Ψ : M → MeroGerm 0` of `M` into the meromorphic germs at the origin.  Rotating
the coordinate by a `d`-th root of unity leaves the parameter `T` alone, so it carries one branch
to another; when `M` is normal over `ℂ(T)` the two branches differ by an automorphism of `M`.

That automorphism is the local monodromy in algebraic dress.  Its construction is pure Galois
theory — restriction of an automorphism of an overfield to a normal subextension — and it comes
with the equivariance `Ψ ∘ σ = ρ ∘ Ψ` relating the algebraic and the analytic side.  Iterating it
iterates the rotation, so the order of `σ` is the order of the rotation, provided no nontrivial
rotation fixes the branch: that proviso is the primitivity of the branch, the one place where the
Kummer exponent has to be the right one and not a multiple of it.

## Main results

* `Rigidity.RET.Analytic.exists_algEquiv_of_scaleGerm` — a rotation of the Kummer coordinate is
  realized by an automorphism of the extension.
* `Rigidity.RET.Analytic.apply_pow_eq_scaleGerm` — iterating the automorphism iterates the
  rotation.
* `Rigidity.RET.Analytic.orderOf_eq_of_scaleGerm` — the automorphism has the order of the rotation.
-/

open Filter Topology Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

open MeroGerm

variable {M : Type*} [Field M] [Algebra (RatFunc ℂ) M]

/-- **A rotation of the Kummer coordinate is realized by an automorphism of the extension.**

Composing a branch with the rotation gives another `ℂ(T)`-embedding of `M` into the germs; since
`M` is normal over `ℂ(T)` the two embeddings have the same image, and the automorphism is the one
that identifies them. -/
theorem exists_algEquiv_of_scaleGerm [Normal (RatFunc ℂ) M]
    {s : ℂ} {d : ℕ} (hd : d ≠ 0) {c : ℂ} (hc : c ≠ 0) (hcd : c ^ d = 1)
    {Ψ : M →+* MeroGerm (0 : ℂ)}
    (hΨ : ∀ x : RatFunc ℂ, Ψ (algebraMap (RatFunc ℂ) M x) = kummerRatHom s hd x) :
    ∃ σ : M ≃ₐ[RatFunc ℂ] M, ∀ x : M, Ψ (σ x) = scaleGerm hc (Ψ x) := by
  letI : Algebra (RatFunc ℂ) (MeroGerm (0 : ℂ)) :=
    (kummerRatHom s hd : RatFunc ℂ →+* MeroGerm (0 : ℂ)).toAlgebra
  letI : Algebra M (MeroGerm (0 : ℂ)) := Ψ.toAlgebra
  haveI : IsScalarTower (RatFunc ℂ) M (MeroGerm (0 : ℂ)) :=
    IsScalarTower.of_algebraMap_eq fun x => (hΨ x).symm
  let ρ : MeroGerm (0 : ℂ) →ₐ[RatFunc ℂ] MeroGerm (0 : ℂ) :=
    { scaleGerm hc with
      commutes' := fun x => scaleGerm_kummerRatHom hc hd hcd s x }
  refine ⟨AlgHom.restrictNormal' ρ M, fun x => ?_⟩
  exact AlgHom.restrictNormal_commutes ρ M x

/-- **Iterating the automorphism iterates the rotation.** -/
theorem apply_pow_eq_scaleGerm {Ψ : M →+* MeroGerm (0 : ℂ)} {σ : M ≃ₐ[RatFunc ℂ] M} {c : ℂ}
    (hc : c ≠ 0) (h : ∀ x : M, Ψ (σ x) = scaleGerm hc (Ψ x)) (n : ℕ) (x : M) :
    Ψ ((σ ^ n) x) = scaleGerm (pow_ne_zero n hc) (Ψ x) := by
  induction n with
  | zero =>
    rw [scaleGerm_congr (pow_ne_zero 0 hc) (one_ne_zero : (1 : ℂ) ≠ 0) (pow_zero c) (Ψ x),
      scaleGerm_one, pow_zero]
    rfl
  | succ n ih =>
    rw [pow_succ' σ n]
    show Ψ (σ ((σ ^ n) x)) = _
    rw [h, ih, scaleGerm_scaleGerm,
      scaleGerm_congr (mul_ne_zero (pow_ne_zero n hc) hc) (pow_ne_zero (n + 1) hc)
        (pow_succ c n).symm]

/-- **The automorphism has the order of the rotation**, as soon as no nontrivial rotation of the
coordinate fixes the branch.

Without that proviso only one inequality survives: a branch read in the coordinate `u` is also a
branch read in `u ^ 2`, and the automorphism attached to a rotation of the finer coordinate is the
one attached to its square. -/
theorem orderOf_eq_of_scaleGerm {Ψ : M →+* MeroGerm (0 : ℂ)} {σ : M ≃ₐ[RatFunc ℂ] M} {c : ℂ}
    {d : ℕ} (hc : c ≠ 0) (hd : orderOf c = d)
    (hprim : ∀ (a : ℂ) (ha : a ≠ 0), a ^ d = 1 → (∀ x : M, scaleGerm ha (Ψ x) = Ψ x) → a = 1)
    (h : ∀ x : M, Ψ (σ x) = scaleGerm hc (Ψ x)) : orderOf σ = d := by
  have hΨinj : Function.Injective Ψ := Ψ.injective
  have hcd : c ^ d = 1 := by rw [← hd]; exact pow_orderOf_eq_one c
  have hσd : σ ^ d = 1 := by
    refine AlgEquiv.ext fun x => hΨinj ?_
    rw [apply_pow_eq_scaleGerm hc h d x,
      scaleGerm_congr (pow_ne_zero d hc) (one_ne_zero : (1 : ℂ) ≠ 0) hcd (Ψ x), scaleGerm_one]
    rfl
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hσd) ?_
  have hj : σ ^ orderOf σ = 1 := pow_orderOf_eq_one σ
  have hfix : ∀ x : M, scaleGerm (pow_ne_zero (orderOf σ) hc) (Ψ x) = Ψ x := by
    intro x
    rw [← apply_pow_eq_scaleGerm hc h (orderOf σ) x, hj]
    rfl
  have hone : c ^ orderOf σ = 1 :=
    hprim _ (pow_ne_zero (orderOf σ) hc) (by rw [← pow_mul, mul_comm, pow_mul, hcd, one_pow]) hfix
  rw [← hd]
  exact orderOf_dvd_of_pow_eq_one hone

end Rigidity.RET.Analytic

end

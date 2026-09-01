/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicCompositum
import InverseGalois.CFT.Brauer.CyclicInvariant

/-!
# The invariant of a Brauer class under base change along a field that is not intermediate

Let `E / K` be a cyclic Galois extension which is unramified, let `M / K` be another discretely
valued extension, and let `N` be a field containing both `E` and `M` whose Galois group over `M` is
carried onto `Gal(E/K)` compatibly with the embedding of `E`.  Base change carries a class of the
relative Brauer group `Br(E / K)` into `Br(N / M)`, and the two invariants are related by the
factor by which the value of the base field is multiplied:

`inv_M (res_M x) = r · inv_K x`,   where `v_M (a) = r · v_K (a)` for `a` in `K`.

The reason is transparent on cyclic algebras.  A class of `Br(E / K)` is `(E / K, σ₀, a)`, its
invariant is `v_K(a) / [E : K]`, and base change turns it into `(N / M, σ₁, a)` with the *same*
coefficient and the *same* degree, because the two Galois groups are isomorphic.  So the invariant
computed over `M` is `v_M(a) / [E : K]`, and only the change of valuation is left.

## Main results

* `InverseGalois.CFT.baseChangeHom_mem_relative_compositum`: base change keeps a class in the
  relative Brauer group of the larger extension.
* `InverseGalois.CFT.brauerInvariant_baseChange_compositum`: **the invariant of a Brauer class is
  multiplied by the ratio of the two valuations under base change.**

## Tags

Brauer group, relative Brauer group, invariant map, base change, compositum, class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped WithZero

/-! ### The degree is unchanged -/

section Degree

variable {K E M N : Type} [Field K] [Field E] [Field M] [Field N] [Algebra K E] [Algebra M N]
  [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional M N] [IsGalois M N]

/-- The two Galois groups are isomorphic, so the two extensions have the same degree. -/
theorem finrank_eq_finrank_of_mulEquiv (e : Gal(N/M) ≃* Gal(E/K)) :
    finrank M N = finrank K E := by
  rw [← IsGalois.card_aut_eq_finrank M N, ← IsGalois.card_aut_eq_finrank K E]
  exact Nat.card_congr e.toEquiv

end Degree

variable {K E M N : Type} [Field K] [Field E] [Field M] [Field N]
variable [Algebra K E] [Algebra K M] [Algebra K N] [Algebra E N] [Algebra M N]
variable [IsScalarTower K M N] [IsScalarTower K E N]

/-! ### Base change stays in the relative Brauer group -/

variable (M N) in
/-- **Base change keeps a class in the relative Brauer group of the larger extension**, because
base change to the top field factors both through the base change to the intermediate field of the
first extension and through the base change to the base field of the second. -/
theorem baseChangeHom_mem_relative_compositum {x : BrauerGroup.{0, 0} K}
    (hx : x ∈ BrauerGroup.relative K E) :
    BrauerGroup.baseChangeHom M x ∈ BrauerGroup.relative M N := by
  rw [BrauerGroup.relative, MonoidHom.mem_ker] at hx ⊢
  rw [← MonoidHom.comp_apply, BrauerGroup.baseChangeHom_comp K M N,
    ← BrauerGroup.baseChangeHom_comp K E N, MonoidHom.comp_apply, hx, map_one]

/-! ### The invariant under base change -/

section Invariant

variable [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional M N] [IsGalois M N]
variable [Valued K ℤᵐ⁰] [Valued M ℤᵐ⁰] {mK mM : ℤ} {e : Gal(N/M) ≃* Gal(E/K)}

/-- **The invariant of a Brauer class is multiplied by the ratio of the two valuations under base
change.**  A class of the relative Brauer group is a cyclic algebra, base change keeps both its
coefficient and its degree, and the invariant divides the value of the coefficient by that
degree. -/
theorem brauerInvariant_baseChange_compositum {σ₀ : Gal(E/K)} {σ₁ : Gal(N/M)}
    (hσ₀ : ∀ x : Gal(E/K), x ∈ Subgroup.zpowers σ₀)
    (hσ₁ : ∀ x : Gal(N/M), x ∈ Subgroup.zpowers σ₁) (hgen : e σ₁ = σ₀)
    (he : ∀ (σ : Gal(N/M)) (x : E), σ (algebraMap E N x) = algebraMap E N (e σ x))
    (hurK : HasUnramifiedNormValues K E) (hurM : HasUnramifiedNormValues M N)
    (hmK : IsUnitValGen K mK) (hmM : IsUnitValGen M mM) {r : ℕ}
    (hval : ∀ a : Kˣ,
      unitValDiv hmM (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a))
        = (r : ℤ) * unitValDiv hmK (Additive.ofMul a))
    (x : ↥(BrauerGroup.relative K E)) :
    brauerInvariant hσ₁ hurM hmM
        ⟨BrauerGroup.baseChangeHom M (x : BrauerGroup.{0, 0} K),
          baseChangeHom_mem_relative_compositum M N x.2⟩
      = brauerInvariant hσ₀ hurK hmK x ^ r := by
  have hfr : finrank M N = finrank K E := finrank_eq_finrank_of_mulEquiv e
  obtain ⟨x, hx⟩ := x
  obtain ⟨a, rfl⟩ := exists_cyclicBrauerHom_eq hσ₀ x hx
  have hsub : (⟨BrauerGroup.baseChangeHom M (cyclicBrauerHom hσ₀ a),
        baseChangeHom_mem_relative_compositum M N hx⟩ : ↥(BrauerGroup.relative M N))
      = ⟨cyclicBrauerHom hσ₁ (Units.map (algebraMap K M).toMonoidHom a),
        cyclicBrauerHom_mem_relative hσ₁ (Units.map (algebraMap K M).toMonoidHom a)⟩ :=
    Subtype.ext (baseChangeHom_cyclicBrauerHom_compositum hσ₀ hσ₁ hgen he a)
  rw [hsub, brauerInvariant_apply_cyclicBrauerHom, brauerInvariant_apply_cyclicBrauerHom,
    baseInvariant_apply, baseInvariant_apply, ← ofAdd_nsmul]
  refine congrArg Multiplicative.ofAdd ?_
  rw [unitInvariant_apply, unitInvariant_apply, hval]
  have hsmul : r •
        (QuotientAddGroup.mk (((unitValDiv hmK (Additive.ofMul a) : ℤ) : ℚ)
          / ((finrank K E : ℕ) : ℚ)) : QModZ)
      = QuotientAddGroup.mk ((r : ℚ) * (((unitValDiv hmK (Additive.ofMul a) : ℤ) : ℚ)
          / ((finrank K E : ℕ) : ℚ))) := by
    rw [← nsmul_eq_mul]
    exact (map_nsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) _ _).symm
  rw [hsmul, hfr]
  refine congrArg QuotientAddGroup.mk ?_
  push_cast
  ring

end Invariant

end InverseGalois.CFT

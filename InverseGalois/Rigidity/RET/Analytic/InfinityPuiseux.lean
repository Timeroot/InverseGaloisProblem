/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.TwistMinpoly
import InverseGalois.Rigidity.RET.Analytic.LaurentExpansion
import InverseGalois.Rigidity.RET.Analytic.InfinityRoot
import InverseGalois.Rigidity.RET.Local.PuiseuxAssembly

/-!
# The Puiseux parametrisation of a cover at the point at infinity

A branch of the roots of the equation of a cover, read in the parameter at infinity `T = (uᵈ)⁻¹`,
is a meromorphic germ at `u = 0`; its Laurent expansion is a formal solution of the equation of the
cover written in the coordinate that exchanges `0` with the point at infinity.  That is exactly the
data of a Puiseux parametrisation of the twisted cover at the point `0`, so the whole local theory
at a point of the line applies at infinity, with the twist taking the place of the cover.

The bridge is one identity between two homomorphisms of the coordinate ring of the line into formal
Laurent series: reading a polynomial in the twisted coordinate and expanding it in the Kummer
parameter at `0` is the same as substituting the parameter at infinity and taking the Laurent
expansion of the resulting germ.  Both sides are ring homomorphisms out of a polynomial ring, so
the identity is checked on constants and on the coordinate.

Once the parametrisation is available, a rotation of the local coordinate by a `d`-th root of unity
names an inertia element of the twist at `0`; if the cover is unramified at infinity that element
is trivial, and the branch is therefore invariant under the rotation.

## Main results

* `Rigidity.RET.Analytic.kummerLift_invSubst_comp` — the bridge identity.
* `Rigidity.RET.Analytic.exists_puiseuxEmbedding_at_infinity` — a meromorphic branch of the roots
  in the parameter at infinity is a Puiseux parametrisation of the twisted cover at `0`.
* `Rigidity.RET.Analytic.eventuallyEq_scale_of_isUnramifiedAtInfinity` — over a cover unramified at
  infinity, such a branch is invariant under rotation of the parameter by a `d`-th root of unity.
-/

open Polynomial Filter Topology GeomAKLB

noncomputable section

namespace Rigidity.RET

/-! ### The inversion read backwards -/

/-- The inversion is its own inverse on the parameter. -/
theorem invSubstEquiv_symm_X :
    (invSubst.toRingEquiv : RatFunc k ≃+* RatFunc k).symm (RatFunc.X : RatFunc k)
      = (RatFunc.X : RatFunc k)⁻¹ := by
  refine (RingEquiv.symm_apply_eq _).2 ?_
  show (RatFunc.X : RatFunc k) = invSubst (RatFunc.X : RatFunc k)⁻¹
  rw [map_inv₀, invSubst_X, inv_inv]

/-- The inversion fixes the constants. -/
theorem invSubstEquiv_symm_algebraMap (a : k) :
    (invSubst.toRingEquiv : RatFunc k ≃+* RatFunc k).symm (algebraMap k (RatFunc k) a)
      = algebraMap k (RatFunc k) a := by
  refine (RingEquiv.symm_apply_eq _).2 ?_
  exact (invSubst.commutes a).symm

namespace Analytic

/-! ### The bridge identity -/

/-- **Reading the coordinate ring in the twisted coordinate and expanding it at `0` is substituting
the parameter at infinity.**  Both sides are ring homomorphisms out of the coordinate ring of the
line, so it is enough to compare them on the constants, which both send to constants, and on the
coordinate, which both send to the inverse of the `d`-th power of the formal variable. -/
theorem kummerLift_invSubst_comp [Algebra k ℂ] {d : ℕ} (hd : 0 < d) :
    (kummerLift ℂ (0 : k) hd).comp
        (((invSubst.toRingEquiv : RatFunc k ≃+* RatFunc k).symm : RatFunc k →+* RatFunc k).comp
          (algebraMap (Polynomial k) (RatFunc k)))
      = (meroExpand.comp (invAlgHom d).toRingHom).comp
          (Polynomial.mapRingHom (algebraMap k ℂ)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · show kummerLift ℂ (0 : k) hd
        ((invSubst.toRingEquiv : RatFunc k ≃+* RatFunc k).symm
          (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C a)))
      = meroExpand ((invAlgHom d) (Polynomial.mapRingHom (algebraMap k ℂ) (Polynomial.C a)))
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C, invAlgHom_C, meroExpand_constHom,
      show algebraMap (Polynomial k) (RatFunc k) (Polynomial.C a) = algebraMap k (RatFunc k) a from
        (IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k) a).symm,
      invSubstEquiv_symm_algebraMap,
      IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k) a,
      show algebraMap k (Polynomial k) a = Polynomial.C a from rfl,
      kummerLift_algebraMap, kummerSubst_C]
  · show kummerLift ℂ (0 : k) hd
        ((invSubst.toRingEquiv : RatFunc k ≃+* RatFunc k).symm
          (algebraMap (Polynomial k) (RatFunc k) Polynomial.X))
      = meroExpand ((invAlgHom d) (Polynomial.mapRingHom (algebraMap k ℂ) Polynomial.X))
    rw [Polynomial.coe_mapRingHom, Polynomial.map_X, invAlgHom_X, meroExpand_invGerm,
      RatFunc.algebraMap_X, invSubstEquiv_symm_X, map_inv₀,
      show (RatFunc.X : RatFunc k) = algebraMap (Polynomial k) (RatFunc k) Polynomial.X from
        RatFunc.algebraMap_X.symm,
      kummerLift_algebraMap, kummerSubst_X]
    simp

/-! ### The parametrisation at infinity -/

section AtInfinity

variable {L : LineCover} [Algebra k ℂ] {α : L.M} {d : ℕ} {g : ℂ → ℂ}

/-- **A meromorphic branch of the roots in the parameter at infinity solves the equation of the
twisted cover at `0`.** -/
theorem eval₂_kummerLift_minpoly_ofBase (hd : 0 < d) (hα : IsIntegral (Polynomial k) α)
    (hg : MeromorphicAt g 0)
    (hroot : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (spec (complexEquation α) ((u ^ d)⁻¹)).eval (g u) = 0) :
    Polynomial.eval₂ (kummerLift ℂ (0 : k) hd) (meroExpand (MeroGerm.of hg))
        (minpoly (RatFunc k) (Twist.ofBase invSubst.toRingEquiv L.M α)) = 0 := by
  have h0 : Polynomial.eval₂ (invAlgHom d).toRingHom (MeroGerm.of hg) (complexEquation α) = 0 :=
    eval₂_invAlgHom_eq_zero hg hroot
  have h1 : Polynomial.eval₂ (meroExpand.comp (invAlgHom d).toRingHom)
      (meroExpand (MeroGerm.of hg)) (complexEquation α) = 0 := by
    rw [← Polynomial.hom_eval₂, h0, map_zero]
  rw [complexEquation, Polynomial.eval₂_map] at h1
  rw [Twist.minpoly_ofBase, minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc k) hα,
    Polynomial.map_map, Polynomial.eval₂_map, kummerLift_invSubst_comp hd]
  exact h1

/-- **A meromorphic branch of the roots in the parameter at infinity is a Puiseux parametrisation of
the twisted cover at `0`.** -/
theorem exists_puiseuxEmbedding_at_infinity (hd : 0 < d) (hα : IsIntegral (Polynomial k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤) (hg : MeromorphicAt g 0)
    (hroot : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (spec (complexEquation α) ((u ^ d)⁻¹)).eval (g u) = 0) :
    ∃ ψ : PuiseuxEmbedding (Twist invSubst.toRingEquiv L.M) ℂ (0 : k) d,
      ψ.hom (Twist.ofBase invSubst.toRingEquiv L.M α) = meroExpand (MeroGerm.of hg) :=
  exists_puiseuxEmbedding_hom_eq_of_eval₂_eq_zero ℂ (0 : k) hd
    (Twist.ofBase invSubst.toRingEquiv L.M α) (Algebra.IsIntegral.isIntegral _)
    (Twist.adjoin_ofBase_eq_top hgen) _ (eval₂_kummerLift_minpoly_ofBase hd hα hg hroot)

/-- **Over a cover unramified at infinity a branch of the roots in the parameter at infinity is
invariant under rotation of the parameter.**  The rotation by a `d`-th root of unity names an
inertia element of the twisted cover at `0`, and that element is trivial. -/
theorem eventuallyEq_scale_of_isUnramifiedAtInfinity (hd : 0 < d)
    (hα : IsIntegral (Polynomial k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    (hg : MeromorphicAt g 0)
    (hroot : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (spec (complexEquation α) ((u ^ d)⁻¹)).eval (g u) = 0)
    (hinf : L.IsUnramifiedAtInfinity) {ζ : ℂ} (hζ : ζ ^ d = 1) :
    ∀ᶠ u in 𝓝[≠] (0 : ℂ), g u = g (ζ * u) := by
  obtain ⟨ψ, hψ⟩ := exists_puiseuxEmbedding_at_infinity hd hα hgen hg hroot
  have hnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ hd.ne'
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨σ, hσin, hσ⟩ := (L.twist invSubst.toRingEquiv).exists_isInertiaAt_of_puiseux ψ hζ0 hζ
    (α := Twist.ofBase invSubst.toRingEquiv L.M α) (Algebra.IsIntegral.isIntegral _)
    (Twist.adjoin_ofBase_eq_top hgen)
  have h2 : ψ.hom (Twist.ofBase invSubst.toRingEquiv L.M α)
      = laurentRescale hζ0 (ψ.hom (Twist.ofBase invSubst.toRingEquiv L.M α)) := by
    have h := hσ (Twist.ofBase invSubst.toRingEquiv L.M α)
    rwa [hinf σ hσin] at h
  rw [hψ] at h2
  have h3 : meroExpand (MeroGerm.of hg)
      = meroExpand (Analytic.scaleGerm hζ0 (MeroGerm.of hg)) := by
    rw [meroExpand_scaleGerm hζ0 hnorm.le]
    exact h2
  have h4 : MeroGerm.of hg = MeroGerm.of (meromorphicAt_comp_scaleFun (c := ζ) hg) := by
    refine meroExpand_injective ?_
    rw [h3, scaleGerm_of]
  have h5 := congrArg Subtype.val h4
  rw [MeroGerm.of_val, MeroGerm.of_val] at h5
  filter_upwards [Filter.Germ.coe_eq.1 h5] with u hu
  exact hu

end AtInfinity

end Analytic

end Rigidity.RET

end

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.BaseChart
import InverseGalois.Rigidity.RET.TranslateInfinity

/-!
# Reading a place of a power chart from the chart it covers

A field `M` finite and Galois over the line can carry a second line, through a parameter `u` whose
`m`-th power is the coordinate of the first.  The two lines are two ways of addressing the same
places of `M`: a place at which `u - a` vanishes is a place at which `T - aᵐ` vanishes, because
`T - aᵐ = uᵐ - aᵐ` is divisible by `u - a`.  So a symmetry inertial at a point `a` of the second
line is inertial at the point `aᵐ` of the first.

## Main results

* `Rigidity.RET.LineCover.isInertiaAt_pow_of_chart` — an inertia element at `a` for the chart cut
  out by an `m`-th root `u` of the coordinate is an inertia element at `aᵐ` for the cover itself.
-/

open Polynomial IsDedekindDomain

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

namespace LineCover

attribute [local instance] LineCover.instAlgebraConst LineCover.instTowerConstRatFunc
  LineCover.instTowerConstPoly

variable (P : LineCover) (ρ : RatFunc k →+* P.M)

section Chart

variable (hρ : ∀ f : RatFunc k, algebraMap (RatFunc k) P.M f ∈ ρ.fieldRange)
  (hC : ∀ c : k, ρ (algebraMap k (RatFunc k) c)
    = algebraMap (RatFunc k) P.M (algebraMap k (RatFunc k) c))
  {m : ℕ} (hpow : ρ RatFunc.X ^ m = algebraMap (RatFunc k) P.M RatFunc.X)
  [FiniteDimensional (RatFunc k) (Chart P.M ρ)] [IsGalois (RatFunc k) (Chart P.M ρ)]

include hC hpow

/-- **A polynomial in the coordinate of the line is the substituted polynomial in the parameter of
the chart.**  The parameter is an `m`-th root of the coordinate, so substituting `Xᵐ` for `X` in a
polynomial and reading it on the chart reads the polynomial itself on the line. -/
theorem algebraMap_poly_chart (p : Polynomial k) :
    algebraMap (Polynomial k) P.M p
      = algebraMap (Polynomial k) (LineCover.of (Chart P.M ρ)).M (p.comp (X ^ m)) := by
  set N := LineCover.of (Chart P.M ρ) with hN
  have key : (algebraMap (Polynomial k) P.M : Polynomial k →+* P.M)
      = (algebraMap (Polynomial k) N.M).comp
        (Polynomial.aeval (X ^ m : Polynomial k)).toRingHom := by
    refine Polynomial.ringHom_ext ?_ ?_
    · intro c
      show algebraMap (Polynomial k) P.M (C c)
        = algebraMap (Polynomial k) N.M ((Polynomial.aeval (X ^ m : Polynomial k)) (C c))
      have hCc : algebraMap (Polynomial k) (RatFunc k) (C c) = algebraMap k (RatFunc k) c := by
        rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
      rw [Polynomial.aeval_C, Polynomial.algebraMap_eq,
        IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) P.M,
        IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) N.M, hCc, ← hC c]
      rfl
    · show algebraMap (Polynomial k) P.M X
        = algebraMap (Polynomial k) N.M ((Polynomial.aeval (X ^ m : Polynomial k)) X)
      rw [Polynomial.aeval_X, map_pow,
        IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) P.M,
        IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) N.M, RatFunc.algebraMap_X,
        ← hpow]
      rfl
  have hp := congrArg (fun f : Polynomial k →+* P.M => f p) key
  simpa [Polynomial.comp_eq_aeval] using hp

/-- **An inertia element of the power chart is an inertia element of the cover, at the power of the
point.**  A place of the cover at which the chart parameter takes the value `a` is a place at which
the coordinate takes the value `aᵐ`, since `T - aᵐ` factors through `u - a`. -/
theorem isInertiaAt_pow_of_chart {a : k} {σ : (LineCover.of (Chart P.M ρ)).deck}
    (hσ : (LineCover.of (Chart P.M ρ)).IsInertiaAt a σ) :
    P.IsInertiaAt (a ^ m) (Chart.deckHom ρ hρ σ) := by
  set N := LineCover.of (Chart P.M ρ) with hN
  obtain ⟨Q, hQmax, hQover, hσQ⟩ := hσ
  haveI := hQmax
  haveI := hQover
  set v : HeightOneSpectrum (Bring N.M) := ⟨Q, hQmax.isPrime, Q_ne_bot _ a Q⟩ with hv
  set A : ValuationSubring N.M := placeSubring N.M v with hA
  have hcomm : ∀ (τ : N.deck) (b : Bring N.M),
      algebraMap (Bring N.M) N.M (τ • b) = τ • algebraMap (Bring N.M) N.M b :=
    fun τ b => coe_smul_geom N.M τ b
  have hI := isInertialAtPlace_of_mem_inertia (F := N.M) (B := Bring N.M) hcomm (v := v) hσQ
  -- the parameter takes the value `a` at the place
  have hmemQ : algebraMap (Polynomial k) (Bring N.M) (X - C a) ∈ v.asIdeal := by
    have hmem : (X - C a : Polynomial k) ∈ Ideal.under (Polynomial k) Q := by
      rw [← hQover.over]
      exact Ideal.mem_span_singleton_self _
    exact hmem
  refine isInertiaAt_of_inertial P (a ^ m) A (placeSubring_ne_top (F := N.M) v) ?_ ?_ _ ?_
  · -- the constants are regular at the place
    intro c
    rw [algebraMap_poly_chart P ρ hC hpow (C c)]
    exact algebraMap_poly_mem_placeSubring N v _
  · -- the coordinate takes the value `aᵐ` at the place
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (X : Polynomial k) (C a) m
    have hcomp : (X - C (a ^ m) : Polynomial k).comp (X ^ m) = (X - C a) * q := by
      rw [sub_comp, X_comp, C_comp, map_pow]
      exact hq
    rw [algebraMap_poly_chart P ρ hC hpow (X - C (a ^ m)), hcomp, map_mul, map_mul]
    have h1 : A.valuation (algebraMap (Polynomial k) N.M (X - C a)) < 1 :=
      valuation_algebraMap_poly_lt_one N v hmemQ
    have h2 : A.valuation (algebraMap (Polynomial k) N.M q) ≤ 1 :=
      A.valuation_le_one ⟨_, algebraMap_poly_mem_placeSubring N v q⟩
    calc A.valuation (algebraMap (Polynomial k) N.M (X - C a))
            * A.valuation (algebraMap (Polynomial k) N.M q)
        ≤ A.valuation (algebraMap (Polynomial k) N.M (X - C a)) * 1 := mul_le_mul_right h2 _
      _ = A.valuation (algebraMap (Polynomial k) N.M (X - C a)) := mul_one _
      _ < 1 := h1
  · -- the symmetry is inertial at the place, and acts on the cover as it acts on the chart
    intro x hx
    exact hI x hx

end Chart

end LineCover

end Rigidity.RET

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Rigidity.RET.RegularCriterion

/-!
# A resolvent criterion for a regular realization

The reusable seam of the Hilbert-irreducibility side of this development takes a family of
polynomials over `ℚ[T]` together with an absolutely irreducible *resolvent* of degree `|G|`, and
produces a realization of `G` over `ℚ` by specializing.  This file is the generic counterpart: it
keeps everything over `ℚ(T)` and produces a realization of `G` *over `ℚ(T)`*, regular.

The input is a Galois extension `L / ℚ(T)`, an injection of its Galois group into `G` — the
landing certificate — and a root in `L` of a monic polynomial `R ∈ ℚ[T][X]` of degree `|G|` that
stays irreducible over `ℚ̄(T)`.  Three inequalities close the loop: the injection bounds the Galois
group by `|G|`, the root generates a subfield of degree `|G|`, and a subfield is no larger than
the whole field.  So the Galois group *is* `G`, the root generates `L`, and the resolvent is its
minimal polynomial — whose absolute irreducibility is exactly regularity.

The absolute irreducibility of the resolvent therefore plays two roles at once: over `ℚ(T)` it
forces the resolvent to be the minimal polynomial, and over `ℚ̄(T)` it forces the extension to have
no constants beyond `ℚ`.

## Main results

* `IsRegularInverseGalois.of_embeds_and_root` — the criterion.
-/

open Polynomial

noncomputable section

namespace IsRegularInverseGalois

open Rigidity.RET

/-- The geometric base field `ℚ̄(T)`, as the fraction field of the polynomial ring over the
algebraic closure of the rationals. -/
local notation "ℚ̄T" => FractionRing (Polynomial (AlgebraicClosure ℚ))

/-- **A Galois extension of `ℚ(T)` whose group embeds into `G` and which contains a root of an
absolutely irreducible resolvent of degree `|G|` is a regular realization of `G`.**

This is the generic counterpart of the specialization seam `IsInverseGalois.of_regular_family`:
the same two ingredients — a landing certificate and a root of the resolvent — but read over
`ℚ(T)` rather than at a specialized parameter, and delivering regularity for free. -/
theorem of_embeds_and_root {G : Type*} [Group G] (L : Type) [Field L]
    [Algebra (RatFunc ℚ) L] [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]
    (R : ℚ[X][X]) (hRmonic : R.Monic) (hRdeg : R.natDegree = Nat.card G)
    (hRabs : Irreducible (R.map toClosureFrac))
    (α : L) (hα : (aeval α) (R.map (algebraMap ℚ[X] (RatFunc ℚ))) = 0)
    (φ : (L ≃ₐ[RatFunc ℚ] L) →* G) (hφ : Function.Injective φ) :
    IsRegularInverseGalois G := by
  set r : (RatFunc ℚ)[X] := R.map (algebraMap ℚ[X] (RatFunc ℚ)) with hr
  have hrmonic : r.Monic := hRmonic.map _
  -- the geometric base change of `r` is the geometric base change of `R`
  have hcomp : (algebraMap (RatFunc ℚ) ℚ̄T).comp (algebraMap ℚ[X] (RatFunc ℚ)) = toClosureFrac :=
    RingHom.ext algebraMap_ratFunc_geom_comp
  have hrmap : r.map (algebraMap (RatFunc ℚ) ℚ̄T) = R.map toClosureFrac := by
    rw [hr, Polynomial.map_map, hcomp]
  -- absolute irreducibility descends to irreducibility over `ℚ(T)`
  have hrirr : Irreducible r :=
    Monic.irreducible_of_irreducible_map (algebraMap (RatFunc ℚ) ℚ̄T) r hrmonic
      (by rw [hrmap]; exact hRabs)
  have hminpoly : minpoly (RatFunc ℚ) α = r :=
    (minpoly.eq_of_irreducible_of_monic hrirr hα hrmonic).symm
  -- the resolvent has positive degree, so `G` is finite
  have hRpos : 0 < R.natDegree := by
    have h := hRabs.natDegree_pos
    rwa [hRmonic.natDegree_map] at h
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [← hRdeg]; exact hRpos.ne')
  -- the root generates a subfield of degree `|G|`
  have hfr : Module.finrank (RatFunc ℚ) (IntermediateField.adjoin (RatFunc ℚ) {α})
      = Nat.card G := by
    rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite _ α), hminpoly, hr,
      hRmonic.natDegree_map, hRdeg]
  -- the three inequalities
  have hcard : Nat.card (L ≃ₐ[RatFunc ℚ] L) = Module.finrank (RatFunc ℚ) L :=
    IsGalois.card_aut_eq_finrank (RatFunc ℚ) L
  have hle1 : Module.finrank (RatFunc ℚ) L ≤ Nat.card G := by
    rw [← hcard]; exact Nat.card_le_card_of_injective φ hφ
  have hle2 : Nat.card G ≤ Module.finrank (RatFunc ℚ) L := by
    rw [← hfr]
    exact Module.finrank_bot_le_finrank_of_isScalarTower (RatFunc ℚ)
      (IntermediateField.adjoin (RatFunc ℚ) {α}) L
  have hdim : Module.finrank (RatFunc ℚ) L = Nat.card G := le_antisymm hle1 hle2
  -- hence the root generates the whole field
  have htop : IntermediateField.adjoin (RatFunc ℚ) {α} = ⊤ := by
    refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
    rw [hfr, IntermediateField.finrank_top', hdim]
  -- and the landing certificate is an isomorphism
  have hbij : Function.Bijective φ := by
    refine (Nat.bijective_iff_injective_and_card φ).2 ⟨hφ, ?_⟩
    rw [hcard, hdim]
  exact of_primitive_irreducible L α htop R hminpoly hRabs (MulEquiv.ofBijective φ hbij)

end IsRegularInverseGalois

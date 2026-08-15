/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.InertiaGen
import InverseGalois.Rigidity.RET.Unramified

/-!
# Places from Laurent series embeddings

A point `s` of the line together with a positive integer `e` determines a local coordinate
`X = s + u ^ e` and hence an embedding of the coordinate ring of the line into the ring of formal
power series in `u`.  A **Puiseux embedding of index `e`** of a cover at `s` is an extension of that
embedding to the function field of the cover, landing in the field of formal Laurent series.

Such an embedding forces the cover to be at worst `e`-fold ramified over `s`.  The integral model of
the cover is integral over the coordinate ring, so the embedding carries it into the power series
ring, which is integrally closed; pulling back the maximal ideal produces a place of the cover above
`s`.  The uniformiser `X - s` of the line has order exactly `e` in the power series ring, so the
place cannot absorb more than `e` powers of the maximal ideal, and its ramification index is at most
`e`.  Since the deck group is transitive on the places above a point, the bound holds at every place
above `s`, and the inertia groups there have order at most `e`.

The case `e = 1` is the one that crosses the analytic divide: an honest power series solution of the
equation of the cover at `s` — the Taylor expansion of a single-valued branch — proves that the
cover is unramified at `s`.  For general `e` the bound is sharp from below as soon as the point
carries an inertia element of order `e`, and then that element *generates* the inertia group: a
Puiseux parametrisation of index `e` converts a local monodromy generator into a distinguished
inertia element.

The coefficients of the local coordinate are allowed to lie in any extension `K` of the constant
field, because the parametrisations that arise analytically are complex ones while the cover itself
is defined over the algebraic closure of the rationals.

## Main definitions

* `Rigidity.RET.kummerSubst` — the substitution `X ↦ s + u ^ e` of the coordinate ring into formal
  power series.
* `Rigidity.RET.PuiseuxEmbedding` — an embedding of the function field of a cover into formal
  Laurent series extending `kummerSubst`.

## Main results

* `Rigidity.RET.PuiseuxEmbedding.ramificationIdxIn_le` — the ramification index above `s` is at
  most `e`.
* `Rigidity.RET.PuiseuxEmbedding.card_inertia_le` — the inertia group at any place above `s` has
  order at most `e`.
* `Rigidity.RET.PuiseuxEmbedding.geomInertia_eq_zpowers` — an inertia element of order at least the
  index generates the whole inertia group of its place.
* `Rigidity.RET.LineCover.orderOf_le_of_isInertiaAt` — a Puiseux embedding of index `e` at `s`
  bounds the order of every inertia element of the cover at `s`.
* `Rigidity.RET.LineCover.isInertiaGenAt_of_puiseux` — with the matching index, an inertia element
  at `s` is a distinguished one.
* `Rigidity.RET.LineCover.isUnramifiedOutside_of_puiseux` — a cover admitting a Puiseux embedding of
  index one at every point outside `S` is unramified outside `S`.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB GeomAKLB.instTorsionFree

/-! ### The local coordinate -/

section Coordinate

variable (K : Type) [Field K] [Algebra k K]

/-- The **Kummer substitution** `X ↦ s + u ^ e`, from the coordinate ring of the line to the ring of
formal power series in the local coordinate `u` over an extension `K` of the constant field. -/
def kummerSubst (s : k) (e : ℕ) : Polynomial k →+* PowerSeries K :=
  Polynomial.eval₂RingHom ((PowerSeries.C (R := K)).comp (algebraMap k K))
    (PowerSeries.C (algebraMap k K s) + PowerSeries.X ^ e)

@[simp] theorem kummerSubst_C (s : k) (e : ℕ) (a : k) :
    kummerSubst K s e (Polynomial.C a) = PowerSeries.C (algebraMap k K a) := by
  simp [kummerSubst]

@[simp] theorem kummerSubst_X (s : k) (e : ℕ) :
    kummerSubst K s e Polynomial.X = PowerSeries.C (algebraMap k K s) + PowerSeries.X ^ e := by
  simp [kummerSubst]

/-- The uniformiser of the line at `s` becomes the `e`-th power of the local coordinate. -/
@[simp] theorem kummerSubst_X_sub_C (s : k) (e : ℕ) :
    kummerSubst K s e (Polynomial.X - Polynomial.C s) = PowerSeries.X ^ e := by
  rw [map_sub, kummerSubst_X, kummerSubst_C, add_sub_cancel_left]

/-- The constant term of a substituted polynomial is its value at the point. -/
theorem constantCoeff_kummerSubst {e : ℕ} (he : 0 < e) (s : k) (p : Polynomial k) :
    PowerSeries.constantCoeff (kummerSubst K s e p) = algebraMap k K (p.eval s) := by
  have h : (PowerSeries.constantCoeff (R := K)).comp (kummerSubst K s e)
      = (algebraMap k K).comp (Polynomial.evalRingHom s) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp [he.ne']
  exact congrArg (fun f => f p) h

/-- The place of the line cut out by the local coordinate is the point `s`. -/
theorem comap_kummerSubst {e : ℕ} (he : 0 < e) (s : k) :
    Ideal.comap (kummerSubst K s e) (Ideal.span {(PowerSeries.X : PowerSeries K)}) = placeP s := by
  ext p
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff,
    constantCoeff_kummerSubst K he, map_eq_zero_iff _ (algebraMap k K).injective,
    show placeP s = Ideal.span {Polynomial.X - Polynomial.C s} from rfl,
    Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]
  exact Iff.rfl

end Coordinate

section Embedding

variable {K : Type} [Field K] [Algebra k K]
  {Ω : Type} [Field Ω] [Algebra (Polynomial k) Ω]

/-- A **Puiseux embedding of index `e`** of the cover `Ω` at the point `s`: an embedding of the
function field into formal Laurent series in a local coordinate `u`, under which the coordinate of
the line becomes `s + u ^ e`. -/
structure PuiseuxEmbedding (Ω : Type) [Field Ω] [Algebra (Polynomial k) Ω] (K : Type) [Field K]
    [Algebra k K] (s : k) (e : ℕ) where
  /-- the embedding of the function field into formal Laurent series. -/
  hom : Ω →+* LaurentSeries K
  /-- the index of the local coordinate is positive. -/
  index_pos : 0 < e
  /-- the coordinate of the line becomes `s + u ^ e`. -/
  compat : ∀ p : Polynomial k, hom (algebraMap (Polynomial k) Ω p)
    = algebraMap (PowerSeries K) (LaurentSeries K) (kummerSubst K s e p)

namespace PuiseuxEmbedding

variable {s : k} {e : ℕ} (ψ : PuiseuxEmbedding Ω K s e)

omit [Algebra k K] in
theorem injective_algebraMap :
    Function.Injective (algebraMap (PowerSeries K) (LaurentSeries K)) :=
  IsFractionRing.injective _ _

/-- The embedding carries the integral model into the power series ring: the model is integral over
the coordinate ring, and the power series ring is integrally closed in its fraction field. -/
theorem mem_range (x : Bring Ω) :
    ψ.hom (x : Ω) ∈ (algebraMap (PowerSeries K) (LaurentSeries K)).range := by
  have hx : IsIntegral (Polynomial k) (x : Ω) := by
    have := x.2
    rwa [mem_integralClosure_iff] at this
  have hcomp : (algebraMap (PowerSeries K) (LaurentSeries K)).comp (kummerSubst K s e)
      = ψ.hom.comp (algebraMap (Polynomial k) Ω) :=
    RingHom.ext fun p => (ψ.compat p).symm
  have : IsIntegral (PowerSeries K) (ψ.hom (x : Ω)) :=
    hx.map_of_comp_eq (kummerSubst K s e) ψ.hom hcomp
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
  exact ⟨y, hy⟩

/-- The power series ring, identified with the range of its embedding into Laurent series. -/
def rangeEquiv : PowerSeries K ≃+* (algebraMap (PowerSeries K) (LaurentSeries K)).range :=
  RingEquiv.ofBijective (RingHom.rangeRestrict _)
    ⟨fun _ _ h => injective_algebraMap (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

/-- The restriction of a Puiseux embedding to the integral model, as a map to formal power
series. -/
def psHom : Bring Ω →+* PowerSeries K :=
  rangeEquiv.symm.toRingHom.comp
    (RingHom.codRestrict (ψ.hom.comp (algebraMap (Bring Ω) Ω)) _ ψ.mem_range)

@[simp] theorem algebraMap_psHom (x : Bring Ω) :
    algebraMap (PowerSeries K) (LaurentSeries K) (ψ.psHom x) = ψ.hom (x : Ω) := by
  have h := rangeEquiv.apply_symm_apply
    (RingHom.codRestrict (ψ.hom.comp (algebraMap (Bring Ω) Ω)) _ ψ.mem_range x)
  exact congrArg Subtype.val h

theorem psHom_algebraMap (p : Polynomial k) :
    ψ.psHom (algebraMap (Polynomial k) (Bring Ω) p) = kummerSubst K s e p := by
  refine injective_algebraMap ?_
  rw [algebraMap_psHom]
  rw [show ((algebraMap (Polynomial k) (Bring Ω) p : Bring Ω) : Ω)
      = algebraMap (Polynomial k) Ω p from
    (IsScalarTower.algebraMap_apply (Polynomial k) (Bring Ω) Ω p).symm]
  exact ψ.compat p

/-- The place of the cover cut out by a Puiseux embedding. -/
def place : Ideal (Bring Ω) :=
  Ideal.comap ψ.psHom (Ideal.span {(PowerSeries.X : PowerSeries K)})

theorem place_isPrime : (ψ.place).IsPrime := by
  haveI : (Ideal.span {(PowerSeries.X : PowerSeries K)}).IsPrime :=
    (Ideal.span_singleton_prime PowerSeries.X_ne_zero).mpr PowerSeries.X_prime
  exact Ideal.comap_isPrime _ _

theorem place_liesOver : (ψ.place).LiesOver (placeP s) :=
  ⟨by
    rw [Ideal.under, place, Ideal.comap_comap,
      show ψ.psHom.comp (algebraMap (Polynomial k) (Bring Ω)) = kummerSubst K s e from
        RingHom.ext ψ.psHom_algebraMap]
    exact (comap_kummerSubst K ψ.index_pos s).symm⟩

theorem place_isMaximal : (ψ.place).IsMaximal := by
  haveI := ψ.place_isPrime
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Polynomial k) _ ?_
  rw [show Ideal.comap (algebraMap (Polynomial k) (Bring Ω)) ψ.place = placeP s from
    (ψ.place_liesOver).over.symm]
  infer_instance

/-! ### The ramification bound -/

/-- The image of the uniformiser of the line has order exactly `e`. -/
theorem psHom_uniformiser :
    ψ.psHom (algebraMap (Polynomial k) (Bring Ω) (Polynomial.X - Polynomial.C s))
      = PowerSeries.X ^ e := by
  rw [ψ.psHom_algebraMap, kummerSubst_X_sub_C]

/-- **A Puiseux embedding of index `e` bounds the ramification at the place it cuts out.** -/
theorem ramificationIdx_place_le :
    Ideal.ramificationIdx (algebraMap (Polynomial k) (Bring Ω)) (placeP s) ψ.place ≤ e := by
  refine csSup_le ⟨0, by simp⟩ ?_
  rintro n hn
  by_contra hlt
  push_neg at hlt
  have hmem : algebraMap (Polynomial k) (Bring Ω) (Polynomial.X - Polynomial.C s)
      ∈ ψ.place ^ n :=
    hn (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))
  have hmap : Ideal.map ψ.psHom (ψ.place ^ n)
      ≤ Ideal.span {(PowerSeries.X : PowerSeries K)} ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_comap_le) n
  have h2 : PowerSeries.X ^ e ∈ Ideal.span {(PowerSeries.X : PowerSeries K)} ^ n := by
    rw [← ψ.psHom_uniformiser]
    exact hmap (Ideal.mem_map_of_mem _ hmem)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at h2
  have := h2 e hlt
  rw [PowerSeries.coeff_X_pow_self] at this
  exact one_ne_zero this

section Galois

variable [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω]

include ψ in
/-- **A Puiseux embedding of index `e` bounds the ramification above the point.** -/
theorem ramificationIdxIn_le : Ideal.ramificationIdxIn (placeP s) (Bring Ω) ≤ e := by
  haveI := ψ.place_isMaximal
  haveI := ψ.place_isPrime
  haveI := ψ.place_liesOver
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (placeP s) ψ.place (Ω ≃ₐ[RatFunc k] Ω)]
  exact ψ.ramificationIdx_place_le

include ψ in
/-- **The inertia group at any place above the point has order at most `e`.** -/
theorem card_inertia_le (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP s)] :
    Nat.card (geomInertia Ω Q) ≤ e := by
  haveI := residue_isSeparable Ω s Q
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Ω ≃ₐ[RatFunc k] Ω) _ (placeP_ne_bot s)]
  exact ψ.ramificationIdxIn_le

include ψ in
/-- **The order of an inertia element above the point is at most `e`.** -/
theorem orderOf_le_of_mem_inertia (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP s)]
    {g : Ω ≃ₐ[RatFunc k] Ω} (hg : g ∈ geomInertia Ω Q) : orderOf g ≤ e := by
  have h2 : Ideal.ramificationIdxIn (placeP s) (Bring Ω) ≠ 0 :=
    Ideal.ramificationIdxIn_ne_zero (G := Ω ≃ₐ[RatFunc k] Ω) (placeP_ne_bot s)
  exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero h2)
    (geom_orderOf_dvd_ramificationIdxIn Ω s Q hg)) ψ.ramificationIdxIn_le

/-- **A Puiseux embedding of index one at a point kills the inertia there.** -/
theorem eq_one_of_mem_inertia (ψ : PuiseuxEmbedding Ω K s 1) (Q : Ideal (Bring Ω)) [Q.IsMaximal]
    [Q.LiesOver (placeP s)] {g : Ω ≃ₐ[RatFunc k] Ω} (hg : g ∈ geomInertia Ω Q) : g = 1 := by
  have h := ψ.orderOf_le_of_mem_inertia Q hg
  have hpos : 0 < orderOf g := orderOf_pos_iff.mpr (isOfFinOrder_of_finite g)
  exact orderOf_eq_one_iff.mp (le_antisymm h hpos)

include ψ in
/-- **The inertia group at a place above the point is generated by any inertia element there whose
order is at least the index of the embedding.**

The inertia group has order at most `e` by the ramification bound, and it contains the cyclic group
generated by the element, which already has order at least `e`; so the two coincide.  This is the
form in which a local analytic monodromy generator becomes a distinguished algebraic inertia
element. -/
theorem geomInertia_eq_zpowers (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP s)]
    {g : Ω ≃ₐ[RatFunc k] Ω} (hg : g ∈ geomInertia Ω Q) (he : e ≤ orderOf g) :
    geomInertia Ω Q = Subgroup.zpowers g := by
  refine (SetLike.coe_injective (Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _))).symm
  · exact SetLike.coe_subset_coe.mpr (Subgroup.zpowers_le.mpr hg)
  · have h : Nat.card (geomInertia Ω Q) ≤ Nat.card (Subgroup.zpowers g) := by
      rw [Nat.card_zpowers]
      exact le_trans (ψ.card_inertia_le Q) he
    exact h

end Galois

end PuiseuxEmbedding

end Embedding

/-! ### Covers of the line -/

namespace LineCover

variable (L : LineCover) {K : Type} [Field K] [Algebra k K] {s : k}

/-- **A Puiseux embedding of index `e` at a point bounds the order of the inertia there.** -/
theorem orderOf_le_of_isInertiaAt {e : ℕ} (ψ : PuiseuxEmbedding L.M K s e) {σ : L.deck}
    (hσ : L.IsInertiaAt s σ) : orderOf σ ≤ e := by
  obtain ⟨Q, hQmax, hQover, hσQ⟩ := hσ
  haveI := hQmax
  haveI := hQover
  exact ψ.orderOf_le_of_mem_inertia Q hσQ

/-- **A Puiseux embedding of index one at a point kills the inertia there**: a single-valued
solution of the equation of the cover at `s`, expanded as a power series, proves that the cover is
unramified over `s`. -/
theorem eq_one_of_isInertiaAt (ψ : PuiseuxEmbedding L.M K s 1) {σ : L.deck}
    (hσ : L.IsInertiaAt s σ) : σ = 1 := by
  have h := L.orderOf_le_of_isInertiaAt ψ hσ
  have hpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  exact orderOf_eq_one_iff.mp (le_antisymm h hpos)

/-- **A local Puiseux parametrisation of index `e` makes an inertia element of order at least `e` a
distinguished inertia element**: it generates the whole inertia group of the place it lies in. -/
theorem isInertiaGenAt_of_puiseux {e : ℕ} (ψ : PuiseuxEmbedding L.M K s e) {σ : L.deck}
    (hσ : L.IsInertiaAt s σ) (he : e ≤ orderOf σ) : L.IsInertiaGenAt s σ := by
  obtain ⟨Q, hQmax, hQover, hσQ⟩ := hσ
  haveI := hQmax
  haveI := hQover
  exact ⟨Q, hQmax, hQover, ψ.geomInertia_eq_zpowers Q hσQ he⟩

/-- **A cover with a power series solution at every point outside `S` is unramified outside
`S`.** -/
theorem isUnramifiedOutside_of_puiseux (S : Set k)
    (h : ∀ t ∉ S, Nonempty (PuiseuxEmbedding L.M K t 1)) : L.IsUnramifiedOutside S :=
  fun t ht _ hσ => L.eq_one_of_isInertiaAt (h t ht).some hσ

end LineCover

end Rigidity.RET

end

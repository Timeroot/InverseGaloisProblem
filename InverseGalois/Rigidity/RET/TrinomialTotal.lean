/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.TrinomialCycle
import InverseGalois.Rigidity.RET.MorseSymmetric
import InverseGalois.Rigidity.RET.GeomFundamental
import InverseGalois.Rigidity.RET.Genus.Fundamental

/-!
# A totally ramified place carries a full cycle

The trinomial family has a single point of the cover above the origin, and the whole degree of the
cover is concentrated there.  Two counts meet: the order of vanishing of the coordinate at a place
of the cover is the winding number of the cover at that place, and the winding number is the order
of the inertia group; on the other hand the equation forces the order of vanishing of the
coordinate to be a multiple of the degree.  Since the inertia group also embeds in the group of
`(m+1)`-st roots of unity, the two bounds close on each other and the inertia group has exactly the
degree of the cover for its order.

An inertia group of that size acting freely on that many roots acts simply transitively, so a
generator moves the roots in a single cycle: the branch cycle of the family at the origin is a full
cycle.

## Main results

* `Rigidity.RET.card_geomInertia_eq_intOrd_baseX` — the order of the inertia group at a place over
  the origin is the order of vanishing of the coordinate there.
* `Rigidity.RET.card_geomInertia_eq_succ` — for the trinomial family the inertia group at a place
  over the origin has order `m + 1`.
* `Rigidity.RET.exists_isCycle_of_geomInertia` — a generator of that inertia group permutes the
  roots in a single `(m+1)`-cycle.
* `Rigidity.RET.exists_isInertiaAt_orderOf_ramTrinomialCover` — the cover defined by the family has
  a branch cycle of order `m + 1` at the origin.
-/

open Polynomial IsDedekindDomain Pointwise

noncomputable section

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB
attribute [local instance] Rigidity.RET.instSMulCommDeck

/-! ### The order of the inertia group is the winding number -/

/-- **The coordinate vanishes at a place over the origin to the order of ramification there.**
Both count the exponent of the place in the factorization of the ideal the coordinate spans. -/
theorem intOrd_baseX_eq_ramificationIdx (L : LineCover) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP (0 : k))] :
    intOrd L.M (coverPlace L 0 Q) (baseX L)
      = (Ideal.ramificationIdx (algebraMap (Polynomial k) (Bring L.M)) (placeP 0) Q : ℤ) := by
  have hspan : Ideal.span {(Polynomial.X : Polynomial k)} = placeP (0 : k) := by
    show Ideal.span {(Polynomial.X : Polynomial k)}
      = Ideal.span {(Polynomial.X - Polynomial.C (0 : k))}
    rw [map_zero, sub_zero]
  have hmap0 : Ideal.map (algebraMap (Polynomial k) (Bring L.M)) (placeP (0 : k)) ≠ ⊥ := by
    intro h
    have hmem : baseX L ∈ Ideal.map (algebraMap (Polynomial k) (Bring L.M)) (placeP (0 : k)) := by
      rw [← hspan]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
    rw [h, Ideal.mem_bot] at hmem
    exact baseX_ne_zero L hmem
  have hkey := ord_algebraMap_eq_ramificationIdx (R := Polynomial k) (B := Bring L.M) L.M
    (placeP (0 : k)) (coverPlace L 0 Q) hspan hmap0
  rw [coverPlace_asIdeal] at hkey
  have hbx : algebraMap (Bring L.M) L.M (baseX L) = algebraMap (Polynomial k) L.M Polynomial.X :=
    (IsScalarTower.algebraMap_apply (Polynomial k) (Bring L.M) L.M Polynomial.X).symm
  show ord L.M (coverPlace L 0 Q) (algebraMap (Bring L.M) L.M (baseX L)) = _
  rw [hbx]
  exact hkey

/-- **The order of the inertia group at a place over the origin is the order of vanishing of the
coordinate there.** -/
theorem card_geomInertia_eq_intOrd_baseX (L : LineCover) (Q : Ideal (Bring L.M)) [Q.IsMaximal]
    [Q.LiesOver (placeP (0 : k))] :
    (Nat.card (geomInertia L.M Q) : ℤ) = intOrd L.M (coverPlace L 0 Q) (baseX L) := by
  rw [intOrd_baseX_eq_ramificationIdx L Q, card_geomInertia_eq_ramificationIdx L 0 Q]

/-! ### The inertia group of the trinomial family at the origin -/

variable {m : ℕ} {c : k}

/-- **The trinomial family is totally ramified over the origin.**  The order of the inertia group
is the order of vanishing of the coordinate, which the equation makes a multiple of `m + 1`; and
the inertia group embeds in the group of `(m+1)`-st roots of unity, so its order divides `m + 1`
as well. -/
theorem card_geomInertia_eq_succ (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly (ramTrinomial m c))]
    (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP (0 : k))]
    {y₀ : Bring L.M} (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    Nat.card (geomInertia L.M Q) = m + 1 := by
  have hdvd₁ : Nat.card (geomInertia L.M Q) ∣ m + 1 := card_geomInertia_dvd L hm hc Q hy₀
  have hdvd₂ : ((m : ℤ) + 1) ∣ (Nat.card (geomInertia L.M Q) : ℤ) := by
    rw [card_geomInertia_eq_intOrd_baseX L Q]
    exact succ_dvd_intOrd_baseX L hm (intOrd_baseX_pos L Q) hy₀
  refine Nat.dvd_antisymm hdvd₁ ?_
  have hcast : ((m + 1 : ℕ) : ℤ) ∣ (Nat.card (geomInertia L.M Q) : ℤ) := by
    push_cast
    exact hdvd₂
  exact_mod_cast hcast

/-! ### The branch cycle at the origin is a full cycle -/

/-- **The inertia group at a place over the origin acts freely on the roots**: two of its elements
agreeing at one root agree everywhere. -/
theorem geomInertia_smul_root_injective (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly (ramTrinomial m c))]
    (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP (0 : k))]
    {y₀ : Bring L.M} (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    Function.Injective fun σ : geomInertia L.M Q => (σ : L.deck) • y₀ := by
  intro a b hab
  have hab' : (a : L.deck) • y₀ = (b : L.deck) • y₀ := hab
  have hfix : ((a : L.deck)⁻¹ * (b : L.deck)) • y₀ = y₀ := by
    rw [mul_smul, ← hab', ← mul_smul, inv_mul_cancel, one_smul]
  have hmem : ((a : L.deck)⁻¹ * (b : L.deck)) ∈ geomInertia L.M Q :=
    mul_mem (inv_mem a.2) b.2
  exact Subtype.ext (inv_mul_eq_one.mp
    (eq_one_of_mem_geomInertia_of_fixes_root L hm hc Q hmem hy₀ hfix))

/-- **The number of roots of the trinomial family in the integral model is its degree.** -/
theorem card_rootSet_ramTrinomial (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly (ramTrinomial m c))] :
    Nat.card ((ramTrinomial m c).rootSet (Bring L.M)) = m + 1 := by
  rw [Nat.card_coe_set_eq, ncard_rootSet_bring L (ramTrinomial m c) (ramTrinomial_monic hm c)
    (genericPoly_ramTrinomial_separable hm hc), ramTrinomial_natDegree hm]

/-- **The inertia group at a place over the origin acts simply transitively on the roots.** -/
theorem geomInertia_smul_root_bijective (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly (ramTrinomial m c))]
    (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP (0 : k))]
    {y₀ : Bring L.M} (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    Function.Bijective fun σ : geomInertia L.M Q =>
      (⟨(σ : L.deck) • y₀, Polynomial.smul_mem_rootSet (σ : L.deck) hy₀⟩ :
        (ramTrinomial m c).rootSet (Bring L.M)) := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨fun a b hab => geomInertia_smul_root_injective L hm hc Q hy₀
    (congrArg Subtype.val hab), ?_⟩
  rw [card_geomInertia_eq_succ L hm hc Q hy₀, card_rootSet_ramTrinomial L hm hc]

/-- **The branch cycle of the trinomial family at the origin is a full cycle.**  The inertia group
at a place over the origin is cyclic of order `m + 1` and acts simply transitively on the `m + 1`
roots, so a generator carries each root to the next in a single cycle. -/
theorem exists_isCycle_of_geomInertia (L : LineCover) (hm : 1 ≤ m) (hc : c ≠ 0)
    [Polynomial.IsSplittingField (RatFunc k) L.M (genericPoly (ramTrinomial m c))]
    (Q : Ideal (Bring L.M)) [Q.IsMaximal] [Q.LiesOver (placeP (0 : k))]
    {y₀ : Bring L.M} (hy₀ : y₀ ∈ (ramTrinomial m c).rootSet (Bring L.M)) :
    ∃ σ : L.deck, σ ∈ geomInertia L.M Q ∧ orderOf σ = m + 1 ∧
      (MulAction.toPermHom L.deck ((ramTrinomial m c).rootSet (Bring L.M)) σ).IsCycle := by
  classical
  haveI : IsCyclic (geomInertia L.M Q) := isCyclic_geomInertia L.M 0 Q
  have hcard : Nat.card (geomInertia L.M Q) = m + 1 := card_geomInertia_eq_succ L hm hc Q hy₀
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := geomInertia L.M Q)
  have hord : orderOf (g : L.deck) = m + 1 := by
    rw [Subgroup.orderOf_coe, ← Nat.card_zpowers g,
      (Subgroup.zpowers g).eq_top_iff'.mpr hg, Subgroup.card_top, hcard]
  refine ⟨(g : L.deck), g.2, hord, ?_⟩
  -- the orbit map is a bijection, so every root is reached by a power of the generator
  have hbij := geomInertia_smul_root_bijective L hm hc Q hy₀
  refine ⟨⟨y₀, hy₀⟩, ?_, ?_⟩
  · -- the generator moves the base root: otherwise it would be trivial
    intro hfixed
    have hfix : (g : L.deck) • y₀ = y₀ := congrArg Subtype.val hfixed
    have hone : (g : L.deck) = 1 :=
      eq_one_of_mem_geomInertia_of_fixes_root L hm hc Q g.2 hy₀ hfix
    rw [hone, orderOf_one] at hord
    omega
  · intro y _
    obtain ⟨τ, hτ⟩ := hbij.2 y
    obtain ⟨j, hj⟩ := hg τ
    refine ⟨j, ?_⟩
    rw [← hτ, ← hj]
    have hzpow : (MulAction.toPermHom L.deck ((ramTrinomial m c).rootSet (Bring L.M))
        (g : L.deck)) ^ j
        = MulAction.toPermHom L.deck ((ramTrinomial m c).rootSet (Bring L.M))
            ((g : L.deck) ^ j) := (map_zpow _ _ _).symm
    rw [hzpow]
    refine Subtype.ext ?_
    show ((g : L.deck) ^ j) • y₀ = (((g ^ j : geomInertia L.M Q) : L.deck)) • y₀
    rw [SubgroupClass.coe_zpow]

/-! ### The cover defined by the trinomial family -/

/-- **The cover defined by the trinomial family is totally ramified over the origin.**  There is a
place of the cover above the origin whose inertia group is generated by an element permuting the
roots of the family in a single `(m+1)`-cycle. -/
theorem exists_isCycle_ramTrinomialCover (hm : 1 ≤ m) (hc : c ≠ 0) :
    ∃ Q : Ideal (Bring (ramTrinomialCover hm hc).M), ∃ _ : Q.IsMaximal,
      ∃ _ : Q.LiesOver (placeP (0 : k)), ∃ σ : (ramTrinomialCover hm hc).deck,
        σ ∈ geomInertia (ramTrinomialCover hm hc).M Q ∧ orderOf σ = m + 1 ∧
          (MulAction.toPermHom (ramTrinomialCover hm hc).deck
            ((ramTrinomial m c).rootSet (Bring (ramTrinomialCover hm hc).M)) σ).IsCycle := by
  haveI := ramTrinomialCover_isSplittingField hm hc
  set L := ramTrinomialCover hm hc with hL
  obtain ⟨Q, hQmax, hQover⟩ := exists_Q_over_placeP L.M (0 : k)
  haveI := hQmax
  haveI := hQover
  have hpos : 0 < Nat.card ((ramTrinomial m c).rootSet (Bring L.M)) := by
    rw [card_rootSet_ramTrinomial L hm hc]
    omega
  obtain ⟨⟨y₀, hy₀⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  obtain ⟨σ, hσ, hord, hcyc⟩ := exists_isCycle_of_geomInertia L hm hc Q hy₀
  exact ⟨Q, hQmax, hQover, σ, hσ, hord, hcyc⟩

/-- **The trinomial cover has an inertia element of order exactly `m + 1` at the origin**: the
origin is a branch point of the cover, and the branch cycle there has the full degree of the
family for its order. -/
theorem exists_isInertiaAt_orderOf_ramTrinomialCover (hm : 1 ≤ m) (hc : c ≠ 0) :
    ∃ σ : (ramTrinomialCover hm hc).deck,
      (ramTrinomialCover hm hc).IsInertiaAt 0 σ ∧ orderOf σ = m + 1 := by
  obtain ⟨Q, hQmax, hQover, σ, hσ, hord, -⟩ := exists_isCycle_ramTrinomialCover hm hc
  exact ⟨σ, ⟨Q, hQmax, hQover, hσ⟩, hord⟩

end Rigidity.RET

end

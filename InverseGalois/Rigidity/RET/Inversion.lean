/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.GeomRET
import InverseGalois.Rigidity.RET.MoveInfinity
import InverseGalois.Rigidity.RET.TranslateInfinity

/-!
# The branch-cycle correspondence in the inverted coordinate

Inverting the parameter, `T ↦ T⁻¹`, is the one coordinate change of the line which is not affine
and still fixes the two ends of the line as a pair; together with the affine changes it generates
every coordinate change of the projective line.  Unlike an affine change it does not preserve the
polynomial ring, so a distinguished inertia generator cannot be carried along by the ring-level
machinery of a semilinear isomorphism.  It is carried along by the *places* instead: a place of
the field at which `T` takes a non-zero value `t` is a place at which `T⁻¹` takes the value `t⁻¹`,
and the inertia group of a place does not know which coordinate was used to address it.

The file therefore first restates the notion of a distinguished inertia generator in terms of
places of the field alone (`Rigidity.RET.LineCover.IsInertiaGenAtPlace`), proves that this restated
form agrees with the ring-theoretic one, and then reads off the inversion.

## Main definitions

* `Rigidity.RET.LineCover.IsInertiaGenAtPlace` — a distinguished inertia generator, described by a
  place of the field rather than by a prime of the integral model.

## Main results

* `Rigidity.RET.LineCover.isInertiaGenAtPlace_iff` — the two descriptions agree.
* `Rigidity.RET.LineCover.isInertiaGenAt_twist_inv` — inverting the coordinate exchanges the
  distinguished inertia generators at `t` and at `t⁻¹`.
* `Rigidity.RET.GeomRET.twist_inv` — the branch-cycle correspondence travels along the inversion
  of the parameter.
-/

open Polynomial IsDedekindDomain

noncomputable section

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

/-! ## A reciprocal computation with a place -/

/-- **Taking reciprocals preserves the relation of taking a given non-zero value at a place.**  If
a function differs from a unit of the place by something vanishing there, so do their
reciprocals. -/
theorem valuation_inv_sub_inv_lt_one {F : Type*} [Field F] (A : ValuationSubring F) {x c : F}
    (hc0 : c ≠ 0) (hcA : c ∈ A) (hcA' : c⁻¹ ∈ A) (h : A.valuation (x - c) < 1) :
    A.valuation (x⁻¹ - c⁻¹) < 1 := by
  have hcval : A.valuation c = 1 :=
    valuation_eq_one_of_le A hc0 (A.valuation_le_one ⟨c, hcA⟩) (A.valuation_le_one ⟨c⁻¹, hcA'⟩)
  have hxval : A.valuation x = 1 := by
    have hlt : A.valuation (x - c) < A.valuation c := by rw [hcval]; exact h
    have heq := valuation_add_eq_of_lt A hlt
    have hcx : c + (x - c) = x := by ring
    rw [hcx, hcval] at heq
    exact heq
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, map_zero] at hxval
    exact zero_ne_one hxval
  have hid : (x⁻¹ - c⁻¹) * (x * c) = c - x := by
    have h1 : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0
    have h2 : c⁻¹ * c = 1 := inv_mul_cancel₀ hc0
    calc (x⁻¹ - c⁻¹) * (x * c) = x⁻¹ * x * c - c⁻¹ * c * x := by ring
      _ = c - x := by rw [h1, h2, one_mul, one_mul]
  have hval := congrArg A.valuation hid
  rw [map_mul, map_mul, hxval, hcval, mul_one, mul_one] at hval
  rw [hval, A.valuation.map_sub_swap]
  exact h

namespace LineCover

attribute [local instance] LineCover.instAlgebraConst LineCover.instTowerConstRatFunc
  LineCover.instTowerConstPoly

/-! ## A place of the field cut out by a value of the coordinate -/

/-- **A place of the field at which the constants are regular and the coordinate takes the value
`t` is the place of a maximal ideal of the integral model lying over `t`.**  Such a place contains
the whole first chart, hence comes from a prime of the integral model, and that prime contains the
coordinate shifted to vanish at `t`. -/
theorem exists_place_of_valuation (L : LineCover) (t : k) (A : ValuationSubring L.M) (hA : A ≠ ⊤)
    (hc : ∀ c : k, algebraMap (Polynomial k) L.M (C c) ∈ A)
    (hXt : A.valuation (algebraMap (Polynomial k) L.M (X - C t)) < 1) :
    ∃ v : HeightOneSpectrum (Bring L.M), placeSubring L.M v = A ∧ v.asIdeal.IsMaximal ∧
      v.asIdeal.LiesOver (placeP t) := by
  have hXtA : algebraMap (Polynomial k) L.M (X - C t) ∈ A :=
    A.mem_of_valuation_le_one _ (le_of_lt hXt)
  have hXA : algebraMap (Polynomial k) L.M X ∈ A := by
    have hsum : algebraMap (Polynomial k) L.M (X - C t) + algebraMap (Polynomial k) L.M (C t) ∈ A :=
      add_mem hXtA (hc t)
    rwa [map_sub, sub_add_cancel] at hsum
  have hpoly : ∀ p : Polynomial k, algebraMap (Polynomial k) L.M p ∈ A :=
    algebraMap_polynomial_mem_of_C A hc hXA
  have hB : ∀ b : Bring L.M, algebraMap (Bring L.M) L.M b ∈ A := fun b =>
    mem_of_isIntegral_algebraMap (R := Polynomial k) hpoly b.2
  set v := underPlace A hB hA with hv
  have hpl : placeSubring L.M v = A := placeSubring_underPlace A hB hA
  have hmem : algebraMap (Polynomial k) (Bring L.M) (X - C t) ∈ v.asIdeal := by
    rw [← valuation_lt_one_iff_mem (F := L.M) v, hpl, ← IsScalarTower.algebraMap_apply]
    exact hXt
  refine ⟨v, hpl, v.isPrime.isMaximal v.ne_bot, ⟨?_⟩⟩
  have hle : placeP t ≤ (v.asIdeal).under (Polynomial k) := by
    rw [placeP, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  have hne : (v.asIdeal).under (Polynomial k) ≠ ⊤ := by
    haveI : (v.asIdeal).IsPrime := v.isPrime
    haveI : (Ideal.comap (algebraMap (Polynomial k) (Bring L.M)) v.asIdeal).IsPrime :=
      Ideal.comap_isPrime _ _
    exact Ideal.IsPrime.ne_top this
  exact (placeP_max t).eq_of_le hne hle

/-! ## Distinguished inertia generators, read at a place -/

/-- **A distinguished inertia generator, described by a place of the field.**  There is a place at
which the constants are regular and the coordinate takes the value `t`, and the symmetries which
act trivially on the residue field of that place are exactly the powers of `σ`.

Nothing in this description mentions the integral model, so it is insensitive to a change of
coordinate on the line. -/
def IsInertiaGenAtPlace (L : LineCover) (t : k) (σ : L.deck) : Prop :=
  ∃ A : ValuationSubring L.M, A ≠ ⊤ ∧ (∀ c : k, algebraMap (Polynomial k) L.M (C c) ∈ A) ∧
    A.valuation (algebraMap (Polynomial k) L.M (X - C t)) < 1 ∧
    ∀ τ : L.deck, ((∀ y ∈ A, A.valuation (τ y - y) < 1) ↔ τ ∈ Subgroup.zpowers σ)

variable {L : LineCover} {t : k} {σ : L.deck}

/-- **The two descriptions of a distinguished inertia generator agree.**  A prime of the integral
model over the point has a place, and a place at which the coordinate takes the value at the point
has a prime; inertia is read the same way on either side. -/
theorem isInertiaGenAtPlace_iff : L.IsInertiaGenAtPlace t σ ↔ L.IsInertiaGenAt t σ := by
  have hcomm : ∀ (ρ : L.deck) (b : Bring L.M),
      algebraMap (Bring L.M) L.M (ρ • b) = ρ • algebraMap (Bring L.M) L.M b :=
    fun ρ b => coe_smul_geom L.M ρ b
  constructor
  · rintro ⟨A, hAtop, hc, hXt, hin⟩
    obtain ⟨v, hpl, hmax, hover⟩ := exists_place_of_valuation L t A hAtop hc hXt
    refine ⟨v.asIdeal, hmax, hover, ?_⟩
    ext τ
    rw [mem_inertia_iff_isInertialAtPlace (F := L.M) (B := Bring L.M) hcomm v τ, hpl]
    exact hin τ
  · rintro ⟨Q, hQmax, hQover, hI⟩
    haveI := hQmax
    haveI := hQover
    have hQbot : Q ≠ ⊥ := Q_ne_bot L.M t Q
    set v : HeightOneSpectrum (Bring L.M) := ⟨Q, hQmax.isPrime, hQbot⟩ with hv
    refine ⟨placeSubring L.M v, placeSubring_ne_top _ v,
      fun c => algebraMap_poly_mem_placeSubring L v _, ?_, ?_⟩
    · refine valuation_algebraMap_poly_lt_one L v ?_
      have hle : (X - C t : Polynomial k) ∈ placeP t := Ideal.mem_span_singleton_self _
      have hunder : placeP t = Q.under (Polynomial k) := hQover.over
      rw [hunder] at hle
      exact hle
    · intro τ
      rw [← hI]
      exact (mem_inertia_iff_isInertialAtPlace (F := L.M) (B := Bring L.M) hcomm v τ).symm

/-! ## The coordinate of the inversion twist -/

variable (L) in
/-- The coordinate of the inversion twist is the reciprocal of the coordinate. -/
theorem twist_inv_algebraMap_X :
    algebraMap (Polynomial k) (L.twist invSubst.toRingEquiv).M X
      = (algebraMap (Polynomial k) L.M X)⁻¹ := by
  have hX : algebraMap (Polynomial k) L.M X
      = algebraMap (RatFunc k) L.M (RatFunc.X : RatFunc k) := by
    rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) L.M, RatFunc.algebraMap_X]
  rw [twist_algebraMap_X, hX, ← map_inv₀]

variable (L) in
/-- The constants of the inversion twist are the constants. -/
theorem twist_inv_algebraMap_C (c : k) :
    algebraMap (Polynomial k) (L.twist invSubst.toRingEquiv).M (C c)
      = algebraMap (Polynomial k) L.M (C c) := by
  rw [twist_algebraMap_C, Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]

variable (L) in
/-- The coordinate of the inversion twist, shifted to vanish at `t`, is the reciprocal of the
coordinate shifted to vanish at `t⁻¹`. -/
theorem twist_inv_algebraMap_X_sub_C {t : k} :
    algebraMap (Polynomial k) (L.twist invSubst.toRingEquiv).M (X - C t)
      = (algebraMap (Polynomial k) L.M X)⁻¹ - (algebraMap (Polynomial k) L.M (C t⁻¹))⁻¹ := by
  have hCt : algebraMap (Polynomial k) L.M (C t) = (algebraMap (Polynomial k) L.M (C t⁻¹))⁻¹ := by
    rw [Polynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, ← map_inv₀, inv_inv]
  rw [map_sub, twist_inv_algebraMap_X, twist_inv_algebraMap_C, hCt]

/-! ## Inverting the coordinate -/

variable (L) in
/-- **The deck group of a twist of a cover is the deck group of the cover**, packaged so that both
covers are named: linearity over the base for one action of the base is linearity for the other. -/
def twistDeckEquiv (φ : RatFunc k ≃+* RatFunc k) : L.deck ≃* (L.twist φ).deck where
  toFun := L.twistAut φ
  invFun τ := Twist.unaut τ
  left_inv _ := AlgEquiv.ext fun _ => rfl
  right_inv _ := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp] theorem twistDeckEquiv_apply (L : LineCover) (φ : RatFunc k ≃+* RatFunc k) (σ : L.deck)
    (x : L.M) : (L.twistDeckEquiv φ σ) x = σ x := rfl

@[simp] theorem twistDeckEquiv_symm_apply (L : LineCover) (φ : RatFunc k ≃+* RatFunc k)
    (τ : (L.twist φ).deck) (x : L.M) : ((L.twistDeckEquiv φ).symm τ) x = τ x := rfl

/-- **Inverting the coordinate exchanges the places at `t` and at `t⁻¹`, together with their
inertia.**  A place at which the coordinate takes the non-zero value `t` is a place at which the
inverse coordinate takes the value `t⁻¹`, and the two covers have the same field, the same
symmetries and the same places. -/
theorem isInertiaGenAtPlace_twist_inv (L : LineCover) {t : k} (ht : t ≠ 0) (σ : L.deck) :
    (L.twist invSubst.toRingEquiv).IsInertiaGenAtPlace t⁻¹
        (L.twistDeckEquiv invSubst.toRingEquiv σ)
      ↔ L.IsInertiaGenAtPlace t σ := by
  set E := L.twistDeckEquiv invSubst.toRingEquiv with hE
  -- the powers of `σ` and the powers of its avatar on the twist correspond
  have hz : ∀ τ : L.deck, (E τ ∈ Subgroup.zpowers (E σ)) ↔ τ ∈ Subgroup.zpowers σ := by
    intro τ
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, E.injective ?_⟩
      rw [map_zpow]
      exact hn
    · rintro ⟨n, rfl⟩
      exact ⟨n, (map_zpow _ _ _).symm⟩
  constructor
  · rintro ⟨A, hAtop, hc, hXt, hin⟩
    have hc' : ∀ c : k, algebraMap (Polynomial k) L.M (C c) ∈ A := by
      intro c
      have h := hc c
      rwa [twist_inv_algebraMap_C L c] at h
    refine ⟨A, hAtop, hc', ?_, ?_⟩
    · -- read the value of the coordinate back from the value of its reciprocal
      rw [twist_inv_algebraMap_X_sub_C L (t := t⁻¹), inv_inv] at hXt
      have hc0 : algebraMap (Polynomial k) L.M (C t) ≠ 0 := by
        rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
        exact fun h => ht ((algebraMap k L.M).injective (by rw [h, map_zero]))
      have hinv : (algebraMap (Polynomial k) L.M (C t))⁻¹
          = algebraMap (Polynomial k) L.M (C t⁻¹) := by
        rw [Polynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap,
          ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← map_inv₀]
      have hkey := valuation_inv_sub_inv_lt_one A (x := (algebraMap (Polynomial k) L.M X)⁻¹)
        (c := (algebraMap (Polynomial k) L.M (C t))⁻¹) (inv_ne_zero hc0)
        (by rw [hinv]; exact hc' t⁻¹) (by rw [inv_inv]; exact hc' t) hXt
      rw [inv_inv, inv_inv] at hkey
      rw [map_sub]
      exact hkey
    · intro τ
      exact (hin (E τ)).trans (hz τ)
  · rintro ⟨A, hAtop, hc, hXt, hin⟩
    have hc' : ∀ c : k, algebraMap (Polynomial k) (L.twist invSubst.toRingEquiv).M (C c) ∈ A := by
      intro c
      rw [twist_inv_algebraMap_C L c]
      exact hc c
    refine ⟨A, hAtop, hc', ?_, ?_⟩
    · have hc0 : algebraMap (Polynomial k) L.M (C t) ≠ 0 := by
        rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
        exact fun h => ht ((algebraMap k L.M).injective (by rw [h, map_zero]))
      have hinv : (algebraMap (Polynomial k) L.M (C t))⁻¹
          = algebraMap (Polynomial k) L.M (C t⁻¹) := by
        rw [Polynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap,
          ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← map_inv₀]
      rw [map_sub] at hXt
      have hkey := valuation_inv_sub_inv_lt_one A hc0 (hc t) (by rw [hinv]; exact hc t⁻¹) hXt
      rw [twist_inv_algebraMap_X_sub_C L (t := t⁻¹), inv_inv]
      exact hkey
    · intro τ'
      obtain ⟨τ, rfl⟩ := E.surjective τ'
      exact (hin τ).trans (hz τ).symm

/-- **Inverting the coordinate exchanges the distinguished inertia generators at `t` and at
`t⁻¹`.** -/
theorem isInertiaGenAt_twist_inv (L : LineCover) {t : k} (ht : t ≠ 0) (σ : L.deck) :
    (L.twist invSubst.toRingEquiv).IsInertiaGenAt t⁻¹
        (L.twistDeckEquiv invSubst.toRingEquiv σ)
      ↔ L.IsInertiaGenAt t σ := by
  rw [← isInertiaGenAtPlace_iff, ← isInertiaGenAtPlace_iff]
  exact isInertiaGenAtPlace_twist_inv L ht σ

end LineCover

/-! ## The branch locus in the inverted coordinate -/

/-- The points whose reciprocal is one of finitely many non-zero points are the reciprocals of
those points. -/
theorem setOf_inv_mem_range {r : ℕ} {t : Fin r → k} (ht : ∀ i, t i ≠ 0) :
    {s : k | s ≠ 0 ∧ s⁻¹ ∈ Set.range t} = Set.range fun i => (t i)⁻¹ := by
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨hs, i, hi⟩
    exact ⟨i, by rw [hi, inv_inv]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨inv_ne_zero (ht i), i, (inv_inv (t i)).symm⟩

/-- A cover unramified outside a set of non-zero points is unramified at the origin. -/
theorem isUnramifiedOutside_compl_zero_of_range {L : LineCover} {r : ℕ} {t : Fin r → k}
    (ht : ∀ i, t i ≠ 0) (hout : L.IsUnramifiedOutside (Set.range t)) :
    L.IsUnramifiedOutside ({(0 : k)}ᶜ) := by
  intro s hs σ hσ
  have hs0 : s = 0 := by
    by_contra h
    exact hs h
  subst hs0
  refine hout 0 ?_ σ hσ
  rintro ⟨i, hi⟩
  exact ht i hi

/-- **A monodromy tuple travels along the inversion of the parameter.**  The reciprocal carries the
branch points along; the origin, which the inversion exchanges with the point at infinity, is a
branch point of neither cover. -/
theorem IsMonodromyOver.twist_inv {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    {t : Fin r → k} (ht : ∀ i, t i ≠ 0) (H : IsMonodromyOver h t) :
    IsMonodromyOver h fun i => (t i)⁻¹ := by
    obtain ⟨L, e, hout, hinf, hin⟩ := H
    refine ⟨L.twist invSubst.toRingEquiv,
      (L.twistDeckEquiv invSubst.toRingEquiv).symm.trans e, ?_, ?_, ?_⟩
    · have hu := LineCover.isUnramifiedOutside_twist_inv L hout hinf
      rwa [setOf_inv_mem_range ht] at hu
    · exact LineCover.isUnramifiedAtInfinity_twist_inv L (isUnramifiedOutside_compl_zero_of_range ht hout)
    · intro i
      exact (LineCover.isInertiaGenAt_twist_inv L (ht i) (e.symm (h i))).2 (hin i)

/-- **The existence direction travels along the inversion of the parameter.** -/
theorem GeomRETExistence.twist_inv {r : ℕ} {t : Fin r → k} (ht : ∀ i, t i ≠ 0)
    (H : GeomRETExistence t) : GeomRETExistence fun i => (t i)⁻¹ :=
  fun _ _ _ h hprod htop => (H h hprod htop).twist_inv ht

/-- **The completeness direction travels along the inversion of the parameter.** -/
theorem GeomRETCompleteness.twist_inv {r : ℕ} {t : Fin r → k} (ht : ∀ i, t i ≠ 0)
    (H : GeomRETCompleteness t) : GeomRETCompleteness fun i => (t i)⁻¹ := by
    intro L' hout' hinf'
    set E := L'.twistDeckEquiv invSubst.toRingEquiv with hE
    have hti : ∀ i, (t i)⁻¹ ≠ 0 := fun i => inv_ne_zero (ht i)
    -- read the cover in the inverted coordinate: it is branched over the original points
    have hout : (L'.twist invSubst.toRingEquiv).IsUnramifiedOutside (Set.range t) := by
      have hu := LineCover.isUnramifiedOutside_twist_inv L' hout' hinf'
      rw [setOf_inv_mem_range hti] at hu
      have hset : (Set.range fun i => ((t i)⁻¹)⁻¹) = Set.range t := by
        refine congrArg Set.range (funext fun i => ?_)
        rw [inv_inv]
      rwa [hset] at hu
    have hinf : (L'.twist invSubst.toRingEquiv).IsUnramifiedAtInfinity :=
      LineCover.isUnramifiedAtInfinity_twist_inv L' (isUnramifiedOutside_compl_zero_of_range hti hout')
    obtain ⟨g, hg⟩ := H _ hout hinf
    refine ⟨fun i => E.symm (g i), ?_, ?_, ?_⟩
    · intro i
      have hpt : ((t i)⁻¹)⁻¹ = t i := inv_inv (t i)
      have h := (LineCover.isInertiaGenAt_twist_inv L' (hti i) (E.symm (g i))).1
      rw [hpt, MulEquiv.apply_symm_apply] at h
      exact h (hg.inertia i)
    · have hrange : (Set.range fun i => E.symm (g i))
          = (E.symm : (L'.twist invSubst.toRingEquiv).deck →* L'.deck) '' Set.range g := by
        rw [← Set.range_comp]
        rfl
      rw [hrange, ← MonoidHom.map_closure, hg.top,
        Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)]
    · have hlist : (List.ofFn fun i => E.symm (g i))
          = (List.ofFn g).map (E.symm : (L'.twist invSubst.toRingEquiv).deck →* L'.deck) := by
        rw [List.map_ofFn]
        rfl
      rw [hlist, List.prod_hom, hg.prod, map_one]

/-- **The branch-cycle correspondence travels along the inversion of the parameter.** -/
theorem GeomRET.twist_inv {r : ℕ} {t : Fin r → k} (ht : ∀ i, t i ≠ 0) (H : GeomRET t) :
    GeomRET fun i => (t i)⁻¹ :=
  ⟨H.exists_cover.twist_inv ht, H.exists_cycles.twist_inv ht⟩

end Rigidity.RET

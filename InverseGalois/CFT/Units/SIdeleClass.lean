/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Isogeny
import InverseGalois.CFT.Units.LocalEmbedding
import InverseGalois.CFT.Units.SIdeleHerbrand

/-!
# The Herbrand quotient of the classes of the ideles that are units outside a finite set of places

An `S`-unit of a number field is a unit of the completion at every place outside `S`, so the field
sits diagonally inside the group of ideles that are units outside `S`, and the quotient by the
diagonal is the group of classes of such ideles.  This file constructs that diagonal, checks that it
commutes with the Galois action, and computes the Herbrand quotient of the quotient group.

The computation is the arithmetic heart of the first inequality.  Both the `S`-ideles and the
`S`-units have Herbrand quotient the same product of orders of decomposition groups, up to a factor
of the degree of the extension, and the Herbrand quotient is multiplicative along a short exact
sequence, so the two products cancel and the quotient group is left with the degree exactly.

Multiplicativity of the Herbrand quotient requires all six Tate groups involved to be finite, and
none of these groups is finitely generated.  Finiteness is instead read off from the computation
itself: the cardinality of an infinite group is recorded as zero, so a Herbrand quotient that is a
positive product of orders of decomposition groups already certifies that the two Tate groups
entering it are finite, and finiteness for the quotient group then follows from exactness.

## Main definitions

* `InverseGalois.CFT.SIdele`: **the ideles that are units outside the chosen places.**
* `InverseGalois.CFT.sIdeleDiag`: **the diagonal embedding of the `S`-units into the `S`-ideles.**
* `InverseGalois.CFT.sIdeleClassSES`: the short exact sequence of the `S`-units inside the
  `S`-ideles.

## Main results

* `InverseGalois.CFT.sIdeleAut_sIdeleDiag`: **the diagonal commutes with the Galois action.**
* `InverseGalois.CFT.sIdeleDiag_injective`: the diagonal is injective.
* `InverseGalois.CFT.herbrand_sIdeleClassSES`: **the classes of the ideles that are units outside
  the chosen places have Herbrand quotient the degree of the extension.**

## Tags

number field, idele class group, S-unit, Herbrand quotient, first inequality
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

/-! ### The diagonal -/

section Diag

variable {K : Type*} [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K)))
  [DecidablePred (· ∈ T)]

/-- The component at a finite place of the diagonal image of an `S`-unit.  Away from the chosen
places the order of an `S`-unit vanishes, so the local unit lies in the units of the valuation ring;
at a chosen place there is nothing to check. -/
noncomputable def sUnitAdicComponent (u : ↥(sUnits K T)) (v : HeightOneSpectrum (𝓞 K)) :
    ↥(adicSUnits T v) :=
  ⟨Additive.ofMul (adicUnitHom v (u : Kˣ)), by
    by_cases hv : v ∈ T
    · rw [adicSUnits_of_mem T hv]
      trivial
    · rw [adicSUnits_of_notMem T hv, AddMonoidHom.mem_ker, unitVal_adicUnitHom,
        u.2 v hv, neg_zero]⟩

@[simp]
theorem coe_sUnitAdicComponent (u : ↥(sUnits K T)) (v : HeightOneSpectrum (𝓞 K)) :
    ((sUnitAdicComponent T u v : ↥(adicSUnits T v)) : Additive (v.adicCompletion K)ˣ)
      = Additive.ofMul (adicUnitHom v (u : Kˣ)) := rfl

/-- **The ideles that are units outside a set of finite places**: an arbitrary unit of the
completion at every infinite place, and a unit of the valuation ring at every finite place other
than the chosen ones. -/
abbrev SIdele : Type _ :=
  (∀ w : InfinitePlace K, Additive w.Completionˣ) ×
    (∀ v : HeightOneSpectrum (𝓞 K), ↥(adicSUnits T v))

/-- **The diagonal embedding of the `S`-units into the `S`-ideles**, sending an `S`-unit to its
image in every completion at once. -/
noncomputable def sIdeleDiag : Additive ↥(sUnits K T) →+ SIdele T where
  toFun u := (fun w => Additive.ofMul (infiniteUnitHom w ((u.toMul : ↥(sUnits K T)) : Kˣ)),
    fun v => sUnitAdicComponent T u.toMul v)
  map_zero' := by
    refine Prod.ext (funext fun w => ?_) (funext fun v => ?_)
    · exact Additive.toMul.injective (Units.ext (by simp))
    · exact Subtype.ext (Additive.toMul.injective (Units.ext (by simp)))
  map_add' u u' := by
    refine Prod.ext (funext fun w => ?_) (funext fun v => ?_)
    · exact Additive.toMul.injective (Units.ext (by simp [Subgroup.coe_mul]))
    · exact Subtype.ext (Additive.toMul.injective (Units.ext (by simp [Subgroup.coe_mul])))

/-- The diagonal is injective, since a number field has an infinite place and embeds in the
completion there. -/
theorem sIdeleDiag_injective : Function.Injective (sIdeleDiag T) := by
  intro u u' h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have h1 := congrFun (congrArg Prod.fst h) w
  exact Additive.toMul.injective (Subtype.ext
    (infiniteUnitHom_injective w (Additive.toMul.injective h1)))

end Diag

/-! ### Equivariance of the diagonal -/

section Equiv

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K]
  {Y : Type*} [MulAction Gal(K/k) Y] {ι : Y → HeightOneSpectrum (𝓞 K)}
  (hι : ∀ (g : Gal(K/k)) (y : Y), ι (g • y) = g • ι y) [DecidablePred (· ∈ Set.range ι)]

include hι

omit [DecidablePred (· ∈ Set.range ι)] in
/-- At an infinite place, the transport isomorphism carries the diagonal image of an `S`-unit to the
diagonal image of its translate. -/
theorem map_infiniteUnit (σ : Gal(K/k)) (u : Additive ↥(sUnits K (Set.range ι)))
    (w : InfinitePlace K) :
    (infiniteRingFamily (k := k) (K := K)).unitsFamily.map σ w
        (Additive.ofMul (infiniteUnitHom w ((u.toMul : ↥(sUnits K (Set.range ι))) : Kˣ)))
      = Additive.ofMul (infiniteUnitHom (σ • w)
          ((((sUnitsAut hι σ) u).toMul : ↥(sUnits K (Set.range ι))) : Kˣ)) := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [RingFamilyAction.unitsFamily_map_apply]
  show infiniteCompletionGalEquiv w σ (infiniteCoe _ w) = infiniteCoe _ (σ • w)
  rw [infiniteCompletionGalEquiv_infiniteCoe]
  rfl

/-- At a finite place, the transport isomorphism carries the diagonal image of an `S`-unit to the
diagonal image of its translate. -/
theorem map_sUnitAdicComponent (σ : Gal(K/k)) (u : Additive ↥(sUnits K (Set.range ι)))
    (v : HeightOneSpectrum (𝓞 K)) :
    (adicSIdeleFamily (Set.range ι) (smul_mem_range_iff hι)).map σ v
        (sUnitAdicComponent (Set.range ι) u.toMul v)
      = sUnitAdicComponent (Set.range ι) ((sUnitsAut hι σ) u).toMul (σ • v) := by
  refine Subtype.ext (Additive.toMul.injective (Units.ext ?_))
  rw [adicSIdeleFamily_eq, FamilyAction.restrict_map, FamilyAction.coe_restrictMap]
  show (adicCompletionGalEquiv v σ) (adicCoe _ v) = adicCoe _ (σ • v)
  rw [adicCompletionGalEquiv_adicCoe]
  rfl

/-- **The diagonal commutes with the Galois action**: the action on the `S`-ideles restricts along
the diagonal to the action on the `S`-units. -/
theorem sIdeleAut_sIdeleDiag (σ : Gal(K/k)) (u : Additive ↥(sUnits K (Set.range ι))) :
    sIdeleAut hι σ (sIdeleDiag (Set.range ι) u)
      = sIdeleDiag (Set.range ι) (sUnitsAut hι σ u) := by
  rw [sIdeleAut_eq, prodAut_apply]
  exact Prod.ext (FamilyAction.familyAut_eq_of_map _ σ _ _ (map_infiniteUnit hι σ u))
    (FamilyAction.familyAut_eq_of_map _ σ _ _ (map_sUnitAdicComponent hι σ u))

end Equiv

/-! ### The Herbrand quotient of the quotient group -/

section Class

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {Y : Type*} [Fintype Y] [MulAction Gal(K/k) Y]
  [Fintype (orbitRel.Quotient Gal(K/k) Y)] {ι : Y → HeightOneSpectrum (𝓞 K)}
  (hι : ∀ (g : Gal(K/k)) (y : Y), ι (g • y) = g • ι y) [DecidablePred (· ∈ Set.range ι)]
  (σ : Gal(K/k)) {n : ℕ} (hn : Nat.card Gal(K/k) = n)

include hι hn

omit [NumberField k] [IsGalois k K] [Fintype Y] [Fintype (orbitRel.Quotient Gal(K/k) Y)]
  [DecidablePred (· ∈ Set.range ι)] in
/-- The action of a Galois automorphism on the `S`-units has order dividing the degree. -/
theorem sUnitsAut_pow_eq_one_of_card : (sUnitsAut hι σ) ^ n = 1 :=
  sUnitsAut_pow_eq_one hι (by rw [← hn]; exact pow_card_eq_one')

omit [NumberField k] [IsGalois k K] [Fintype Y] [Fintype (orbitRel.Quotient Gal(K/k) Y)] in
/-- The action of a Galois automorphism on the `S`-ideles has order dividing the degree. -/
theorem sIdeleAut_pow_eq_one : (sIdeleAut hι σ) ^ n = 1 := by
  have hσ : σ ^ n = 1 := by rw [← hn]; exact pow_card_eq_one'
  rw [sIdeleAut_eq]
  exact prodAut_pow_eq_one (by rw [← map_pow, hσ, map_one]) (by rw [← map_pow, hσ, map_one])

/-- The short exact sequence of the `S`-units inside the `S`-ideles, with the group of classes of
`S`-ideles as its quotient term. -/
noncomputable def sIdeleClassSES :
    TateSES n (Additive ↥(sUnits K (Set.range ι))) (SIdele (Set.range ι))
      (SIdele (Set.range ι) ⧸ (sIdeleDiag (Set.range ι)).range) :=
  tateSESOfInjective (sUnitsAut_pow_eq_one_of_card hι σ hn) (sIdeleAut_pow_eq_one hι σ hn)
    (sIdeleDiag (Set.range ι)) (fun a => (sIdeleAut_sIdeleDiag hι σ a).symm)
    (sIdeleDiag_injective _)

omit [NumberField k] [IsGalois k K] [Fintype Y] [Fintype (orbitRel.Quotient Gal(K/k) Y)] in
@[simp]
theorem sIdeleClassSES_σA : (sIdeleClassSES hι σ hn).σA = sUnitsAut hι σ := rfl

omit [NumberField k] [IsGalois k K] [Fintype Y] [Fintype (orbitRel.Quotient Gal(K/k) Y)] in
@[simp]
theorem sIdeleClassSES_σB : (sIdeleClassSES hι σ hn).σB = sIdeleAut hι σ := rfl

variable (hinj : Function.Injective ι) [NeZero n]

include hinj

/-- **The classes of the ideles that are units outside the chosen places have Herbrand quotient the
degree of the extension**, provided the chosen places carry the ramification and the Galois group is
generated by the automorphism in question.  Both outer terms of the short exact sequence have the
same product of orders of decomposition groups as Herbrand quotient, up to the degree, so the
products cancel and only the degree survives. -/
theorem herbrand_sIdeleClassSES
    (hunram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Set.range ι →
      ∃ π : (v.adicCompletion K)ˣ,
        (∀ g : ↥(stabilizer Gal(K/k) v),
            g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
          ∧ unitVal (Additive.ofMul π) = 1)
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) :
    herbrand (sIdeleClassSES hι σ hn).σC n = n := by
  have hpos : (0 : ℚ)
      < (∏ v : InfinitePlace k, (Nat.card ↥(stabilizer Gal(K/k) (placeAbove k K v)) : ℚ))
        * ∏ o : orbitRel.Quotient Gal(K/k) Y, (Nat.card ↥(stabilizer Gal(K/k) o.out) : ℚ) := by
    refine mul_pos (Finset.prod_pos fun i _ => ?_) (Finset.prod_pos fun o _ => ?_)
    · exact_mod_cast Nat.card_pos
    · exact_mod_cast Nat.card_pos
  have hB : (0 : ℚ) < herbrand (sIdeleAut hι σ) n := by
    rw [herbrand_sIdeleAut hι hinj hunram hgen hn]
    exact hpos
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hAn : (0 : ℚ) < herbrand (sUnitsAut hι σ) n * n := by
    rw [herbrand_sUnitsAut_mul hι hinj hgen hn]
    exact hpos
  have hA : (0 : ℚ) < herbrand (sUnitsAut hι σ) n := by
    by_contra hc
    push_neg at hc
    nlinarith
  obtain ⟨hB0, hB1⟩ := finite_tate_of_herbrand_ne_zero (sIdeleAut hι σ) n hB.ne'
  obtain ⟨hA0, hA1⟩ := finite_tate_of_herbrand_ne_zero (sUnitsAut hι σ) n hA.ne'
  haveI : Finite (tateH0 (sIdeleClassSES hι σ hn).σA n) := hA0
  haveI : Finite (tateHm1 (sIdeleClassSES hι σ hn).σA n) := hA1
  haveI : Finite (tateH0 (sIdeleClassSES hι σ hn).σB n) := hB0
  haveI : Finite (tateHm1 (sIdeleClassSES hι σ hn).σB n) := hB1
  haveI : Finite (tateH0 (sIdeleClassSES hι σ hn).σC n) :=
    TateSES.finite_tateH0_quot' (sIdeleClassSES hι σ hn)
  haveI : Finite (tateHm1 (sIdeleClassSES hι σ hn).σC n) :=
    TateSES.finite_tateHm1_quot' (sIdeleClassSES hι σ hn)
  have hmul := (sIdeleClassSES hι σ hn).herbrand_mul
  rw [sIdeleClassSES_σA, sIdeleClassSES_σB,
    herbrand_sIdeleAut_eq_sUnits_mul hι hinj hunram hgen hn] at hmul
  exact mul_left_cancel₀ hA.ne' hmul

end Class

end InverseGalois.CFT

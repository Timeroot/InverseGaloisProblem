/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.Idele
import InverseGalois.CFT.Units.SIdeleClass

/-!
# The Herbrand quotient of the idele class group

The idele class group of a number field is the quotient of the ideles by the diagonal image of the
multiplicative group of the field.  The ideles that are units outside a finite set of places form a
subgroup, and when that set is large enough the two quotients coincide: every idele differs from one
of the smaller group by a principal idele, and the elements of the field that are ideles of the
smaller group are exactly the `S`-units.  The Herbrand quotient of the idele class group is
therefore the one already computed, namely the degree of the extension.

The largeness required of the set of places is exactly what the finiteness of the class number
provides: every finitely supported system of orders must be realised away from the set by a single
element of the field.

## Main definitions

* `InverseGalois.CFT.sIdeleToIdele`: the ideles that are units outside a finite set of places, as
  ideles.
* `InverseGalois.CFT.ideleClassAut`: **the action of a Galois automorphism on the idele class
  group.**

## Main results

* `InverseGalois.CFT.exists_ideleDiag_add_sIdeleToIdele`: **every idele is a principal idele plus an
  idele that is a unit outside the chosen places.**
* `InverseGalois.CFT.mem_range_ideleDiag_iff`: **an idele that is a unit outside the chosen places is
  principal exactly when it comes from an `S`-unit.**
* `InverseGalois.CFT.herbrand_ideleClassAut`: **the idele class group has Herbrand quotient the
  degree of the extension.**

## Tags

number field, idele class group, S-unit, Herbrand quotient, first inequality
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

/-! ### The ideles that are units outside a finite set of places -/

section Incl

variable {K : Type*} [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K)))
  [DecidablePred (· ∈ T)]

/-- An idele that is a unit outside the chosen places, viewed in the product of all the local unit
groups. -/
noncomputable def sIdeleIncl : SIdele T →+ FullIdele K where
  toFun x := (x.1, fun v => ((x.2 v : ↥(adicSUnits T v)) : Additive (v.adicCompletion K)ˣ))
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem sIdeleIncl_fst (x : SIdele T) (w : InfinitePlace K) : (sIdeleIncl T x).1 w = x.1 w := rfl

@[simp]
theorem sIdeleIncl_snd (x : SIdele T) (v : HeightOneSpectrum (𝓞 K)) :
    (sIdeleIncl T x).2 v = ((x.2 v : ↥(adicSUnits T v)) : Additive (v.adicCompletion K)ˣ) := rfl

theorem sIdeleIncl_injective : Function.Injective (sIdeleIncl T) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := fun v => congrFun (congrArg Prod.snd h) v
  exact Prod.ext h1 (funext fun v => Subtype.ext (h2 v))

/-- Away from the chosen places, the local component of an idele that is a unit outside them has
valuation zero. -/
theorem unitVal_coe_adicSUnits {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ T)
    (a : ↥(adicSUnits T v)) : unitVal ((a : Additive (v.adicCompletion K)ˣ)) = 0 := by
  obtain ⟨a, ha⟩ := a
  show unitVal a = 0
  rw [adicSUnits_of_notMem T hv, AddMonoidHom.mem_ker] at ha
  exact ha

theorem sIdeleIncl_mem_idele (hT : T.Finite) (x : SIdele T) : sIdeleIncl T x ∈ idele K := by
  rw [mem_idele]
  filter_upwards [hT.compl_mem_cofinite] with v hv
  exact unitVal_coe_adicSUnits T hv (x.2 v)

/-- **An idele that is a unit outside the chosen places, as an idele.** -/
noncomputable def sIdeleToIdele (hT : T.Finite) : SIdele T →+ ↥(idele K) where
  toFun x := ⟨sIdeleIncl T x, sIdeleIncl_mem_idele T hT x⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp]
theorem coe_sIdeleToIdele (hT : T.Finite) (x : SIdele T) :
    ((sIdeleToIdele T hT x : ↥(idele K)) : FullIdele K) = sIdeleIncl T x := rfl

/-- The diagonal of the `S`-units is the diagonal of the field, restricted. -/
theorem sIdeleIncl_sIdeleDiag (u : Additive ↥(sUnits K T)) :
    sIdeleIncl T (sIdeleDiag T u)
      = fullDiag K (Additive.ofMul ((u.toMul : ↥(sUnits K T)) : Kˣ)) :=
  rfl

end Incl

/-! ### Comparison of the two quotients -/

section Compare

variable {K : Type*} [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K)))
  [DecidablePred (· ∈ T)] (hT : T.Finite)

/-- **Every idele is a principal idele plus an idele that is a unit outside the chosen places**,
provided every finitely supported system of orders is realised away from the chosen places by an
element of the field. -/
theorem exists_ideleDiag_add_sIdeleToIdele
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ T, ord K v (a : K) = m v)
    (x : ↥(idele K)) :
    ∃ (a : Additive Kˣ) (y : SIdele T), x = ideleDiag K a + sIdeleToIdele T hT y := by
  obtain ⟨a, ha⟩ := hrepr (fun v => -unitVal ((x : FullIdele K).2 v)) (by
    filter_upwards [(mem_idele K).mp x.2] with v hv
    rw [hv, neg_zero])
  have hzv : ∀ v ∉ T,
      unitVal (((x : FullIdele K) - fullDiag K (Additive.ofMul a)).2 v) = 0 := by
    intro v hv
    show unitVal ((x : FullIdele K).2 v - (fullDiag K (Additive.ofMul a)).2 v) = 0
    rw [map_sub, fullDiag_snd]
    show unitVal ((x : FullIdele K).2 v) - unitVal (Additive.ofMul (adicUnitHom v a)) = 0
    rw [unitVal_adicUnitHom, ha v hv]
    ring
  refine ⟨Additive.ofMul a,
    (((x : FullIdele K) - fullDiag K (Additive.ofMul a)).1,
      fun v => ⟨((x : FullIdele K) - fullDiag K (Additive.ofMul a)).2 v, ?_⟩), ?_⟩
  · by_cases hv : v ∈ T
    · rw [adicSUnits_of_mem T hv]
      trivial
    · rw [adicSUnits_of_notMem T hv, AddMonoidHom.mem_ker]
      exact hzv v hv
  · refine Subtype.ext ?_
    show (x : FullIdele K)
      = fullDiag K (Additive.ofMul a) + ((x : FullIdele K) - fullDiag K (Additive.ofMul a))
    abel

/-- **An idele that is a unit outside the chosen places is principal exactly when it comes from an
`S`-unit.**  An element of the field whose diagonal image is a unit of the valuation ring away from
the chosen places has order zero there, which is what it means to be an `S`-unit. -/
theorem mem_range_ideleDiag_iff (y : SIdele T) :
    sIdeleToIdele T hT y ∈ (ideleDiag K).range ↔ y ∈ (sIdeleDiag T).range := by
  constructor
  · rintro ⟨a, ha⟩
    have hfull : fullDiag K a = sIdeleIncl T y := congrArg Subtype.val ha
    have hmem : (a.toMul : Kˣ) ∈ sUnits K T := by
      refine mem_sUnits.mpr fun v hv => ?_
      have h2 := congrFun (congrArg Prod.snd hfull) v
      have h3 : unitVal ((fullDiag K a).2 v) = 0 := by
        rw [h2]
        exact unitVal_coe_adicSUnits T hv (y.2 v)
      rw [fullDiag_snd, unitVal_adicUnitHom, neg_eq_zero] at h3
      exact h3
    exact ⟨Additive.ofMul ⟨a.toMul, hmem⟩,
      sIdeleIncl_injective T ((sIdeleIncl_sIdeleDiag T _).trans hfull)⟩
  · rintro ⟨u, rfl⟩
    exact ⟨Additive.ofMul ((u.toMul : ↥(sUnits K T)) : Kˣ),
      Subtype.ext (sIdeleIncl_sIdeleDiag T u).symm⟩

end Compare

/-! ### Equivariance -/

section Equivariance

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K]

omit [NumberField K] in
/-- At an infinite place, the transport carries the diagonal image of a unit of the field to the
diagonal image of its translate. -/
theorem map_infiniteUnitHom (σ : Gal(K/k)) (a : Additive Kˣ) (w : InfinitePlace K) :
    (infiniteRingFamily (k := k) (K := K)).unitsFamily.map σ w
        (Additive.ofMul (infiniteUnitHom w a.toMul))
      = Additive.ofMul (infiniteUnitHom (σ • w) ((globalUnitsAut σ a).toMul)) := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [RingFamilyAction.unitsFamily_map_apply]
  show infiniteCompletionGalEquiv w σ (infiniteCoe _ w) = infiniteCoe _ (σ • w)
  rw [infiniteCompletionGalEquiv_infiniteCoe]
  rfl

/-- At a finite place, the transport carries the diagonal image of a unit of the field to the
diagonal image of its translate. -/
theorem map_adicUnitHom (σ : Gal(K/k)) (a : Additive Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (adicRingFamily (k := k) (K := K)).unitsFamily.map σ v
        (Additive.ofMul (adicUnitHom v a.toMul))
      = Additive.ofMul (adicUnitHom (σ • v) ((globalUnitsAut σ a).toMul)) := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [RingFamilyAction.unitsFamily_map_apply]
  show adicCompletionGalEquiv v σ (adicCoe _ v) = adicCoe _ (σ • v)
  rw [adicCompletionGalEquiv_adicCoe]
  rfl

/-- **The diagonal commutes with the Galois action.** -/
theorem fullIdeleAut_fullDiag (σ : Gal(K/k)) (a : Additive Kˣ) :
    fullIdeleAut (k := k) σ (fullDiag K a) = fullDiag K (globalUnitsAut σ a) :=
  Prod.ext (FamilyAction.familyAut_eq_of_map _ σ _ _ (map_infiniteUnitHom σ a))
    (FamilyAction.familyAut_eq_of_map _ σ _ _ (map_adicUnitHom σ a))

theorem ideleAut_ideleDiag (σ : Gal(K/k)) (a : Additive Kˣ) :
    ideleAut (k := k) σ (ideleDiag K a) = ideleDiag K (globalUnitsAut σ a) :=
  Subtype.ext (fullIdeleAut_fullDiag σ a)

/-- The diagonal image of the units of the field is a stable subgroup of the ideles. -/
theorem map_range_ideleDiag (σ : Gal(K/k)) :
    (ideleDiag K).range.map (ideleAut (k := k) σ : ↥(idele K) →+ ↥(idele K))
      = (ideleDiag K).range :=
  map_range_eq_range (σA := globalUnitsAut σ) (ideleDiag K) fun a =>
    (ideleAut_ideleDiag σ a).symm

/-- **The action of a Galois automorphism on the idele class group.** -/
noncomputable def ideleClassAut (σ : Gal(K/k)) :
    (↥(idele K) ⧸ (ideleDiag K).range) ≃+ (↥(idele K) ⧸ (ideleDiag K).range) :=
  quotAut (B := ↥(idele K)) (ideleAut (k := k) σ) (ideleDiag K).range (map_range_ideleDiag σ)

@[simp]
theorem ideleClassAut_mk (σ : Gal(K/k)) (x : ↥(idele K)) :
    ideleClassAut (k := k) σ (QuotientAddGroup.mk x)
      = QuotientAddGroup.mk (ideleAut (k := k) σ x) := rfl

variable {Y : Type*} [MulAction Gal(K/k) Y] {ι : Y → HeightOneSpectrum (𝓞 K)}
  (hι : ∀ (g : Gal(K/k)) (y : Y), ι (g • y) = g • ι y) [DecidablePred (· ∈ Set.range ι)]

include hι

/-- The inclusion of the ideles that are units outside the chosen places commutes with the Galois
action. -/
theorem sIdeleIncl_sIdeleAut (σ : Gal(K/k)) (y : SIdele (Set.range ι)) :
    sIdeleIncl (Set.range ι) (sIdeleAut hι σ y)
      = fullIdeleAut (k := k) σ (sIdeleIncl (Set.range ι) y) := by
  rw [sIdeleAut_eq, prodAut_apply, fullIdeleAut, prodAut_apply]
  refine Prod.ext rfl (funext fun v => ?_)
  show (((adicSIdeleFamily (Set.range ι) (smul_mem_range_iff hι)).familyAut σ y.2 v :
      ↥(adicSUnits (Set.range ι) v)) : Additive (v.adicCompletion K)ˣ)
    = (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ
        (fun v => ((y.2 v : ↥(adicSUnits (Set.range ι) v)) : Additive (v.adicCompletion K)ˣ)) v
  rw [(adicSIdeleFamily (Set.range ι) (smul_mem_range_iff hι)).familyAut_apply_eq_transport
        (smul_inv_smul σ v) y.2,
    (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut_apply_eq_transport
      (smul_inv_smul σ v) (fun v => ((y.2 v : ↥(adicSUnits (Set.range ι) v)) :
        Additive (v.adicCompletion K)ˣ)),
    adicSIdeleFamily_eq, FamilyAction.coe_restrict_transport]

theorem sIdeleToIdele_sIdeleAut (hT : (Set.range ι).Finite) (σ : Gal(K/k))
    (y : SIdele (Set.range ι)) :
    sIdeleToIdele (Set.range ι) hT (sIdeleAut hι σ y)
      = ideleAut (k := k) σ (sIdeleToIdele (Set.range ι) hT y) :=
  Subtype.ext (sIdeleIncl_sIdeleAut hι σ y)

end Equivariance

/-! ### The Herbrand quotient of the idele class group -/

section Herbrand

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {Y : Type*} [Fintype Y] [MulAction Gal(K/k) Y]
  [Fintype (orbitRel.Quotient Gal(K/k) Y)] {ι : Y → HeightOneSpectrum (𝓞 K)}
  (hι : ∀ (g : Gal(K/k)) (y : Y), ι (g • y) = g • ι y) [DecidablePred (· ∈ Set.range ι)]
  (σ : Gal(K/k)) {n : ℕ} (hn : Nat.card Gal(K/k) = n)
  (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
    (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
    ∃ a : Kˣ, ∀ v ∉ Set.range ι, ord K v (a : K) = m v)

include hι hrepr

omit [NumberField k] [IsGalois k K] [Fintype (orbitRel.Quotient Gal(K/k) Y)] hι in
/-- The classes of the ideles that are units outside the chosen places exhaust the idele class
group, and two of them agree exactly when they differ by an `S`-unit. -/
theorem sIdeleClassHom_surjective :
    Function.Surjective (((QuotientAddGroup.mk' (ideleDiag K).range).comp
      (sIdeleToIdele (Set.range ι) (Set.finite_range ι))) ) := by
  intro z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨a, y, hy⟩ := exists_ideleDiag_add_sIdeleToIdele (Set.range ι) (Set.finite_range ι)
    hrepr x
  refine ⟨y, ?_⟩
  show QuotientAddGroup.mk (sIdeleToIdele (Set.range ι) (Set.finite_range ι) y)
    = QuotientAddGroup.mk x
  have hz : (QuotientAddGroup.mk (ideleDiag K a) : ↥(idele K) ⧸ (ideleDiag K).range) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)
  rw [hy, QuotientAddGroup.mk_add, hz]
  abel

omit [NumberField k] [IsGalois k K] [Fintype (orbitRel.Quotient Gal(K/k) Y)] hι hrepr in
theorem sIdeleClassHom_ker :
    ((QuotientAddGroup.mk' (ideleDiag K).range).comp
        (sIdeleToIdele (Set.range ι) (Set.finite_range ι))).ker
      = (sIdeleDiag (Set.range ι)).range := by
  ext y
  rw [AddMonoidHom.mem_ker]
  show QuotientAddGroup.mk (sIdeleToIdele (Set.range ι) (Set.finite_range ι) y) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  exact mem_range_ideleDiag_iff (Set.range ι) (Set.finite_range ι) y

/-- The classes of the ideles that are units outside the chosen places are the idele classes. -/
noncomputable def sIdeleClassEquiv :
    (SIdele (Set.range ι) ⧸ (sIdeleDiag (Set.range ι)).range)
      ≃+ (↥(idele K) ⧸ (ideleDiag K).range) :=
  (QuotientAddGroup.quotientAddEquivOfEq (sIdeleClassHom_ker (K := K) (ι := ι)).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (sIdeleClassHom_surjective hrepr))

omit [NumberField k] [IsGalois k K] [Fintype (orbitRel.Quotient Gal(K/k) Y)] hι in
theorem sIdeleClassEquiv_mk (y : SIdele (Set.range ι)) :
    sIdeleClassEquiv hrepr (QuotientAddGroup.mk y)
      = QuotientAddGroup.mk (sIdeleToIdele (Set.range ι) (Set.finite_range ι) y) := rfl

omit [NumberField k] [IsGalois k K] [Fintype Y] [Fintype (orbitRel.Quotient Gal(K/k) Y)] hrepr in
theorem sIdeleClassSES_σC_mk (y : SIdele (Set.range ι)) :
    (sIdeleClassSES hι σ hn).σC (QuotientAddGroup.mk y)
      = QuotientAddGroup.mk (sIdeleAut hι σ y) := rfl

include hn

/-- **The idele class group has Herbrand quotient the degree of the extension**, provided the chosen
places carry the ramification and the ideal classes and the Galois group is generated by the
automorphism in question. -/
theorem herbrand_ideleClassAut (hinj : Function.Injective ι) [NeZero n]
    (hunram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Set.range ι →
      ∃ π : (v.adicCompletion K)ˣ,
        (∀ g : ↥(stabilizer Gal(K/k) v),
            g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
          ∧ unitVal (Additive.ofMul π) = 1)
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) :
    herbrand (ideleClassAut (k := k) (K := K) σ) n = n := by
  rw [← herbrand_sIdeleClassSES hι σ hn hinj hunram hgen]
  refine (herbrand_congr (sIdeleClassEquiv (Y := Y) (ι := ι) hrepr) (fun z => ?_) n).symm
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [sIdeleClassSES_σC_mk, sIdeleClassEquiv_mk, sIdeleClassEquiv_mk, ideleClassAut_mk,
    sIdeleToIdele_sIdeleAut hι (Set.finite_range ι) σ y]

end Herbrand

end InverseGalois.CFT

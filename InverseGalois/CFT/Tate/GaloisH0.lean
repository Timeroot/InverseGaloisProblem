/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Galois
import InverseGalois.CFT.NormSubgroup

/-!
# The zeroth Tate group of the units of a cyclic extension

For a finite cyclic Galois extension `L / K` with a chosen generator `g` of the Galois group, the
zeroth Tate group of the unit group is the group of units of the base field modulo the norms.

The two ingredients are already available.  A unit fixed by a generator is fixed by the whole
Galois group, hence lies in the base field, so every class of `Ĥ⁰(Lˣ)` comes from a unit of `K`;
and the norm operator of the Tate formalism is the field norm, so the class of a unit of `K`
vanishes exactly when that unit is a norm.  Packaging the two statements gives a surjection from
the units of `K` onto `Ĥ⁰(Lˣ)` whose kernel is the group of norms, and hence an isomorphism from
`Kˣ / N Lˣ`.

Counting, the order of `Ĥ⁰(Lˣ)` is the norm index `[Kˣ : N Lˣ]`.  Together with the vanishing of
`Ĥ⁻¹(Lˣ)` this makes the Herbrand quotient of the unit group equal to that index.

## Main definitions

* `InverseGalois.CFT.tateH0Units`: the map from the units of the base field to `Ĥ⁰(Lˣ)`.
* `InverseGalois.CFT.tateH0UnitsEquiv`: the resulting isomorphism `Kˣ / N Lˣ ≃+ Ĥ⁰(Lˣ)`.

## Main results

* `InverseGalois.CFT.tateH0Units_surjective`: every class of `Ĥ⁰(Lˣ)` comes from the base field.
* `InverseGalois.CFT.tateH0Units_eq_zero_iff`: the class of a base unit vanishes exactly when it
  is a norm.
* `InverseGalois.CFT.card_tateH0_units`: the order of `Ĥ⁰(Lˣ)` is the norm index.
* `InverseGalois.CFT.herbrand_units`: the Herbrand quotient of the unit group is the norm index.

## Tags

Tate cohomology, norm index, cyclic extension, Herbrand quotient
-/

namespace InverseGalois.CFT

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **A unit of the base field, viewed in the extension.** -/
def unitsAlgebraMap (K L : Type) [Field K] [Field L] [Algebra K L] : Kˣ →* Lˣ :=
  Units.map (algebraMap K L : K →+* L).toMonoidHom

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem coe_unitsAlgebraMap (k : Kˣ) :
    ((unitsAlgebraMap K L k : Lˣ) : L) = algebraMap K L (k : K) := rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A unit of the base field is fixed by every automorphism of the extension. -/
theorem unitsAut_unitsAlgebraMap (g : L ≃ₐ[K] L) (k : Kˣ) :
    unitsAut g (unitsAlgebraMap K L k) = unitsAlgebraMap K L k :=
  Units.ext (g.commutes (k : K))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A unit of the base field is a fixed point of the transported automorphism. -/
theorem addAut_unitsAlgebraMap (g : L ≃ₐ[K] L) (k : Kˣ) :
    addAut (unitsAut g) (Additive.ofMul (unitsAlgebraMap K L k))
      = Additive.ofMul (unitsAlgebraMap K L k) :=
  addAut_apply_eq_self _ (unitsAut_unitsAlgebraMap g k)

/-- **The map from the units of the base field to `Ĥ⁰` of the unit group.** -/
noncomputable def tateH0Units (g : L ≃ₐ[K] L) :
    Additive Kˣ →+ tateH0 (addAut (unitsAut g)) (Nat.card (L ≃ₐ[K] L)) :=
  (QuotientAddGroup.mk' _).comp
    ((MonoidHom.toAdditive (unitsAlgebraMap K L)).codRestrict
      (sigmaSubOne (addAut (unitsAut g))).ker
      (fun u => (mem_ker_sigmaSubOne_iff _ _).mpr (addAut_unitsAlgebraMap g (Additive.toMul u))))

omit [FiniteDimensional K L] [IsGalois K L] in
theorem tateH0Units_apply (g : L ≃ₐ[K] L) (k : Kˣ) :
    tateH0Units g (Additive.ofMul k)
      = tateH0.mk (addAut (unitsAut g)) (Nat.card (L ≃ₐ[K] L))
          (Additive.ofMul (unitsAlgebraMap K L k)) (addAut_unitsAlgebraMap g k) := rfl

/-- **Every class of `Ĥ⁰` of the unit group comes from the base field.** -/
theorem tateH0Units_surjective (g : L ≃ₐ[K] L)
    (hg : ∀ φ : L ≃ₐ[K] L, φ ∈ Subgroup.zpowers g) :
    Function.Surjective (tateH0Units g) := by
  intro c
  obtain ⟨u, hu, rfl⟩ := tateH0.mk_surjective c
  obtain ⟨x, rfl⟩ : ∃ x : Lˣ, Additive.ofMul x = u := ⟨Additive.toMul u, rfl⟩
  have hfix : unitsAut g x = x := Additive.ofMul.injective hu
  obtain ⟨k, hk⟩ := exists_algebraMap_of_unitsAut_eq g hg hfix
  have hux : unitsAlgebraMap K L k = x := Units.ext hk
  subst hux
  exact ⟨Additive.ofMul k, tateH0Units_apply g k⟩

/-- **The class of a base unit vanishes in `Ĥ⁰` exactly when it is a norm.** -/
theorem tateH0Units_eq_zero_iff (g : L ≃ₐ[K] L)
    (hg : ∀ φ : L ≃ₐ[K] L, φ ∈ Subgroup.zpowers g) (k : Kˣ) :
    tateH0Units g (Additive.ofMul k) = 0 ↔ k ∈ normSubgroup K L := by
  rw [tateH0Units_apply, tateH0_unitsAut_mk_eq_zero_iff, mem_normSubgroup_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, FaithfulSMul.algebraMap_injective K L ?_⟩
    have hval := congrArg (Units.val) hy
    rw [coe_prod_range_unitsAut g hg y] at hval
    exact hval
  · rintro ⟨y, hy⟩
    refine ⟨y, Units.ext ?_⟩
    rw [coe_prod_range_unitsAut g hg y, hy]
    rfl

/-- The kernel of the map onto `Ĥ⁰` is the group of norms. -/
theorem ker_tateH0Units (g : L ≃ₐ[K] L) (hg : ∀ φ : L ≃ₐ[K] L, φ ∈ Subgroup.zpowers g) :
    (tateH0Units g).ker = Subgroup.toAddSubgroup (normSubgroup K L) := by
  ext u
  rw [AddMonoidHom.mem_ker]
  exact tateH0Units_eq_zero_iff g hg (Additive.toMul u)

/-- **`Ĥ⁰` of the unit group is the units of the base field modulo the norms.** -/
noncomputable def tateH0UnitsEquiv (g : L ≃ₐ[K] L)
    (hg : ∀ φ : L ≃ₐ[K] L, φ ∈ Subgroup.zpowers g) :
    Additive Kˣ ⧸ Subgroup.toAddSubgroup (normSubgroup K L)
      ≃+ tateH0 (addAut (unitsAut g)) (Nat.card (L ≃ₐ[K] L)) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_tateH0Units g hg).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (tateH0Units_surjective g hg))

/-- **The order of `Ĥ⁰` of the unit group is the norm index.** -/
theorem card_tateH0_units (g : L ≃ₐ[K] L) (hg : ∀ φ : L ≃ₐ[K] L, φ ∈ Subgroup.zpowers g) :
    Nat.card (tateH0 (addAut (unitsAut g)) (Nat.card (L ≃ₐ[K] L)))
      = (normSubgroup K L).index := by
  rw [← Nat.card_congr (tateH0UnitsEquiv g hg).toEquiv, ← Subgroup.index_toAddSubgroup,
    AddSubgroup.index_eq_card]

/-- The lower Tate group of the unit group has exactly one element. -/
theorem card_tateHm1_units (g : L ≃ₐ[K] L) (hg : ∀ φ : L ≃ₐ[K] L, φ ∈ Subgroup.zpowers g) :
    Nat.card (tateHm1 (addAut (unitsAut g)) (Nat.card (L ≃ₐ[K] L))) = 1 := by
  haveI : Subsingleton (tateHm1 (addAut (unitsAut g)) (Nat.card (L ≃ₐ[K] L))) :=
    ⟨fun a b => by rw [tateHm1_unitsAut_eq_zero g hg a, tateHm1_unitsAut_eq_zero g hg b]⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩

/-- **The Herbrand quotient of the unit group is the norm index.**  The lower Tate group vanishes
by Hilbert's theorem 90, and the upper one is the units of the base field modulo the norms. -/
theorem herbrand_units (g : L ≃ₐ[K] L) (hg : ∀ φ : L ≃ₐ[K] L, φ ∈ Subgroup.zpowers g) :
    herbrand (addAut (unitsAut g)) (Nat.card (L ≃ₐ[K] L)) = (normSubgroup K L).index := by
  rw [herbrand, card_tateH0_units g hg, card_tateHm1_units g hg, Nat.cast_one, div_one]

end InverseGalois.CFT

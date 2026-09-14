/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ConfinedWeighted
import InverseGalois.CFT.PoitouTate.NamedRadicandClass
import InverseGalois.CFT.PoitouTate.RadicandPlaces
import InverseGalois.CFT.PoitouTate.TensorDescent
import InverseGalois.CFT.Units.SUnitFinite

/-!
# The descent run inside the units for a finite set of places

The obstruction to correcting a radicand of confined units to an invariant one is a class of the
first cohomology with coefficients in the confined units having no order at the named places.  Over
a number field that group is far too big to count against: the named places are finitely many, and
the units are left arbitrary order at every other place of the field.

The descent does not need the whole group.  Only finitely many orders are prescribed, so only
finitely many units are needed to realise every prescription, and each of them has a zero or a pole
at finitely many places only.  Collect those places, close the collection under the Galois group,
and the vector of orders is already onto from the confined units supported inside the resulting
finite set.  Running the descent in that subgroup leaves coefficients in the units for a finite set
of places, and the radicand it produces is carried back to a confined radicand with the same orders
by the inclusion, which commutes with the reading.

So no second reading and no arithmetic beyond the surjectivity already in hand is needed to make
the coefficients of the obstruction the units for a finite set of places.

## Main definitions

* `InverseGalois.CFT.confinedSupportUnits`: the confined units having no order outside a set of
  places.
* `InverseGalois.CFT.confinedSupportOrd`: the vector of orders of such a unit at the named places.
* `InverseGalois.CFT.confinedSupportSUnits`: those of them whose orders at the named places vanish.

## Main results

* `InverseGalois.CFT.exists_finite_stable_surjective_confinedSupportOrd`: **the vector of orders is
  already onto from the confined units supported inside a finite stable set of places.**
* `InverseGalois.CFT.exists_invariant_confinedTensorVal_eq_of_named_of_support_class`: **an
  invariant radicand of confined units with the prescribed orders at the named places, the
  obstruction being asked to vanish only with coefficients in the units for a finite set.**
* `InverseGalois.CFT.exists_spanning_confinedSupportSUnits`: **the coefficients of the obstruction,
  for a finite set of places, are spanned by finitely many units.**

## Tags

number field, S-unit, place, order, descent, group cohomology, obstruction, tensor product
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Rigidity.RET TensorProduct

open groupCohomology

/-! ### The confined units supported inside a set of places -/

section Support

variable {K : Type} [Field K] [NumberField K]
variable (n : ℕ) (Tz Y T : Set (HeightOneSpectrum (𝓞 K)))

/-- **The confined units having no order outside a set of places.** -/
def confinedSupportUnits : Subgroup ↥(confinedUnits K n Tz Y) where
  carrier := {x | ∀ v ∉ T, ord K v ((x : Kˣ) : K) = 0}
  mul_mem' {x y} hx hy v hv := by
    show ord K v (((x : Kˣ) * (y : Kˣ) : Kˣ) : K) = 0
    rw [Units.val_mul, ord_mul _ (Units.ne_zero _) (Units.ne_zero _), hx v hv, hy v hv, add_zero]
  one_mem' v _ := by
    show ord K v (((1 : Kˣ) : K)) = 0
    rw [Units.val_one, ord_one]
  inv_mem' {x} hx v hv := by
    show ord K v ((((x : Kˣ)⁻¹ : Kˣ) : K)) = 0
    rw [Units.val_inv_eq_inv_val, ord_inv, hx v hv, neg_zero]

theorem mem_confinedSupportUnits {x : ↥(confinedUnits K n Tz Y)} :
    x ∈ confinedSupportUnits n Tz Y T ↔ ∀ v ∉ T, ord K v ((x : Kˣ) : K) = 0 := Iff.rfl

variable {k : Type} [Field k] [Algebra k K]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y]
  [IsGaloisStablePlaces k K T]

/-- **The confined units supported inside a stable set are carried into themselves by the Galois
group.** -/
instance isStableSubgroup_confinedSupportUnits :
    IsStableSubgroup Gal(K/k) (confinedSupportUnits n Tz Y T) where
  smul_mem σ {a} ha v hv :=
    (ord_coe_smul_confinedUnits n Tz Y σ a v).trans
      (ha (σ⁻¹ • v) fun hc => hv ((IsGaloisStablePlaces.smul_mem_iff (k := k) (T := T) σ⁻¹ v).1 hc))

end Support

/-! ### The vector of orders at the named places -/

section Valuation

variable {K : Type} [Field K] [NumberField K]
variable (n : ℕ) (Tz Y T Xs : Set (HeightOneSpectrum (𝓞 K))) [Finite ↥Xs]

/-- **The vector of orders at the named places of a confined unit supported inside a set of
places.** -/
noncomputable def confinedSupportOrd :
    Additive ↥(confinedSupportUnits n Tz Y T) →+ (↥Xs →₀ ℤ) :=
  (confinedOrd n Tz Y Xs).comp
    (MonoidHom.toAdditive (confinedSupportUnits n Tz Y T).subtype)

@[simp]
theorem confinedSupportOrd_apply (u : Additive ↥(confinedSupportUnits n Tz Y T)) (y : ↥Xs) :
    confinedSupportOrd n Tz Y T Xs u y
      = ord K (y : HeightOneSpectrum (𝓞 K))
        ((((u.toMul : ↥(confinedSupportUnits n Tz Y T)) :
          ↥(confinedUnits K n Tz Y)) : Kˣ) : K) := rfl

/-- **The confined units supported inside a set of places whose orders at the named places all
vanish.** -/
def confinedSupportSUnits : Subgroup ↥(confinedSupportUnits n Tz Y T) where
  carrier := {x | ∀ y : ↥Xs, ord K (y : HeightOneSpectrum (𝓞 K))
    (((x : ↥(confinedSupportUnits n Tz Y T)) : ↥(confinedUnits K n Tz Y)) : Kˣ) = 0}
  mul_mem' {x y} hx hy z := by
    show ord K (z : HeightOneSpectrum (𝓞 K))
      ((((x : ↥(confinedSupportUnits n Tz Y T)) : ↥(confinedUnits K n Tz Y)) : Kˣ)
        * (((y : ↥(confinedSupportUnits n Tz Y T)) : ↥(confinedUnits K n Tz Y)) : Kˣ) : Kˣ) = 0
    rw [Units.val_mul, ord_mul _ (Units.ne_zero _) (Units.ne_zero _), hx z, hy z, add_zero]
  one_mem' z := by
    show ord K (z : HeightOneSpectrum (𝓞 K)) (((1 : Kˣ) : K)) = 0
    rw [Units.val_one, ord_one]
  inv_mem' {x} hx z := by
    show ord K (z : HeightOneSpectrum (𝓞 K))
      (((((x : ↥(confinedSupportUnits n Tz Y T)) : ↥(confinedUnits K n Tz Y)) : Kˣ)⁻¹ : Kˣ) : K) = 0
    rw [Units.val_inv_eq_inv_val, ord_inv, hx z, neg_zero]

/-- **The kernel of the vector of orders is the subgroup of units without order at the named
places.** -/
theorem mem_confinedSupportSUnits_iff (a : ↥(confinedSupportUnits n Tz Y T)) :
    a ∈ confinedSupportSUnits n Tz Y T Xs ↔
      confinedSupportOrd n Tz Y T Xs (Additive.ofMul a) = 0 := by
  refine ⟨fun h => Finsupp.ext fun y => ?_, fun h y => ?_⟩
  · rw [confinedSupportOrd_apply]
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    exact h y
  · have h2 := congrArg (fun z : ↥Xs →₀ ℤ => z y) h
    simpa using h2

variable {k : Type} [Field k] [Algebra k K]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y]
  [IsGaloisStablePlaces k K T] [IsGaloisStablePlaces k K Xs]

/-- **The vector of orders at the named places is equivariant.** -/
theorem confinedSupportOrd_smul_apply (σ : Gal(K/k))
    (a : ↥(confinedSupportUnits n Tz Y T)) (y : ↥Xs) :
    confinedSupportOrd n Tz Y T Xs (Additive.ofMul (σ • a)) y
      = confinedSupportOrd n Tz Y T Xs (Additive.ofMul a) (σ⁻¹ • y) :=
  ord_coe_smul_confinedUnits n Tz Y σ (a : ↥(confinedUnits K n Tz Y))
    (y : HeightOneSpectrum (𝓞 K))

/-- **The units without order at the named places are carried into themselves by the Galois
group.** -/
instance isStableSubgroup_confinedSupportSUnits :
    IsStableSubgroup Gal(K/k) (confinedSupportSUnits n Tz Y T Xs) where
  smul_mem σ {a} ha := fun y =>
    (confinedSupportOrd_smul_apply n Tz Y T Xs σ a y).trans (ha (σ⁻¹ • y))

end Valuation

/-! ### A finite set of places the vector of orders is already onto from -/

section Exists

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
variable (n : ℕ) (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K))) [Finite ↥Xs]

/-- **The vector of orders is already onto from the confined units supported inside a finite stable
set of places.**

Only finitely many places are named, so only finitely many units are needed to realise every
prescribed system of orders — one for each named place, taking order one there and none elsewhere
in the named set.  Each of them has a zero or a pole at finitely many places of the field, so the
places they use, together with the named ones and all their translates, form a finite stable set;
and every prescription is realised by a product of powers of those finitely many units, which is
supported inside it. -/
theorem exists_finite_stable_surjective_confinedSupportOrd
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs)) :
    ∃ (T : Set (HeightOneSpectrum (𝓞 K))) (_ : T.Finite) (_ : IsGaloisStablePlaces k K T),
      Xs ⊆ T ∧ Function.Surjective (confinedSupportOrd n Tz Y T Xs) := by
  classical
  choose x hx using fun y : ↥Xs => hsurj (Finsupp.single y 1)
  set T₀ : Set (HeightOneSpectrum (𝓞 K)) := Xs ∪ ⋃ y : ↥Xs,
    {v | ord K v ((((x y).toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) ≠ 0} with hT₀
  have hT₀fin : T₀.Finite :=
    (Set.toFinite Xs).union (Set.finite_iUnion fun y : ↥Xs =>
      Filter.eventually_cofinite.1 (ord_finite (R := 𝓞 K) (K := K)
        ((((x y).toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K)))
  have hXsT : Xs ⊆ stableHull k K T₀ :=
    Set.Subset.trans Set.subset_union_left (subset_stableHull k K T₀)
  refine ⟨stableHull k K T₀, stableHull_finite (k := k) hT₀fin, inferInstance, hXsT, fun d => ?_⟩
  have hxmem : ∀ y : ↥Xs, ((x y).toMul : ↥(confinedUnits K n Tz Y))
      ∈ confinedSupportUnits n Tz Y (stableHull k K T₀) := by
    intro y v hv
    by_contra hcon
    exact hv (subset_stableHull k K T₀ (Set.mem_union_right _ (Set.mem_iUnion.2 ⟨y, hcon⟩)))
  have hval : ∀ y : ↥Xs, confinedSupportOrd n Tz Y (stableHull k K T₀) Xs
      (Additive.ofMul (⟨((x y).toMul : ↥(confinedUnits K n Tz Y)), hxmem y⟩ :
        ↥(confinedSupportUnits n Tz Y (stableHull k K T₀)))) = Finsupp.single y 1 :=
    fun y => hx y
  refine ⟨∑ y ∈ d.support, d y • Additive.ofMul
    (⟨((x y).toMul : ↥(confinedUnits K n Tz Y)), hxmem y⟩ :
      ↥(confinedSupportUnits n Tz Y (stableHull k K T₀))), ?_⟩
  calc confinedSupportOrd n Tz Y (stableHull k K T₀) Xs (∑ y ∈ d.support, d y • Additive.ofMul
        (⟨((x y).toMul : ↥(confinedUnits K n Tz Y)), hxmem y⟩ :
          ↥(confinedSupportUnits n Tz Y (stableHull k K T₀))))
      = ∑ y ∈ d.support, Finsupp.single y (d y) := by
        rw [_root_.map_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [AddMonoidHom.map_zsmul, hval y, Finsupp.smul_single, smul_eq_mul, mul_one]
    _ = d := Finsupp.sum_single d

end Exists

/-! ### The descent run inside the units for a finite set -/

section Descent

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
variable (n : ℕ) (Tz Y T Xs : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite ↥Xs] [DecidableEq ↥Xs]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y]
  [IsGaloisStablePlaces k K T] [IsGaloisStablePlaces k K Xs]
variable {C : Type} [CommGroup C] [MulDistribMulAction Gal(K/k) C]

/-- **An invariant radicand of confined units whose value is the prescribed one at each of finitely
many named places lying in distinct orbits, the obstruction being asked to vanish only with
coefficients in the units for a finite set of places.**

The descent is run inside the confined units supported in that set, where the vector of orders is
still onto; the inclusion of the subgroup commutes with the reading, so the radicand it produces
has the prescribed orders at the named places once it is read as a confined radicand, and it is
invariant because the inclusion is equivariant. -/
theorem exists_invariant_confinedTensorVal_eq_of_named_of_support_class
    (hsurj : Function.Surjective (confinedSupportOrd n Tz Y T Xs))
    (hδ : ∀ (t : Additive ↥(confinedSupportUnits n Tz Y T) ⊗[ℤ] Additive C)
      (ht : ∀ σ : Gal(K/k), tensorVal C (confinedSupportOrd n Tz Y T Xs) (σ • t)
        = tensorVal C (confinedSupportOrd n Tz Y T Xs) t),
      tensorInvariantClass C (confinedSupportOrd n Tz Y T Xs)
        (confinedSupportSUnits n Tz Y T Xs) hsurj
        (mem_confinedSupportSUnits_iff n Tz Y T Xs) ht = 0)
    {ι : Type} [Fintype ι] (w : ι → ↥Xs) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Gal(K/k) (w μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → w μ ∉ orbit Gal(K/k) (w ν)) :
    ∃ s : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C,
      (∀ σ : Gal(K/k), σ • s = s) ∧
      (∀ μ : ι, tensorVal C (confinedOrd n Tz Y Xs) s (w μ) = Additive.ofMul (V μ)) ∧
      ∀ z : ↥Xs, (∀ μ : ι, z ∉ orbit Gal(K/k) (w μ)) →
        tensorVal C (confinedOrd n Tz Y Xs) s z = 0 := by
  obtain ⟨s, hs, hsval, hszero⟩ := exists_invariant_tensorVal_eq_of_named_of_class
    (confinedSupportOrd n Tz Y T Xs) (confinedSupportSUnits n Tz Y T Xs) hsurj
    (mem_confinedSupportSUnits_iff n Tz Y T Xs) (confinedSupportOrd_smul_apply n Tz Y T Xs)
    hδ w V hV hdisj
  have hres : tensorVal C (confinedOrd n Tz Y Xs)
      (tensorSubIncl C (confinedSupportUnits n Tz Y T) s)
      = tensorVal C (confinedSupportOrd n Tz Y T Xs) s :=
    tensorVal_tensorSubIncl C (confinedOrd n Tz Y Xs) (confinedSupportOrd n Tz Y T Xs)
      (fun _ => rfl) s
  refine ⟨tensorSubIncl C (confinedSupportUnits n Tz Y T) s, fun σ => ?_, fun μ => ?_,
    fun z hz => ?_⟩
  · rw [← tensorSubIncl_smul, hs σ]
  · rw [hres]
    exact hsval μ
  · rw [hres]
    exact hszero z hz

end Descent

/-! ### The units for a finite set of places are finitely generated -/

section Finite

variable {K : Type} [Field K] [NumberField K]
variable (n : ℕ) (Tz Y T Xs : Set (HeightOneSpectrum (𝓞 K)))

/-- **A subgroup of a finitely generated abelian group is finitely generated.** -/
theorem module_finite_additive_subgroup {G : Type*} [CommGroup G]
    [Module.Finite ℤ (Additive G)] (H : Subgroup G) : Module.Finite ℤ (Additive ↥H) := by
  refine Module.Finite.of_injective
    (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive H.subtype)) fun x y h => ?_
  have h2 : ((x.toMul : ↥H) : G) = ((y.toMul : ↥H) : G) := h
  exact Additive.toMul.injective (Subtype.ext h2)

/-- **The confined units supported inside a set of places are units for that set.** -/
def confinedSupportToSUnits : ↥(confinedSupportUnits n Tz Y T) →* ↥(sUnits K T) :=
  MonoidHom.codRestrict
    (((confinedUnits K n Tz Y).subtype).comp (confinedSupportUnits n Tz Y T).subtype)
    (sUnits K T) fun x => x.2

/-- **A confined unit supported inside a set of places is determined by the unit it is.** -/
theorem confinedSupportToSUnits_injective :
    Function.Injective (confinedSupportToSUnits n Tz Y T) := by
  intro x y h
  have h1 : ((confinedSupportToSUnits n Tz Y T x : ↥(sUnits K T)) : Kˣ)
      = ((confinedSupportToSUnits n Tz Y T y : ↥(sUnits K T)) : Kˣ) := by rw [h]
  exact Subtype.ext (Subtype.ext h1)

/-- **The confined units supported inside a finite set of places are finitely generated.** -/
theorem module_finite_confinedSupportUnits (hT : T.Finite) :
    Module.Finite ℤ (Additive ↥(confinedSupportUnits n Tz Y T)) := by
  haveI : Module.Finite ℤ (Additive ↥(sUnits K T)) := module_finite_sUnits T hT
  refine Module.Finite.of_injective (AddMonoidHom.toIntLinearMap
    (MonoidHom.toAdditive (confinedSupportToSUnits n Tz Y T))) fun x y h => ?_
  have h2 : confinedSupportToSUnits n Tz Y T x.toMul
      = confinedSupportToSUnits n Tz Y T y.toMul := h
  exact Additive.toMul.injective (confinedSupportToSUnits_injective n Tz Y T h2)

/-- **The coefficients of the obstruction, for a finite set of places, are finitely
generated.** -/
theorem module_finite_confinedSupportSUnits (hT : T.Finite) :
    Module.Finite ℤ (Additive ↥(confinedSupportSUnits n Tz Y T Xs)) :=
  haveI := module_finite_confinedSupportUnits n Tz Y T hT
  module_finite_additive_subgroup _

/-- **The coefficients of the obstruction, for a finite set of places, are spanned by finitely many
units.**  This is the shape the count of a cohomology class asks its coefficients in. -/
theorem exists_spanning_confinedSupportSUnits (hT : T.Finite) :
    ∃ (d : ℕ) (b : Fin d → Additive ↥(confinedSupportSUnits n Tz Y T Xs)),
      Submodule.span ℤ (Set.range b) = ⊤ :=
  haveI := module_finite_confinedSupportSUnits n Tz Y T Xs hT
  Module.Finite.exists_fin

end Finite

end InverseGalois.CFT

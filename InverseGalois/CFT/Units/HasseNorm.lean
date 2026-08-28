/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CyclicIndex
import InverseGalois.CFT.Units.FirstInequality
import InverseGalois.CFT.Tate.Galois
import InverseGalois.CFT.NormSubgroup

/-!
# The norm theorem for a cyclic extension of number fields

The units of a number field sit inside its ideles as the principal ideles, and the quotient is the
idele class group.  For a cyclic extension all three groups carry the action of a generator of the
Galois group, and the inclusion and the projection are equivariant, so they form a short exact
sequence of modules over a cyclic group.  The Tate hexagon of that sequence relates the norms in the
units of the field to the norms in the ideles.

The two counts already available pin down the Tate groups of the idele class group.  Its Herbrand
quotient is the degree of the extension, and the order of its zeroth Tate group is the index of the
principal ideles together with the norms, which is again the degree.  Dividing, the group `Ĥ⁻¹` of
the idele class group is trivial.  Exactness of the hexagon at `Ĥ⁰` of the units then makes the map
`Ĥ⁰(Kˣ) → Ĥ⁰(I_K)` injective, and that injectivity says exactly that a unit of the base field which
is the norm of an idele is already the norm of a unit of the extension.

Translating out of the Tate formalism uses that the Tate norm operator on the units of the top field
is the field norm, which is the product of the conjugates enumerated by the powers of a generator.

## Main definitions

* `InverseGalois.CFT.ideleClassSES`: the short exact sequence of the units of the field, the ideles,
  and the idele classes.

## Main results

* `InverseGalois.CFT.card_tateHm1_ideleClassAut_eq_one`: the group `Ĥ⁻¹` of the idele class group of
  a cyclic extension is trivial.
* `InverseGalois.CFT.mem_range_normHom_globalUnitsAut`: a unit of the top field fixed by a generator
  whose principal idele is a norm of ideles is a norm of units.
* `InverseGalois.CFT.mem_normSubgroup_of_mem_range_ideleNorm`: **the norm theorem**, that a unit of
  the base field whose principal idele is the norm of an idele is the norm of a unit of the
  extension.

## Tags

Hasse norm theorem, idele class group, Tate cohomology, cyclic extension
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open IsDedekindDomain NumberField

namespace InverseGalois.CFT

/-! ### The short exact sequence of the idele class group -/

section Sequence

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {σ : Gal(K/k)} {n : ℕ}

/-- **The short exact sequence of the units of the field, the ideles, and the idele classes.**  The
diagonal embedding of the units is injective and equivariant for the action of a field automorphism,
so the idele classes are its cokernel. -/
noncomputable abbrev ideleClassSES (hσ : σ ^ n = 1) :
    TateSES n (Additive Kˣ) ↥(idele K) (↥(idele K) ⧸ (ideleDiag K).range) :=
  tateSESOfInjective (σA := globalUnitsAut σ) (σB := ideleAut (k := k) σ)
    (globalUnitsAut_pow_eq_one hσ) (ideleAut_pow_eq_one σ hσ) (ideleDiag K)
    (fun a => (ideleAut_ideleDiag σ a).symm) (ideleDiag_injective K)

omit [NumberField k] [IsGalois k K] in
/-- The automorphism of the quotient term of the sequence is the automorphism of the idele class
group. -/
theorem ideleClassSES_σC (hσ : σ ^ n = 1) :
    (ideleClassSES hσ).σC = ideleClassAut (k := k) σ := rfl

end Sequence

/-! ### The vanishing of the first Tate group of the idele class group -/

section Vanishing

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (σ : Gal(K/k)) {n : ℕ} (hn : Nat.card Gal(K/k) = n) [NeZero n]
  (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)

include hn hgen

/-- **The group `Ĥ⁻¹` of the idele class group of a cyclic extension is trivial.**  Its Herbrand
quotient is the degree of the extension and the order of `Ĥ⁰` is the index of the principal ideles
together with the norms, which is the degree as well. -/
theorem card_tateHm1_ideleClassAut_eq_one :
    Nat.card (tateHm1 (ideleClassAut (k := k) σ) n) = 1 := by
  haveI : IsCyclic Gal(K/k) := ⟨⟨σ, hgen⟩⟩
  have hq : herbrand (ideleClassAut (k := k) σ) n = n :=
    herbrand_ideleClassAut_eq_degree σ hn hgen
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hne : herbrand (ideleClassAut (k := k) σ) n ≠ 0 := by rw [hq]; exact hnq
  obtain ⟨h0, h1⟩ := finite_tate_of_herbrand_ne_zero _ n hne
  have hcard0 : Nat.card (tateH0 (ideleClassAut (k := k) σ) n) = n := by
    rw [card_tateH0_ideleClassAut hgen hn, index_ideleDiag_sup_ideleNorm_eq_card, hn]
  have hmpos : 0 < Nat.card (tateHm1 (ideleClassAut (k := k) σ) n) := Nat.card_pos
  have hmq : (Nat.card (tateHm1 (ideleClassAut (k := k) σ) n) : ℚ) ≠ 0 := by
    exact_mod_cast hmpos.ne'
  rw [herbrand, hcard0, div_eq_iff hmq] at hq
  have hq' : n = n * Nat.card (tateHm1 (ideleClassAut (k := k) σ) n) := by exact_mod_cast hq
  exact Nat.eq_of_mul_eq_mul_left hnpos (by rw [mul_one]; exact hq'.symm)

/-- The group `Ĥ⁻¹` of the idele class group of a cyclic extension has at most one element. -/
theorem subsingleton_tateHm1_ideleClassAut :
    Subsingleton (tateHm1 (ideleClassAut (k := k) σ) n) :=
  (Nat.card_eq_one_iff_unique.mp (card_tateHm1_ideleClassAut_eq_one σ hn hgen)).1

end Vanishing

/-! ### The norm theorem -/

section Hasse

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (σ : Gal(K/k)) {n : ℕ} (hn : Nat.card Gal(K/k) = n) [NeZero n]
  (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)

include hn hgen

/-- **The norm theorem in cohomological form.**  Since `Ĥ⁻¹` of the idele class group vanishes,
exactness of the Tate hexagon at `Ĥ⁰` of the units makes the map to `Ĥ⁰` of the ideles injective: a
unit of the top field fixed by a generator whose principal idele is a norm of ideles is itself a
norm of units. -/
theorem mem_range_normHom_globalUnitsAut (a : Additive Kˣ)
    (ha : globalUnitsAut (k := k) σ a = a)
    (h : ideleDiag K a ∈ (normHom (ideleAut (k := k) σ) n).range) :
    a ∈ (normHom (globalUnitsAut (k := k) σ) n).range := by
  have hσ : σ ^ n = 1 := by rw [← hn]; exact pow_card_eq_one'
  set S := ideleClassSES (k := k) hσ with hS
  have hker : tateH0.mk (globalUnitsAut (k := k) σ) n a ha ∈ S.alpha0.ker := by
    rw [AddMonoidHom.mem_ker]
    show tateH0.map n S.f S.hf _ = 0
    rw [tateH0.map_mk]
    exact (tateH0.mk_eq_zero_iff _ _).mpr h
  rw [← S.range_delta1_eq_ker_alpha0] at hker
  obtain ⟨c, hc⟩ := hker
  have hc0 : c = 0 :=
    @Subsingleton.elim _ (subsingleton_tateHm1_ideleClassAut σ hn hgen) c 0
  rw [hc0, map_zero] at hc
  exact (tateH0.mk_eq_zero_iff a ha).mp hc.symm

/-- A unit of the base field whose principal idele is the norm of an idele has image in the top
field a norm of units. -/
theorem mem_range_normHom_globalUnitsComap (a : Additive kˣ)
    (h : ideleDiag k a ∈ (ideleNorm k K).range) :
    globalUnitsComap k K a ∈ (normHom (globalUnitsAut (k := k) σ) n).range := by
  obtain ⟨x, hx⟩ := h
  refine mem_range_normHom_globalUnitsAut σ hn hgen _
    ((mem_range_globalUnitsComap_iff _).mp ⟨a, rfl⟩ σ) ⟨x, ?_⟩
  rw [← ideleComap_ideleNorm_eq_normHom k K hgen hn, hx, ideleComap_ideleDiag]

/-- **The norm theorem for a cyclic extension of number fields.**  A unit of the base field whose
principal idele is the norm of an idele is the field norm of a unit of the extension.  The Tate norm
operator of a generator is the product of the conjugates, which is the field norm. -/
theorem exists_norm_eq_of_ideleDiag_mem_range (a : kˣ)
    (h : ideleDiag k (Additive.ofMul a) ∈ (ideleNorm k K).range) :
    ∃ b : Kˣ, Algebra.norm k (b : K) = (a : k) := by
  obtain ⟨b, hb⟩ := mem_range_normHom_globalUnitsComap σ hn hgen (Additive.ofMul a) h
  subst hn
  refine ⟨Additive.toMul b, ?_⟩
  have hprod : Additive.ofMul (∏ i ∈ Finset.range (Nat.card Gal(K/k)),
      ((galUnits σ) ^ i) (Additive.toMul b)) = globalUnitsComap k K (Additive.ofMul a) := by
    rw [← normHom_ofMul (galUnits σ) (Nat.card Gal(K/k)) (Additive.toMul b)]
    exact hb
  have hb' : (∏ i ∈ Finset.range (Nat.card Gal(K/k)), ((unitsAut σ) ^ i) (Additive.toMul b))
      = Units.map (algebraMap k K).toMonoidHom a := hprod
  have hcoe := congrArg Units.val hb'
  rw [coe_prod_range_unitsAut σ hgen (Additive.toMul b)] at hcoe
  exact FaithfulSMul.algebraMap_injective k K hcoe

/-- A unit of the base field whose principal idele is the norm of an idele lies in the norm
subgroup. -/
theorem mem_normSubgroup_of_ideleDiag_mem_range (a : kˣ)
    (h : ideleDiag k (Additive.ofMul a) ∈ (ideleNorm k K).range) :
    a ∈ normSubgroup k K :=
  (mem_normSubgroup_iff a).mpr (exists_norm_eq_of_ideleDiag_mem_range σ hn hgen a h)

end Hasse

section Cyclic

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] [IsCyclic Gal(K/k)]

/-- **The norm theorem for a cyclic extension of number fields.**  A unit of the base field whose
principal idele is the norm of an idele lies in the norm subgroup of the extension. -/
theorem mem_normSubgroup_of_mem_range_ideleNorm (a : kˣ)
    (h : ideleDiag k (Additive.ofMul a) ∈ (ideleNorm k K).range) :
    a ∈ normSubgroup k K := by
  obtain ⟨σ, hgen⟩ := IsCyclic.exists_generator (α := Gal(K/k))
  haveI : NeZero (Nat.card Gal(K/k)) := ⟨Nat.card_pos.ne'⟩
  exact mem_normSubgroup_of_ideleDiag_mem_range σ rfl hgen a h

end Cyclic

end InverseGalois.CFT

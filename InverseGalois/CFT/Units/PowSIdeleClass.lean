/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.PowerCriterion
import InverseGalois.CFT.SubgroupIndex
import InverseGalois.CFT.Units.IdeleClass
import InverseGalois.CFT.Units.PowIdele
import InverseGalois.CFT.Units.SUnitIndex
import InverseGalois.CFT.Units.SUnitValuation

/-!
# The principal ideles inside the ideles of a set of places

The counting behind the algebraic proof of the second inequality compares two subgroups of the
ideles of a number field: the ideles of a set of places, and the subgroup of those which are local
`p`-th powers at the infinite places and at the first of the two sets.  Their relative index is
known, and one wants the index of the smaller one once the principal ideles are thrown in.

That is exactly what the splitting of a relative index along a third subgroup computes, the third
subgroup being the principal ideles.  Two intersections have to be identified.  The ideles of the
set of places meet the principal ideles in the diagonal image of the units of that set, because a
principal idele is a unit of the valuation ring at a place exactly when the element has order zero
there.  The subgroup of local powers meets the principal ideles in the diagonal image of the `p`-th
powers of those units: one inclusion is immediate, and the other is the criterion for an element
which is a local `p`-th power at the infinite places and at the first set, and a unit outside the
two sets, to be a global `p`-th power.

Finally the ideles of the set of places together with the principal ideles are all the ideles, the
first set carrying the ideal classes.  Both indices of the splitting are therefore known, and the
index of the local powers together with the principal ideles inside all the ideles follows.

## Main results

* `InverseGalois.CFT.mem_sIdele`, `InverseGalois.CFT.mem_powSIdele`: membership in the two
  subgroups, place by place.
* `InverseGalois.CFT.sIdele_sup_range_fullDiag`: **the ideles of the set of places together with
  the principal ideles are all the ideles.**
* `InverseGalois.CFT.sIdele_inf_range_fullDiag`: **the principal ideles among the ideles of the set
  of places are the units of that set.**
* `InverseGalois.CFT.powSIdele_inf_range_fullDiag`: **the principal ideles among the local `p`-th
  powers are the `p`-th powers of the units of that set.**
* `InverseGalois.CFT.relIndex_map_powMonoidHom_sUnits`: the relative index of the `p`-th powers of
  the units of a finite set of places.
* `InverseGalois.CFT.relIndex_powSIdele_sup_range_fullDiag`: **the index of the local `p`-th powers
  together with the principal ideles inside all the ideles.**

## Tags

number field, idele, S-unit, index, principal idele, second inequality
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### Membership in the two subgroups -/

section Membership

variable {K : Type*} [Field K] [NumberField K] (S T : Set (HeightOneSpectrum (𝓞 K)))
  [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]

/-- An element of the product of the local unit groups is an idele of the two sets of places
exactly when it is a unit of the valuation ring outside them. -/
theorem mem_sIdele {x : FullIdele K} :
    x ∈ sIdele S T ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → unitVal (x.2 v) = 0 := by
  rw [sIdele, AddSubgroup.mem_prod]
  constructor
  · rintro ⟨-, h⟩ v hvS hvT
    have hv : x.2 v ∈ adicSIdele S T v := h v (Set.mem_univ v)
    rwa [adicSIdele_of_notMem S T hvS, adicSUnits_of_notMem T hvT, AddMonoidHom.mem_ker] at hv
  · intro h
    refine ⟨fun w _ => trivial, fun v _ => ?_⟩
    show x.2 v ∈ adicSIdele S T v
    by_cases hvS : v ∈ S
    · rw [adicSIdele_of_mem S T hvS]
      trivial
    by_cases hvT : v ∈ T
    · rw [adicSIdele_of_notMem S T hvS, adicSUnits_of_mem T hvT]
      trivial
    · rw [adicSIdele_of_notMem S T hvS, adicSUnits_of_notMem T hvT, AddMonoidHom.mem_ker]
      exact h v hvS hvT

/-- An element of the product of the local unit groups lies in the subgroup carrying the `p`-th
powers exactly when it is a local `p`-th power at every infinite place and at every place of the
first set, and a unit of the valuation ring outside the two sets. -/
theorem mem_powSIdele {p : ℕ} {x : FullIdele K} :
    x ∈ powSIdele S T p ↔
      (∀ w : InfinitePlace K, ∃ z : w.Completionˣ, z ^ p = Additive.toMul (x.1 w)) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∈ S →
          ∃ z : (v.adicCompletion K)ˣ, z ^ p = Additive.toMul (x.2 v)) ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → unitVal (x.2 v) = 0 := by
  rw [powSIdele, AddSubgroup.mem_prod]
  constructor
  · rintro ⟨hinf, hfin⟩
    refine ⟨fun w => ?_, fun v hv => ?_, fun v hvS hvT => ?_⟩
    · have hw : x.1 w ∈ infinitePow p w := hinf w (Set.mem_univ w)
      obtain ⟨z, hz⟩ := (Additive.mem_toAddSubgroup _ _).mp hw
      exact ⟨z, hz⟩
    · have hv' : x.2 v ∈ adicPowSIdele p S T v := hfin v (Set.mem_univ v)
      rw [adicPowSIdele_of_mem S T p hv] at hv'
      obtain ⟨z, hz⟩ := (Additive.mem_toAddSubgroup _ _).mp hv'
      exact ⟨z, hz⟩
    · have hv' : x.2 v ∈ adicPowSIdele p S T v := hfin v (Set.mem_univ v)
      rwa [adicPowSIdele_of_notMem S T p hvS, adicSUnits_of_notMem T hvT,
        AddMonoidHom.mem_ker] at hv'
  · rintro ⟨hinf, hS, hout⟩
    refine ⟨fun w _ => ?_, fun v _ => ?_⟩
    · show x.1 w ∈ infinitePow p w
      obtain ⟨z, hz⟩ := hinf w
      exact (Additive.mem_toAddSubgroup _ _).mpr ⟨z, hz⟩
    · show x.2 v ∈ adicPowSIdele p S T v
      by_cases hvS : v ∈ S
      · rw [adicPowSIdele_of_mem S T p hvS]
        obtain ⟨z, hz⟩ := hS v hvS
        exact (Additive.mem_toAddSubgroup _ _).mpr ⟨z, hz⟩
      by_cases hvT : v ∈ T
      · rw [adicPowSIdele_of_notMem S T p hvS, adicSUnits_of_mem T hvT]
        trivial
      · rw [adicPowSIdele_of_notMem S T p hvS, adicSUnits_of_notMem T hvT, AddMonoidHom.mem_ker]
        exact hout v hvS hvT

/-- The subgroup carrying the `p`-th powers sits inside the ideles of the two sets of places. -/
theorem powSIdele_le_sIdele (p : ℕ) : powSIdele S T p ≤ sIdele S T := fun _ hx =>
  (mem_sIdele S T).mpr ((mem_powSIdele S T).mp hx).2.2

/-- The ideles of two finite sets of places are ideles. -/
theorem sIdele_le_idele (hS : S.Finite) (hT : T.Finite) : sIdele S T ≤ idele K := by
  intro x hx
  rw [mem_idele, Filter.eventually_cofinite]
  refine ((hS.union hT).subset fun v hv => ?_)
  by_contra hc
  exact hv ((mem_sIdele S T).mp hx v (fun h => hc (Or.inl h)) fun h => hc (Or.inr h))

end Membership

/-! ### The principal ideles -/

section Diagonal

variable {K : Type*} [Field K] [NumberField K] (S T : Set (HeightOneSpectrum (𝓞 K)))
  [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]

/-- **The ideles of the two sets of places together with the principal ideles are all the
ideles**, the first set carrying the ideal classes: an idele is corrected by a principal one into
one that is a unit of the valuation ring outside that set. -/
theorem sIdele_sup_range_fullDiag (hS : S.Finite) (hT : T.Finite)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ S, ord K v (a : K) = m v) :
    sIdele S T ⊔ (fullDiag K).range = idele K := by
  refine le_antisymm (sup_le (sIdele_le_idele S T hS hT) ?_) fun x hx => ?_
  · rintro _ ⟨a, rfl⟩
    exact fullDiag_mem_idele K a
  obtain ⟨a, ha⟩ := hrepr (fun v => -unitVal (x.2 v)) (by
    filter_upwards [(mem_idele K).mp hx] with v hv
    rw [hv, neg_zero])
  refine AddSubgroup.mem_sup.mpr ⟨x - fullDiag K (Additive.ofMul a), ?_,
    fullDiag K (Additive.ofMul a), ⟨_, rfl⟩, by abel⟩
  refine (mem_sIdele S T).mpr fun v hvS _ => ?_
  show unitVal (x.2 v - (fullDiag K (Additive.ofMul a)).2 v) = 0
  rw [map_sub, fullDiag_snd, unitVal_adicUnitHom]
  show unitVal (x.2 v) - -ord K v (a : K) = 0
  rw [ha v hvS]
  ring

/-- **The principal ideles among the ideles of the two sets of places are the units of those
places**: the diagonal image of an element of the field is a unit of the valuation ring at a place
exactly when the element has order zero there. -/
theorem sIdele_inf_range_fullDiag :
    sIdele S T ⊓ (fullDiag K).range
      = AddSubgroup.map (fullDiag K) (Subgroup.toAddSubgroup (sUnits K (S ∪ T))) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hx, a, rfl⟩
    refine ⟨a, (Additive.mem_toAddSubgroup _ _).mpr (mem_sUnits.mpr fun v hv => ?_), rfl⟩
    have h := (mem_sIdele S T).mp hx v (fun h => hv (Or.inl h)) fun h => hv (Or.inr h)
    rw [fullDiag_snd, unitVal_adicUnitHom, neg_eq_zero] at h
    exact h
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨(mem_sIdele S T).mpr fun v hvS hvT => ?_, a, rfl⟩
    rw [fullDiag_snd, unitVal_adicUnitHom, neg_eq_zero]
    exact mem_sUnits.mp ((Additive.mem_toAddSubgroup _ _).mp ha) v fun h => h.elim hvS hvT

end Diagonal

/-! ### The principal ideles that are local powers -/

section Power

variable {K : Type*} [Field K] [NumberField K] {S T : Set (HeightOneSpectrum (𝓞 K))}
  [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] {p : ℕ}

/-- **The principal ideles among the ideles that are local `p`-th powers at the infinite places and
at the first set of places are the `p`-th powers of the units of the two sets.**  One inclusion is
the compatibility of the diagonal with taking powers; the other is the criterion for an element
which is a local `p`-th power at the infinite places and at the first set, and a unit of the
valuation ring outside the two sets, to be a global `p`-th power. -/
theorem powSIdele_inf_range_fullDiag (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hS : S.Finite) (hT : T.Finite) (hTS : ∀ v ∈ T, v ∉ S)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ S, ord K v (a : K) = m v)
    (hsurj : ∀ c : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ,
      (∀ v ∈ T, Valued.v ((c v : v.adicCompletion K)) = 1) →
      ∃ u : Kˣ, u ∈ sUnits K S ∧ ∀ v ∈ T, ∃ z : (v.adicCompletion K)ˣ,
        adicUnitHom v u = c v * z ^ p) :
    powSIdele S T p ⊓ (fullDiag K).range
      = AddSubgroup.map (fullDiag K)
          (Subgroup.toAddSubgroup (Subgroup.map (powMonoidHom p : Kˣ →* Kˣ)
            (sUnits K (S ∪ T)))) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hx, a, rfl⟩
    obtain ⟨hinf, hSpow, hout⟩ := (mem_powSIdele S T).mp hx
    set b : Kˣ := Additive.toMul a with hb
    have hbinf : ∀ w : InfinitePlace K,
        ∃ c : w.Completion, c ^ p = algebraMap K w.Completion (b : K) := by
      intro w
      obtain ⟨z, hz⟩ := hinf w
      refine ⟨(z : w.Completion), ?_⟩
      rw [← Units.val_pow_eq_pow_val, hz]
      exact congrArg Units.val (congrArg Additive.toMul (fullDiag_fst K a w))
    have hbS : ∀ v ∈ S, ∃ c : v.adicCompletion K,
        c ^ p = algebraMap K (v.adicCompletion K) (b : K) := by
      intro v hv
      obtain ⟨z, hz⟩ := hSpow v hv
      refine ⟨(z : v.adicCompletion K), ?_⟩
      rw [← Units.val_pow_eq_pow_val, hz]
      exact congrArg Units.val (congrArg Additive.toMul (fullDiag_snd K a v))
    have hord : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → ord K v (b : K) = 0 := by
      intro v hvS hvT
      have h := hout v hvS hvT
      rw [fullDiag_snd, unitVal_adicUnitHom, neg_eq_zero] at h
      exact h
    obtain ⟨y, hy⟩ := exists_pow_eq_of_forall_localPow hp hζ hS hT hTS hpS hrepr hsurj hbinf hbS
      fun v hvS hvT => (valuation_eq_one_iff_ord_eq_zero v (Units.ne_zero b)).mpr (hord v hvS hvT)
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, zero_pow hp.ne_zero] at hy
      exact (Units.ne_zero b) hy.symm
    refine ⟨a, (Additive.mem_toAddSubgroup _ _).mpr ⟨Units.mk0 y hy0, ?_, ?_⟩, rfl⟩
    · refine mem_sUnits.mpr fun v hv => ?_
      have hpo : (p : ℤ) * ord K v y = 0 := by
        rw [← ord_pow v hy0 p]
        show ord K v (y ^ p) = 0
        rw [hy]
        exact hord v (fun h => hv (Or.inl h)) fun h => hv (Or.inr h)
      exact (mul_eq_zero.mp hpo).resolve_left (Int.natCast_ne_zero.mpr hp.ne_zero)
    · exact Units.ext hy
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨u, hu, hup⟩ := (Additive.mem_toAddSubgroup _ _).mp ha
    refine ⟨(mem_powSIdele S T).mpr ⟨fun w => ⟨infiniteUnitHom w u, ?_⟩,
      fun v _ => ⟨adicUnitHom v u, ?_⟩, fun v hvS hvT => ?_⟩, a, rfl⟩
    · rw [← map_pow]
      exact congrArg (infiniteUnitHom w) hup
    · rw [← map_pow]
      exact congrArg (adicUnitHom v) hup
    · rw [fullDiag_snd, unitVal_adicUnitHom, neg_eq_zero]
      have : Additive.toMul a = u ^ p := hup.symm
      rw [this]
      show ord K v (((u : Kˣ) ^ p : Kˣ) : K) = 0
      rw [Units.val_pow_eq_pow_val, ord_pow v u.ne_zero,
        mem_sUnits.mp hu v (fun h => h.elim hvS hvT), mul_zero]

end Power

/-! ### The index -/

section Index

/-- The relative index of the image of a subgroup of a subgroup is the index upstairs. -/
theorem relIndex_map_subtype {G : Type*} [Group G] {H : Subgroup G} (N : Subgroup H) :
    (N.map H.subtype).relIndex H = N.index := by
  show (Subgroup.comap H.subtype (N.map H.subtype)).index = N.index
  rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

/-- The image of the `n`-th powers of a subgroup is the subgroup of `n`-th powers of its
elements. -/
theorem map_subtype_range_powMonoidHom {G : Type*} [CommGroup G] (H : Subgroup G) (n : ℕ) :
    Subgroup.map H.subtype (powMonoidHom n : ↥H →* ↥H).range
      = Subgroup.map (powMonoidHom n : G →* G) H := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨(z : G), z.2, by simp⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨(⟨z, hz⟩ : ↥H) ^ n, ⟨⟨z, hz⟩, rfl⟩, by simp⟩

variable {K : Type*} [Field K] [NumberField K]

/-- **The relative index of the `p`-th powers of the units of a finite set of places** is `p`
raised to the number of places involved, the infinite ones together with that set. -/
theorem relIndex_map_powMonoidHom_sUnits (p : ℕ) [NeZero p] [HasEnoughRootsOfUnity K p]
    (F : Finset (HeightOneSpectrum (𝓞 K))) :
    (Subgroup.map (powMonoidHom p : Kˣ →* Kˣ)
          (sUnits K (F : Set (HeightOneSpectrum (𝓞 K))))).relIndex
        (sUnits K (F : Set (HeightOneSpectrum (𝓞 K))))
      = p ^ (Fintype.card (InfinitePlace K) + F.card) := by
  have hrange : (F : Set (HeightOneSpectrum (𝓞 K)))
      = Set.range ((↑) : ↥F → HeightOneSpectrum (𝓞 K)) := by
    ext v
    simp
  rw [hrange, ← map_subtype_range_powMonoidHom, relIndex_map_subtype,
    index_range_powMonoidHom_sUnits (ι := ((↑) : ↥F → HeightOneSpectrum (𝓞 K))) (n := p)
      Subtype.val_injective, Fintype.card_coe]

/-- **The index of the local `p`-th powers together with the principal ideles inside all the
ideles.**  The relative index of the local `p`-th powers inside the ideles of the two sets of
places splits along the principal ideles into this index and the index of the `p`-th powers of the
units of those places, and both of the latter two are known. -/
theorem relIndex_powSIdele_sup_range_fullDiag {S T : Set (HeightOneSpectrum (𝓞 K))}
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] {p : ℕ} [NeZero p]
    [HasEnoughRootsOfUnity K p] (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (F G : Finset (HeightOneSpectrum (𝓞 K))) (hF : ∀ v, v ∈ F ↔ v ∈ S)
    (hG : ∀ v, v ∈ G ↔ v ∈ S ∪ T)
    (hpF : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ F)
    (hTS : ∀ v ∈ T, v ∉ S)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ S, ord K v (a : K) = m v)
    (hsurj : ∀ c : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ,
      (∀ v ∈ T, Valued.v ((c v : v.adicCompletion K)) = 1) →
      ∃ u : Kˣ, u ∈ sUnits K S ∧ ∀ v ∈ T, ∃ z : (v.adicCompletion K)ˣ,
        adicUnitHom v u = c v * z ^ p) :
    (powSIdele S T p ⊔ (fullDiag K).range).relIndex (idele K)
        * p ^ (Fintype.card (InfinitePlace K) + G.card)
      = p ^ (2 * (Fintype.card (InfinitePlace K) + F.card)) := by
  have hSfin : S.Finite := F.finite_toSet.subset fun v hv => Finset.mem_coe.mpr ((hF v).mpr hv)
  have hTfin : T.Finite :=
    G.finite_toSet.subset fun v hv => Finset.mem_coe.mpr ((hG v).mpr (Or.inr hv))
  have hST : S ∪ T = (G : Set (HeightOneSpectrum (𝓞 K))) := by
    ext v
    exact (hG v).symm
  have hkey := relIndex_sup_mul_relIndex_inf (C := (fullDiag K).range)
    (powSIdele_le_sIdele S T p)
  rw [sIdele_sup_range_fullDiag S T hSfin hTfin hrepr, sIdele_inf_range_fullDiag S T,
    powSIdele_inf_range_fullDiag hp hζ hSfin hTfin hTS hpS hrepr hsurj,
    relIndex_powSIdele_of_isPrimitiveRoot S T hζ F hF hpF,
    AddSubgroup.relIndex_map_map_of_injective _ _ (fullDiag_injective K),
    Subgroup.relIndex_toAddSubgroup, hST, relIndex_map_powMonoidHom_sUnits] at hkey
  exact hkey

end Index

end InverseGalois.CFT

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Norm

/-!
# The exact sequence of the two middle Tate groups

A short exact sequence of representations of a finite group gives a ladder whose rows are the
coinvariants, which are right exact, and the invariants, which are left exact, and whose rungs are
the norms.  The snake of that ladder is a six term exact sequence running from the norm zero
classes in the coinvariants of the three representations to their invariants modulo norms.

The connecting map is built without any choice.  A vector of the middle representation whose norm
comes from the sub has a well defined preimage of that norm, because the map from the sub is
injective, and that preimage is invariant; the vectors of the middle with that property surject
onto the norm zero classes of the quotient, and the recipe kills the kernel of that surjection, so
it descends.

## Main definitions

* `InverseGalois.CFT.Tate.normSource`: the vectors of the middle whose norm comes from the sub.
* `InverseGalois.CFT.Tate.normDescent`: the vector of the sub whose image is that norm.
* `InverseGalois.CFT.Tate.delta`: the connecting map from the Tate group in degree minus one of the
  quotient to the Tate group in degree zero of the sub.

## Main results

* `InverseGalois.CFT.Tate.exact_Hm1_Hm1`, `InverseGalois.CFT.Tate.exact_Hm1_delta`,
  `InverseGalois.CFT.Tate.exact_delta_H0`, `InverseGalois.CFT.Tate.exact_H0_H0`: **the six term
  exact sequence** of a short exact sequence of representations.

## Tags

Tate cohomology, snake lemma, connecting homomorphism, norm map, exact sequence
-/

namespace InverseGalois.CFT.Tate

open Representation

noncomputable section

variable {k G A B C : Type*} [CommRing k] [Group G] [Fintype G]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]

/-! ### The vectors whose norm comes from the sub -/

section Source

/-- The vectors of a representation whose norm lies in the image of a map from another one. -/
def normSource (β : Representation k G B) (f : A →ₗ[k] B) : Submodule k B :=
  (LinearMap.range f).comap (normMap β)

theorem mem_normSource_iff {β : Representation k G B} {f : A →ₗ[k] B} {b : B} :
    b ∈ normSource β f ↔ normMap β b ∈ LinearMap.range f := Iff.rfl

end Source

/-! ### The connecting map -/

section Snake

variable {α : Representation k G A} {β : Representation k G B} {γ : Representation k G C}
  (f : A →ₗ[k] B) (hf : ∀ g, f ∘ₗ α g = β g ∘ₗ f)
  (q : B →ₗ[k] C) (hq : ∀ g, q ∘ₗ β g = γ g ∘ₗ q)
  (hfi : Function.Injective f) (hqs : Function.Surjective q)
  (hex : LinearMap.range f = LinearMap.ker q)

omit [Fintype G] in
include hq hqs in
/-- Every difference of a vector of the quotient and one of its translates is the image of such a
difference in the middle. -/
theorem coinvariantsKer_le_map :
    Coinvariants.ker γ ≤ Submodule.map q (Coinvariants.ker β) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨x, c⟩, rfl⟩
  obtain ⟨b, rfl⟩ := hqs c
  have h : q (β x b) = γ x (q b) := LinearMap.congr_fun (hq x) b
  exact ⟨β x b - b, Submodule.subset_span ⟨⟨x, b⟩, rfl⟩, by rw [map_sub, h]⟩

include hfi in
/-- The vector of the sub whose image is the norm of a vector of the middle. -/
def normDescent : ↥(normSource β f) →ₗ[k] A :=
  (LinearEquiv.ofInjective f hfi).symm.toLinearMap ∘ₗ
    ((normMap β).domRestrict (normSource β f)).codRestrict (LinearMap.range f) fun b => b.2

theorem f_normDescent (b : ↥(normSource β f)) :
    f (normDescent f hfi b) = normMap β (b : B) := by
  show f ((LinearEquiv.ofInjective f hfi).symm
    (⟨normMap β (b : B), b.2⟩ : LinearMap.range f)) = normMap β (b : B)
  exact LinearEquiv.ofInjective_symm_apply f _

include hf in
theorem normDescent_mem_invariants (b : ↥(normSource β f)) :
    normDescent f hfi b ∈ α.invariants := by
  intro x
  refine hfi ?_
  have h1 : f (α x (normDescent f hfi b)) = β x (f (normDescent f hfi b)) :=
    LinearMap.congr_fun (hf x) _
  rw [h1, f_normDescent]
  exact apply_normMap β x _

include hf hfi in
/-- The invariant vector of the sub whose image is the norm of a vector of the middle. -/
def normDescentInv : ↥(normSource β f) →ₗ[k] α.invariants :=
  (normDescent f hfi).codRestrict α.invariants (normDescent_mem_invariants f hf hfi)

@[simp]
theorem normDescentInv_coe (b : ↥(normSource β f)) :
    (normDescentInv f hf hfi b : A) = normDescent f hfi b := rfl

include hf hfi in
/-- The class in the Tate group in degree zero of the sub attached to a vector of the middle whose
norm comes from the sub. -/
def toH0 : ↥(normSource β f) →ₗ[k] H0 α := H0mk α ∘ₗ normDescentInv f hf hfi

theorem toH0_apply (b : ↥(normSource β f)) :
    toH0 f hf hfi b = H0mk α (normDescentInv f hf hfi b) := rfl

include q hq hex in
/-- The class in the Tate group in degree minus one of the quotient attached to a vector of the
middle whose norm comes from the sub. -/
def toHm1 : ↥(normSource β f) →ₗ[k] Hm1 γ :=
  ((Coinvariants.mk γ).comp (q.domRestrict (normSource β f))).codRestrict
    (LinearMap.ker (coinvariantsNorm γ)) fun b => by
      refine LinearMap.mem_ker.mpr ((coinvariantsNorm_eq_zero_iff γ (q (b : B))).mpr ?_)
      have h : q (normMap β (b : B)) = normMap γ (q (b : B)) := map_normMap q hq (b : B)
      rw [← h]
      have hmem : normMap β (b : B) ∈ LinearMap.ker q := hex ▸ b.2
      exact LinearMap.mem_ker.mp hmem

@[simp]
theorem toHm1_coe (b : ↥(normSource β f)) :
    (toHm1 f q hq hex b : Coinvariants γ) = Coinvariants.mk γ (q (b : B)) := rfl

include hqs in
theorem toHm1_surjective : Function.Surjective (toHm1 f q hq hex) := by
  intro z
  obtain ⟨c, hc, rfl⟩ := exists_Hm1mk γ z
  obtain ⟨b, rfl⟩ := hqs c
  have hmem : b ∈ normSource β f := by
    rw [mem_normSource_iff, hex, LinearMap.mem_ker, map_normMap q hq b]
    exact hc
  exact ⟨⟨b, hmem⟩, Subtype.ext rfl⟩

include hf hfi hqs in
theorem ker_toHm1_le_ker_toH0 :
    LinearMap.ker (toHm1 f q hq hex) ≤ LinearMap.ker (toH0 f hf hfi) := by
  intro b hb
  have h0 : Coinvariants.mk γ (q (b : B)) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hb)
  obtain ⟨b', hb', hqb'⟩ :=
    coinvariantsKer_le_map q hq hqs ((Coinvariants.mk_eq_zero γ).mp h0)
  have hker : (b : B) - b' ∈ LinearMap.range f := by
    rw [hex]
    refine LinearMap.mem_ker.mpr ?_
    rw [map_sub, hqb', sub_self]
  obtain ⟨a₀, ha₀⟩ := hker
  have hnb' : normMap β b' = 0 :=
    LinearMap.mem_ker.mp (coinvariantsKer_le_ker_normMap β hb')
  have hkey : f (normDescent f hfi b) = f (normMap α a₀) := by
    rw [f_normDescent, map_normMap f hf a₀, ha₀, map_sub, hnb', sub_zero]
  refine LinearMap.mem_ker.mpr ?_
  rw [toH0_apply]
  refine (H0mk_eq_zero_iff α _).mpr ⟨a₀, ?_⟩
  rw [normDescentInv_coe]
  exact (hfi hkey).symm

include f hf q hq hfi hqs hex in
/-- **The connecting map** from the Tate group in degree minus one of the quotient to the Tate
group in degree zero of the sub. -/
def delta : Hm1 γ →ₗ[k] H0 α :=
  (LinearMap.ker (toHm1 f q hq hex)).liftQ (toH0 f hf hfi)
      (ker_toHm1_le_ker_toH0 f hf q hq hfi hqs hex) ∘ₗ
    ((toHm1 f q hq hex).quotKerEquivOfSurjective
      (toHm1_surjective f q hq hqs hex)).symm.toLinearMap

theorem delta_toHm1 (b : ↥(normSource β f)) :
    delta f hf q hq hfi hqs hex (toHm1 f q hq hex b) = toH0 f hf hfi b := by
  have h : ((toHm1 f q hq hex).quotKerEquivOfSurjective
      (toHm1_surjective f q hq hqs hex)).symm (toHm1 f q hq hex b)
      = Submodule.Quotient.mk b :=
    (toHm1 f q hq hex).quotKerEquivOfSurjective_symm_apply _ _
  show (LinearMap.ker (toHm1 f q hq hex)).liftQ (toH0 f hf hfi)
      (ker_toHm1_le_ker_toH0 f hf q hq hfi hqs hex)
      (((toHm1 f q hq hex).quotKerEquivOfSurjective
        (toHm1_surjective f q hq hqs hex)).symm (toHm1 f q hq hex b)) = _
  rw [h]
  rfl

end Snake

/-! ### Exactness -/

section Exactness

variable {α : Representation k G A} {β : Representation k G B} {γ : Representation k G C}
  (f : A →ₗ[k] B) (hf : ∀ g, f ∘ₗ α g = β g ∘ₗ f)
  (q : B →ₗ[k] C) (hq : ∀ g, q ∘ₗ β g = γ g ∘ₗ q)
  (hfi : Function.Injective f) (hqs : Function.Surjective q)
  (hex : LinearMap.range f = LinearMap.ker q)

include hfi hqs hex in
/-- **Exactness at the Tate group in degree minus one of the middle.** -/
theorem exact_Hm1_Hm1 : Function.Exact (Hm1map f hf) (Hm1map q hq) := by
  intro x
  constructor
  · intro h
    obtain ⟨b, hb, rfl⟩ := exists_Hm1mk β x
    have h0 : Coinvariants.mk γ (q b) = 0 := congrArg Subtype.val h
    obtain ⟨b', hb', hqb'⟩ :=
      coinvariantsKer_le_map q hq hqs ((Coinvariants.mk_eq_zero γ).mp h0)
    have hker : b - b' ∈ LinearMap.range f := by
      rw [hex]
      refine LinearMap.mem_ker.mpr ?_
      rw [map_sub, hqb', sub_self]
    obtain ⟨a, ha⟩ := hker
    have hnb' : normMap β b' = 0 :=
      LinearMap.mem_ker.mp (coinvariantsKer_le_ker_normMap β hb')
    have hna : normMap α a = 0 := by
      refine hfi ?_
      rw [map_normMap f hf a, ha, map_sub, hb, hnb', sub_zero, map_zero]
    refine ⟨Hm1mk α a hna, Subtype.ext ?_⟩
    rw [Hm1map_coe, Hm1mk_coe, Coinvariants.map_mk, Hm1mk_coe, ha, map_sub,
      (Coinvariants.mk_eq_zero β).mpr hb', sub_zero]
  · rintro ⟨y, rfl⟩
    obtain ⟨a, ha, rfl⟩ := exists_Hm1mk α y
    refine Subtype.ext ?_
    have hqf : q (f a) = 0 := by
      have hm : f a ∈ LinearMap.ker q := hex ▸ LinearMap.mem_range_self f a
      exact LinearMap.mem_ker.mp hm
    rw [Hm1map_coe, Hm1map_coe, Hm1mk_coe, Coinvariants.map_mk, Coinvariants.map_mk, hqf,
      map_zero]
    rfl

include hf hfi hqs hex in
/-- **Exactness at the Tate group in degree minus one of the quotient.** -/
theorem exact_Hm1_delta :
    Function.Exact (Hm1map q hq) (delta f hf q hq hfi hqs hex) := by
  intro z
  constructor
  · intro h
    obtain ⟨b, rfl⟩ := toHm1_surjective f q hq hqs hex z
    rw [delta_toHm1, toH0_apply] at h
    obtain ⟨a₀, ha₀⟩ := (H0mk_eq_zero_iff α _).mp h
    rw [normDescentInv_coe] at ha₀
    have hn : normMap β ((b : B) - f a₀) = 0 := by
      rw [map_sub, ← map_normMap f hf a₀, ha₀, f_normDescent, sub_self]
    have hqf : q (f a₀) = 0 := by
      have hm : f a₀ ∈ LinearMap.ker q := hex ▸ LinearMap.mem_range_self f a₀
      exact LinearMap.mem_ker.mp hm
    refine ⟨Hm1mk β ((b : B) - f a₀) hn, Subtype.ext ?_⟩
    rw [Hm1map_coe, Hm1mk_coe, Coinvariants.map_mk, toHm1_coe, map_sub, hqf, sub_zero]
  · rintro ⟨x, rfl⟩
    obtain ⟨b', hb', rfl⟩ := exists_Hm1mk β x
    have hmem : b' ∈ normSource β f := by
      rw [mem_normSource_iff, hb']
      exact zero_mem _
    have heq : Hm1map q hq (Hm1mk β b' hb') = toHm1 f q hq hex ⟨b', hmem⟩ := by
      refine Subtype.ext ?_
      rw [Hm1map_coe, Hm1mk_coe, Coinvariants.map_mk, toHm1_coe]
    rw [heq, delta_toHm1, toH0_apply]
    refine (H0mk_eq_zero_iff α _).mpr ⟨0, ?_⟩
    rw [normDescentInv_coe, map_zero]
    refine (hfi ?_).symm
    rw [f_normDescent, map_zero]
    exact hb'

include hf hfi hqs hex in
/-- **Exactness at the Tate group in degree zero of the sub.** -/
theorem exact_delta_H0 :
    Function.Exact (delta f hf q hq hfi hqs hex) (H0map f hf) := by
  intro w
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := H0mk_surjective α w
    rw [H0map_H0mk] at h
    obtain ⟨b, hb⟩ := (H0mk_eq_zero_iff β _).mp h
    rw [invariantsMap_coe] at hb
    have hmem : b ∈ normSource β f := by
      rw [mem_normSource_iff, hb]
      exact LinearMap.mem_range_self f _
    have hd : normDescent f hfi ⟨b, hmem⟩ = (a : A) := by
      refine hfi ?_
      rw [f_normDescent]
      exact hb
    refine ⟨toHm1 f q hq hex ⟨b, hmem⟩, ?_⟩
    rw [delta_toHm1, toH0_apply]
    exact congrArg (H0mk α) (Subtype.ext hd)
  · rintro ⟨z, rfl⟩
    obtain ⟨b, rfl⟩ := toHm1_surjective f q hq hqs hex z
    rw [delta_toHm1, toH0_apply, H0map_H0mk]
    refine (H0mk_eq_zero_iff β _).mpr ⟨(b : B), ?_⟩
    rw [invariantsMap_coe, normDescentInv_coe, f_normDescent]

include hfi hqs hex in
/-- **Exactness at the Tate group in degree zero of the middle.** -/
theorem exact_H0_H0 : Function.Exact (H0map f hf) (H0map q hq) := by
  intro v
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := H0mk_surjective β v
    obtain ⟨b, hb⟩ := y
    rw [H0map_H0mk] at h
    obtain ⟨c, hc⟩ := (H0mk_eq_zero_iff γ _).mp h
    rw [invariantsMap_coe] at hc
    obtain ⟨b₀, rfl⟩ := hqs c
    have hker : b - normMap β b₀ ∈ LinearMap.range f := by
      rw [hex]
      refine LinearMap.mem_ker.mpr ?_
      rw [map_sub, map_normMap q hq b₀, hc, sub_self]
    obtain ⟨a, ha⟩ := hker
    have hai : a ∈ α.invariants := by
      intro x
      refine hfi ?_
      have h1 : f (α x a) = β x (f a) := LinearMap.congr_fun (hf x) a
      rw [h1, ha, map_sub, apply_normMap, hb x]
    refine ⟨H0mk α ⟨a, hai⟩, ?_⟩
    rw [H0map_H0mk]
    refine (H0mk_eq_H0mk_iff β _ _).mpr ⟨-b₀, ?_⟩
    rw [map_neg, invariantsMap_coe, ha]
    abel
  · rintro ⟨w, rfl⟩
    obtain ⟨a, rfl⟩ := H0mk_surjective α w
    have hqf : q (f (a : A)) = 0 := by
      have hm : f (a : A) ∈ LinearMap.ker q := hex ▸ LinearMap.mem_range_self f _
      exact LinearMap.mem_ker.mp hm
    rw [H0map_H0mk, H0map_H0mk]
    refine (H0mk_eq_zero_iff γ _).mpr ⟨0, ?_⟩
    rw [invariantsMap_coe, invariantsMap_coe, hqf, map_zero]

end Exactness

end

end InverseGalois.CFT.Tate

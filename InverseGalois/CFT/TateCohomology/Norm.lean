/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The norm map of a representation of a finite group

For a representation of a finite group the sum of the actions of all the group elements is the
*norm* of the representation.  Translating the summation index shows that the norm of a vector is
invariant and that the norm of a translate is the norm of the vector, so the norm kills every
difference of a vector and one of its translates: it descends to a linear map from the coinvariants
to the invariants.

The cokernel and the kernel of that map are the two middle members of the complete cohomology of
the group: the invariants modulo the norms, and the classes in the coinvariants killed by the norm.
On the invariants the norm is multiplication by the order of the group, and on the coinvariants the
class of the norm of a vector is the order of the group times the class of the vector, so both
groups are annihilated by the order of the group.  An equivariant map of representations commutes
with the norms, so both are functorial.

## Main definitions

* `InverseGalois.CFT.Tate.normMap`: the sum of the actions of all the group elements.
* `InverseGalois.CFT.Tate.coinvariantsNorm`: the induced map from the coinvariants to the
  invariants.
* `InverseGalois.CFT.Tate.H0`, `InverseGalois.CFT.Tate.Hm1`: the invariants modulo the norms, and
  the norm zero classes in the coinvariants, with their classes `InverseGalois.CFT.Tate.H0mk` and
  `InverseGalois.CFT.Tate.Hm1mk`.
* `InverseGalois.CFT.Tate.invariantsMap`, `InverseGalois.CFT.Tate.H0map`,
  `InverseGalois.CFT.Tate.Hm1map`: the maps induced by an equivariant map of representations.

## Main results

* `InverseGalois.CFT.Tate.normMap_mem_invariants`, `InverseGalois.CFT.Tate.normMap_smul_apply`:
  **the norm of a vector is invariant, and the norm of a translate is the norm.**
* `InverseGalois.CFT.Tate.normMap_of_mem_invariants`: **on the invariants the norm is
  multiplication by the order of the group.**
* `InverseGalois.CFT.Tate.card_nsmul_eq_zero_H0`,
  `InverseGalois.CFT.Tate.card_nsmul_eq_zero_Hm1`: **the order of the group annihilates both
  groups.**
* `InverseGalois.CFT.Tate.coinvariantsNorm_comp_coinvariantsMap`: **the norm map is natural in the
  representation.**

## Tags

Tate cohomology, norm map, invariants, coinvariants, finite group
-/

namespace InverseGalois.CFT.Tate

open Representation

noncomputable section

variable {k G V W : Type*} [CommRing k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-! ### The norm of a representation -/

section NormMap

variable (ρ : Representation k G V) (τ : Representation k G W)

/-- **The norm of a representation of a finite group**: the sum of the actions of all the group
elements. -/
def normMap : V →ₗ[k] V := ∑ᶠ g : G, ρ g

omit [Finite G] in
theorem normMap_eq_sum [Fintype G] : normMap ρ = ∑ g : G, ρ g :=
  finsum_eq_sum_of_fintype _

omit [Finite G] in
theorem normMap_apply [Fintype G] (x : V) : normMap ρ x = ∑ g : G, ρ g x := by
  simp [normMap_eq_sum, LinearMap.sum_apply]

/-- **The norm of a vector is invariant.** -/
theorem apply_normMap (h : G) (x : V) : ρ h (normMap ρ x) = normMap ρ x := by
  letI := Fintype.ofFinite G
  rw [normMap_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  rw [Equiv.coe_mulLeft, map_mul]
  rfl

theorem normMap_mem_invariants (x : V) : normMap ρ x ∈ ρ.invariants :=
  fun g => apply_normMap ρ g x

/-- **The norm of a translate is the norm.** -/
theorem normMap_smul_apply (h : G) (x : V) : normMap ρ (ρ h x) = normMap ρ x := by
  letI := Fintype.ofFinite G
  rw [normMap_apply, normMap_apply]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
  rw [Equiv.coe_mulRight, map_mul]
  rfl

/-- The norm kills every difference of a vector and one of its translates. -/
theorem coinvariantsKer_le_ker_normMap :
    Coinvariants.ker ρ ≤ LinearMap.ker (normMap ρ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g, y⟩, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, normMap_smul_apply, sub_self]

/-- **The norm map of a representation of a finite group**, from the coinvariants to the
invariants. -/
def coinvariantsNorm : Coinvariants ρ →ₗ[k] ρ.invariants :=
  Coinvariants.lift ρ ((normMap ρ).codRestrict ρ.invariants (normMap_mem_invariants ρ))
    fun g => LinearMap.ext fun x => Subtype.ext (normMap_smul_apply ρ g x)

@[simp]
theorem coinvariantsNorm_mk (x : V) :
    (coinvariantsNorm ρ (Coinvariants.mk ρ x) : V) = normMap ρ x := rfl

theorem coinvariantsNorm_eq_zero_iff (x : V) :
    coinvariantsNorm ρ (Coinvariants.mk ρ x) = 0 ↔ normMap ρ x = 0 := by
  rw [← Subtype.coe_inj, coinvariantsNorm_mk]
  rfl

/-- **On the invariants the norm is multiplication by the order of the group.** -/
theorem normMap_of_mem_invariants {x : V} (hx : x ∈ ρ.invariants) :
    normMap ρ x = Nat.card G • x := by
  letI := Fintype.ofFinite G
  rw [normMap_apply, Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun g _ => hx g

/-- **The class of the norm of a vector is the order of the group times the class of the
vector.** -/
theorem mk_normMap (x : V) :
    Coinvariants.mk ρ (normMap ρ x) = Nat.card G • Coinvariants.mk ρ x := by
  letI := Fintype.ofFinite G
  rw [normMap_apply, map_sum, Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun g _ => Coinvariants.mk_self_apply ρ g x

end NormMap

/-! ### The two middle Tate groups -/

section Groups

variable (ρ : Representation k G V)

/-- **The Tate group in degree zero of a representation of a finite group**: the invariants modulo
the norms. -/
abbrev H0 := ρ.invariants ⧸ LinearMap.range (coinvariantsNorm ρ)

/-- **The Tate group in degree minus one of a representation of a finite group**: the classes in
the coinvariants killed by the norm. -/
abbrev Hm1 := LinearMap.ker (coinvariantsNorm ρ)

/-- The class in the Tate group in degree zero of an invariant vector. -/
def H0mk : ρ.invariants →ₗ[k] H0 ρ := (LinearMap.range (coinvariantsNorm ρ)).mkQ

theorem H0mk_surjective : Function.Surjective (H0mk ρ) :=
  Submodule.mkQ_surjective _

theorem H0mk_eq_zero_iff (x : ρ.invariants) :
    H0mk ρ x = 0 ↔ ∃ y : V, normMap ρ y = (x : V) := by
  rw [H0mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨y, rfl⟩ := Coinvariants.mk_surjective ρ c
    exact ⟨y, congrArg Subtype.val hc⟩
  · rintro ⟨y, hy⟩
    exact ⟨Coinvariants.mk ρ y, Subtype.ext ((coinvariantsNorm_mk ρ y).trans hy)⟩

/-- Two invariant vectors have the same class in the Tate group in degree zero exactly when their
difference is a norm. -/
theorem H0mk_eq_H0mk_iff (x y : ρ.invariants) :
    H0mk ρ x = H0mk ρ y ↔ ∃ v : V, normMap ρ v = (x : V) - (y : V) := by
  rw [← sub_eq_zero, ← map_sub, H0mk_eq_zero_iff, Submodule.coe_sub]

/-- The class in the Tate group in degree minus one of a vector whose norm vanishes. -/
def Hm1mk (v : V) (hv : normMap ρ v = 0) : Hm1 ρ :=
  ⟨Coinvariants.mk ρ v, LinearMap.mem_ker.mpr ((coinvariantsNorm_eq_zero_iff ρ v).mpr hv)⟩

@[simp]
theorem Hm1mk_coe (v : V) (hv : normMap ρ v = 0) :
    (Hm1mk ρ v hv : Coinvariants ρ) = Coinvariants.mk ρ v := rfl

/-- Every class in the Tate group in degree minus one comes from a vector whose norm vanishes. -/
theorem exists_Hm1mk (x : Hm1 ρ) : ∃ (v : V) (hv : normMap ρ v = 0), x = Hm1mk ρ v hv := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ y
  exact ⟨v, (coinvariantsNorm_eq_zero_iff ρ v).mp (LinearMap.mem_ker.mp hy), rfl⟩

/-- **The order of the group annihilates the Tate group in degree zero.** -/
theorem card_nsmul_eq_zero_H0 (x : H0 ρ) : Nat.card G • x = 0 := by
  obtain ⟨y, rfl⟩ := H0mk_surjective ρ x
  rw [← map_nsmul]
  refine (H0mk_eq_zero_iff ρ _).mpr ⟨(y : V), ?_⟩
  rw [normMap_of_mem_invariants ρ y.2]
  rfl

/-- **The order of the group annihilates the Tate group in degree minus one.** -/
theorem card_nsmul_eq_zero_Hm1 (x : Hm1 ρ) : Nat.card G • x = 0 := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ y
  refine Subtype.ext ?_
  rw [Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero, ← mk_normMap ρ v,
    (coinvariantsNorm_eq_zero_iff ρ v).mp hy, map_zero]

end Groups

/-! ### Functoriality -/

section Functoriality

variable {ρ : Representation k G V} {τ : Representation k G W}
  (f : V →ₗ[k] W) (hf : ∀ g, f ∘ₗ ρ g = τ g ∘ₗ f)

include hf

/-- **An equivariant map commutes with the norms.** -/
theorem map_normMap (x : V) : f (normMap ρ x) = normMap τ (f x) := by
  letI := Fintype.ofFinite G
  rw [normMap_apply, map_sum, normMap_apply]
  exact Finset.sum_congr rfl fun g _ => LinearMap.congr_fun (hf g) x

omit [Finite G] in
theorem map_mem_invariants {x : V} (hx : x ∈ ρ.invariants) : f x ∈ τ.invariants := fun g => by
  have h := LinearMap.congr_fun (hf g) x
  simp only [LinearMap.comp_apply, hx g] at h
  exact h.symm

/-- **An equivariant map of representations induces a map of invariants.** -/
def invariantsMap : ρ.invariants →ₗ[k] τ.invariants :=
  (f.domRestrict ρ.invariants).codRestrict τ.invariants fun c => map_mem_invariants f hf c.2

omit [Finite G] in
@[simp]
theorem invariantsMap_coe (x : ρ.invariants) : (invariantsMap f hf x : W) = f (x : V) := rfl

omit [Finite G] in
/-- **An injective equivariant map stays injective on the invariants.** -/
theorem invariantsMap_injective (hfi : Function.Injective f) :
    Function.Injective (invariantsMap f hf) := fun x y h =>
  Subtype.ext (hfi (by simpa only [invariantsMap_coe] using congrArg Subtype.val h))

/-- **The norm map is natural in the representation.** -/
theorem coinvariantsNorm_comp_coinvariantsMap :
    coinvariantsNorm τ ∘ₗ Coinvariants.map ρ τ f hf
      = invariantsMap f hf ∘ₗ coinvariantsNorm ρ := by
  refine Coinvariants.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
  simpa using (map_normMap f hf x).symm

/-- **An equivariant map of representations induces a map of the Tate groups in degree zero.** -/
def H0map : H0 ρ →ₗ[k] H0 τ :=
  Submodule.mapQ _ _ (invariantsMap f hf) <| by
    rintro _ ⟨c, rfl⟩
    exact ⟨Coinvariants.map ρ τ f hf c,
      LinearMap.congr_fun (coinvariantsNorm_comp_coinvariantsMap f hf) c⟩

@[simp]
theorem H0map_H0mk (x : ρ.invariants) : H0map f hf (H0mk ρ x) = H0mk τ (invariantsMap f hf x) :=
  rfl

/-- **An equivariant map of representations induces a map of the Tate groups in degree minus
one.** -/
def Hm1map : Hm1 ρ →ₗ[k] Hm1 τ :=
  (Coinvariants.map ρ τ f hf).restrict fun c hc => by
    rw [LinearMap.mem_ker] at hc ⊢
    have h := LinearMap.congr_fun (coinvariantsNorm_comp_coinvariantsMap f hf) c
    simp only [LinearMap.comp_apply, hc, map_zero] at h
    exact h

@[simp]
theorem Hm1map_coe (x : Hm1 ρ) :
    (Hm1map f hf x : Coinvariants τ) = Coinvariants.map ρ τ f hf (x : Coinvariants ρ) := rfl

end Functoriality

end

end InverseGalois.CFT.Tate

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Isogeny
import InverseGalois.CFT.Tate.Restrict

/-!
# The fixed points of an action on a quotient

Let `σ` be an automorphism of order dividing `n` of an abelian group `B`, and let `N` be a
subgroup carried into itself by `σ`.  A class in `B / N` fixed by the induced automorphism need not
be the class of a fixed point of `σ`; the obstruction is a class in the first cohomology of `N`.
Indeed, if the class of `b` is fixed then `σ b - b` lies in `N`, and it has norm zero because the
norm telescopes; if the first cohomology of `N` vanishes it is therefore a difference `σ y - y`
with `y` in `N`, and `b - y` is a fixed point representing the same class.

So when the first cohomology of the subgroup vanishes, the fixed points of the quotient are exactly
the classes of the fixed points.  This is the mechanism behind the passage from the ideles to the
idele classes: Hilbert's theorem 90 for the multiplicative group of the extension says precisely
that the relevant first cohomology vanishes.

## Main results

* `InverseGalois.CFT.sub_mem_of_quotAut_mk_eq`: a representative of a fixed class differs from its
  image by an element of the subgroup.
* `InverseGalois.CFT.exists_fixed_mk_eq_of_forall`: **a fixed class is the class of a fixed point**,
  when every element of the subgroup of norm zero is a difference of elements of the subgroup.
* `InverseGalois.CFT.exists_fixed_mk_eq_of_range`: the same for the cokernel of an equivariant
  injection whose source has vanishing `Ĥ⁻¹`.
* `InverseGalois.CFT.exists_fixed_mk_eq`: the same, with the hypothesis read off the Tate group
  `Ĥ⁻¹` of the subgroup.

## Tags

Tate cohomology, cyclic group, fixed points, quotient, Hilbert 90
-/

namespace InverseGalois.CFT

section QuotientFixed

variable {B : Type*} [AddCommGroup B] {σ : B ≃+ B} {N : AddSubgroup B} {n : ℕ}

/-! ### Representatives of a fixed class -/

/-- The class of a point fixed by the automorphism is fixed by the induced automorphism. -/
theorem quotAut_mk_eq_of_fixed (hN : N.map (σ : B →+ B) = N) {b : B} (hb : σ b = b) :
    quotAut σ N hN (QuotientAddGroup.mk b) = QuotientAddGroup.mk b := by
  rw [quotAut_mk, hb]

/-- **A representative of a class fixed by the induced automorphism differs from its image by an
element of the subgroup.** -/
theorem sub_mem_of_quotAut_mk_eq (hN : N.map (σ : B →+ B) = N) {b : B}
    (hb : quotAut σ N hN (QuotientAddGroup.mk b) = QuotientAddGroup.mk b) : σ b - b ∈ N := by
  rw [quotAut_mk, QuotientAddGroup.eq_iff_sub_mem] at hb
  exact hb

/-! ### Lifting a fixed class to a fixed point -/

/-- **A class fixed by the induced automorphism is the class of a fixed point**, provided every
element of the subgroup of norm zero is a difference `σ y - y` with `y` in the subgroup: the
difference `σ b - b` of a representative has norm zero, and subtracting off the corresponding `y`
makes the representative fixed. -/
theorem exists_fixed_mk_eq_of_forall (hN : N.map (σ : B →+ B) = N) (hσ : σ ^ n = 1)
    (hH : ∀ a ∈ N, normHom σ n a = 0 → ∃ y ∈ N, σ y - y = a) {x : B ⧸ N}
    (hx : quotAut σ N hN x = x) : ∃ b : B, σ b = b ∧ QuotientAddGroup.mk b = x := by
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hmem : σ b - b ∈ N := sub_mem_of_quotAut_mk_eq hN hx
  have hnorm : normHom σ n (σ b - b) = 0 :=
    AddMonoidHom.mem_ker.mp (range_sigmaSubOne_le_ker_normHom σ hσ ⟨b, rfl⟩)
  obtain ⟨y, hyN, hy⟩ := hH _ hmem hnorm
  refine ⟨b - y, ?_, ?_⟩
  · have h : σ b - σ y - (b - y) = (σ b - b) - (σ y - y) := by abel
    rw [map_sub, ← sub_eq_zero, h, hy, sub_self]
  · rw [QuotientAddGroup.eq_iff_sub_mem, sub_sub_cancel_left]
    exact neg_mem hyN

/-! ### A subgroup presented as the range of an equivariant injection -/

section Range

variable {A : Type*} [AddCommGroup A] {σA : A ≃+ A}

/-- **A class of the cokernel of an equivariant injection fixed by the induced automorphism is the
class of a fixed point**, when the Tate group `Ĥ⁻¹` of the source vanishes: the difference between
a representative and its image is the image of an element of norm zero, hence of a difference. -/
theorem exists_fixed_mk_eq_of_range (φ : A →+ B) (hφ : ∀ a, φ (σA a) = σ (φ a))
    (hinj : Function.Injective φ) [Subsingleton (tateHm1 σA n)] (hσ : σ ^ n = 1)
    {x : B ⧸ φ.range} (hx : quotAut σ φ.range (map_range_eq_range φ hφ) x = x) :
    ∃ b : B, σ b = b ∧ QuotientAddGroup.mk b = x := by
  refine exists_fixed_mk_eq_of_forall _ hσ (fun a ha hnorm => ?_) hx
  obtain ⟨c, rfl⟩ := ha
  have hc : normHom σA n c = 0 := by
    refine hinj ?_
    rw [map_normHom φ hφ, hnorm, map_zero]
  have hzero : tateHm1.mk σA n c hc = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (tateHm1.mk_eq_zero_iff c hc).mp hzero
  refine ⟨φ y, ⟨y, rfl⟩, ?_⟩
  rw [← hφ, ← map_sub, hy]

end Range

/-! ### The hypothesis as the vanishing of a Tate group -/

variable (σ N) in
/-- The norm of the restriction of an automorphism to an invariant subgroup is the restriction of
the norm. -/
theorem coe_normHom_subgroupAut (h : ∀ x ∈ N, σ x ∈ N) (h' : ∀ x ∈ N, σ.symm x ∈ N) (n : ℕ)
    (x : N) : ((normHom (subgroupAut σ N h h') n x : N) : B) = normHom σ n (x : B) := by
  rw [normHom_apply, normHom_apply, AddSubmonoidClass.coe_finset_sum]
  exact Finset.sum_congr rfl fun i _ => coe_pow_subgroupAut_apply h h' i x

/-- **A class fixed by the induced automorphism is the class of a fixed point**, when the Tate
group `Ĥ⁻¹` of the subgroup vanishes. -/
theorem exists_fixed_mk_eq (hN : N.map (σ : B →+ B) = N) (hσ : σ ^ n = 1)
    (h : ∀ x ∈ N, σ x ∈ N) (h' : ∀ x ∈ N, σ.symm x ∈ N)
    [Subsingleton (tateHm1 (subgroupAut σ N h h') n)] {x : B ⧸ N} (hx : quotAut σ N hN x = x) :
    ∃ b : B, σ b = b ∧ QuotientAddGroup.mk b = x := by
  refine exists_fixed_mk_eq_of_forall hN hσ (fun a ha hnorm => ?_) hx
  have hker : normHom (subgroupAut σ N h h') n ⟨a, ha⟩ = 0 :=
    Subtype.ext (by rw [coe_normHom_subgroupAut σ N h h' n ⟨a, ha⟩, hnorm]; rfl)
  have hzero : tateHm1.mk (subgroupAut σ N h h') n ⟨a, ha⟩ hker = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (tateHm1.mk_eq_zero_iff _ hker).mp hzero
  exact ⟨(y : B), y.2, congrArg Subtype.val hy⟩

end QuotientFixed

end InverseGalois.CFT

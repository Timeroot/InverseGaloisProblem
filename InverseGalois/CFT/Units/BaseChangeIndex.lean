/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleClassIndex
import InverseGalois.CFT.Units.IdeleNormTower

/-!
# Enlarging the base field of a norm index

The index of the principal ideles together with the norms from an extension can only grow when the
base field is enlarged by an extension whose degree is prime to the degree of the extension.  The
comparison is a transfer: the norm from the larger base field carries principal ideles to principal
ideles and norms to norms, so it descends to a homomorphism of the two quotients, and that
homomorphism is surjective because the quotient downstairs is killed by the degree, on which the
composite of the inclusion with the norm acts invertibly.

Two computations underlie this.  The norm of an idele of the base field is the degree times that
idele, because its conjugates are all itself; consequently the quotient of the ideles by the
principal ideles together with the norms is killed by the degree.  And the norm of a principal
idele is principal, because the product of the conjugates of a unit is fixed by the Galois group
and so lies in the base field.

## Main results

* `InverseGalois.CFT.index_dvd_index_of_transfer`: the index of a subgroup divides the index of a
  subgroup of another group carried into it by a homomorphism which is surjective modulo the first.
* `InverseGalois.CFT.ideleNorm_ideleComap`: **the norm of an idele of the base field is the degree
  times that idele.**
* `InverseGalois.CFT.ideleNorm_ideleDiag_mem`: the norm of a principal idele is principal.
* `InverseGalois.CFT.index_dvd_index_of_coprime`: **enlarging the base field by an extension of
  degree prime to the degree of the extension can only increase the norm index.**

## Tags

number field, idele, norm index, base change, second inequality
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### A transfer between two quotients -/

section Transfer

/-- **The index of a subgroup divides the index of a subgroup of another group carried into it by a
homomorphism which is surjective modulo the first**: the homomorphism descends to a surjection of
the quotients. -/
theorem index_dvd_index_of_transfer {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {N : AddSubgroup A} {M : AddSubgroup B} (f : B →+ A) (hle : ∀ b ∈ M, f b ∈ N)
    (hsurj : ∀ a : A, ∃ b : B, a - f b ∈ N) : N.index ∣ M.index := by
  set F : B ⧸ M →+ A ⧸ N :=
    QuotientAddGroup.lift M ((QuotientAddGroup.mk' N).comp f)
      fun b hb => (QuotientAddGroup.eq_zero_iff _).mpr (hle b hb)
  have hFsurj : Function.Surjective F := by
    intro c
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨b, hb⟩ := hsurj a
    exact ⟨(b : B ⧸ M), (QuotientAddGroup.eq_iff_sub_mem.mpr hb).symm⟩
  rw [AddSubgroup.index_eq_card, AddSubgroup.index_eq_card]
  exact AddSubgroup.card_dvd_of_surjective F hFsurj

end Transfer

/-! ### The norm of an idele of the base field -/

section Comap

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

variable (k K) in
/-- **The norm of an idele of the base field is the degree times that idele**, its conjugates all
being itself. -/
theorem ideleNorm_ideleComap (x : ↥(idele k)) :
    ideleNorm k K (ideleComap k K x) = Nat.card Gal(K/k) • x := by
  refine ideleComap_injective k K ?_
  rw [ideleComap_ideleNorm, galSum_apply, map_nsmul]
  simp only [ideleAut_ideleComap k K _ x]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

variable (k K) in
/-- The norm of a principal idele is principal: the sum of the conjugates of a unit is fixed by the
Galois group, hence comes from the base field. -/
theorem ideleNorm_ideleDiag_mem (u : Additive Kˣ) :
    ideleNorm k K (ideleDiag K u) ∈ (ideleDiag k).range := by
  set w : Additive Kˣ := ∑ g : Gal(K/k), globalUnitsAut (k := k) g u with hw
  have hfix : ∀ τ : Gal(K/k), globalUnitsAut (k := k) τ w = w := by
    intro τ
    rw [hw, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun g => ?_
    show globalUnitsAut (k := k) τ (globalUnitsAut (k := k) g u)
      = globalUnitsAut (k := k) (τ * g) u
    rw [map_mul]
    rfl
  obtain ⟨c, hc⟩ := (mem_range_globalUnitsComap_iff w).mpr hfix
  refine ⟨c, ideleComap_injective k K ?_⟩
  rw [ideleComap_ideleDiag, hc, hw, ideleComap_ideleNorm, galSum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ => (ideleAut_ideleDiag g u).symm

end Comap

/-! ### Enlarging the base field -/

section BaseChange

variable {k L K' L' : Type*} [Field k] [NumberField k] [Field L] [NumberField L]
  [Field K'] [NumberField K'] [Field L'] [NumberField L']
  [Algebra k L] [Algebra k K'] [Algebra k L'] [Algebra L L'] [Algebra K' L']
  [IsScalarTower k L L'] [IsScalarTower k K' L']
  [IsGalois k L] [IsGalois k K'] [IsGalois k L'] [IsGalois L L'] [IsGalois K' L']

set_option synthInstance.maxHeartbeats 400000

/-- **Enlarging the base field by an extension of degree prime to the degree of the extension can
only increase the norm index.**  The norm from the larger base field carries principal ideles to
principal ideles and, by transitivity, norms from the larger top field to norms from the smaller
one; the quotient downstairs is killed by the degree of the extension, so the composite with the
inclusion of the ideles of the base field, which is multiplication by the degree of the enlargement,
is invertible on it. -/
theorem index_dvd_index_of_coprime
    (hcop : Nat.Coprime (Nat.card Gal(K'/k)) (Nat.card Gal(L/k))) :
    ((ideleDiag k).range ⊔ (ideleNorm k L).range).index ∣
      ((ideleDiag K').range ⊔ (ideleNorm K' L').range).index := by
  refine index_dvd_index_of_transfer (ideleNorm k K') (fun b hb => ?_) fun a => ?_
  · obtain ⟨-, ⟨u, rfl⟩, -, ⟨d, rfl⟩, rfl⟩ := AddSubgroup.mem_sup.mp hb
    rw [map_add]
    refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (ideleNorm_ideleDiag_mem k K' u)) ?_
    refine AddSubgroup.mem_sup_right ⟨ideleNorm L L' d, ?_⟩
    rw [ideleNorm_trans k L L', ideleNorm_trans k K' L']
  · have hbez : IsCoprime ((Nat.card Gal(K'/k) : ℤ)) ((Nat.card Gal(L/k) : ℤ)) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hcop)
    obtain ⟨s, t, hst⟩ := hbez
    have ha : a = (s * (Nat.card Gal(K'/k) : ℤ)) • a + (t * (Nat.card Gal(L/k) : ℤ)) • a := by
      rw [← add_zsmul, hst, one_zsmul]
    refine ⟨s • ideleComap k K' a, ?_⟩
    have h1 : ideleNorm k K' (s • ideleComap k K' a) = (s * (Nat.card Gal(K'/k) : ℤ)) • a := by
      rw [map_zsmul, ideleNorm_ideleComap k K', ← natCast_zsmul, smul_smul]
    have h2 : a - ideleNorm k K' (s • ideleComap k K' a)
        = (t * (Nat.card Gal(L/k) : ℤ)) • a := by
      rw [h1, sub_eq_iff_eq_add, add_comm]
      exact ha
    rw [h2, mul_zsmul, natCast_zsmul, ← ideleNorm_ideleComap k L a]
    refine AddSubgroup.zsmul_mem _ (AddSubgroup.mem_sup_right ?_) t
    exact AddMonoidHom.mem_range.mpr ⟨ideleComap k L a, rfl⟩

end BaseChange

end InverseGalois.CFT

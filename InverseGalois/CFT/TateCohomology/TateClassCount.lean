/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.SylowInjective
import InverseGalois.CFT.TateCohomology.TensorTrivial

/-!
# Tate's hypotheses from a count

The classical hypotheses of Tate's theorem ask, on every subgroup, that the complete cohomology
vanish in degree one and that in degree two it be exactly the multiples of the restricted class,
annihilated by no proper multiple of the order of the subgroup.  The second and third of those are
a single arithmetic statement about the order of a finite commutative group: an element whose
annihilator is exactly the multiples of the order generates the whole group, because the subgroup
it generates has as many elements as the group.

The order of the restricted class is controlled by the order of the class one started with.
Corestriction after restriction is multiplication by the index, so a multiple of the class dying
after restriction to a subgroup already dies after multiplication by the index; if only the
multiples of the order of the whole group annihilate the class, then the index times that multiple
is one of them, and the order of the group is the order of the subgroup times the index.

So Tate's hypotheses on a subgroup follow from three things which do not mention the class in degree
two of the subgroup at all: the vanishing in degree one, the count of the degree two, and the order
of the class over the whole group.  That is the shape in which the fundamental class of a class
formation is presented, and it feeds both Tate's theorem and the theorem of Tate and Nakayama.

## Main results

* `InverseGalois.CFT.Tate.exists_zsmul_of_card_eq`: **an element of a finite commutative group
  annihilated by exactly the multiples of the order generates the group.**
* `InverseGalois.CFT.Tate.dvd_of_zsmul_tateRes_eq_zero`: **the restriction of a class of order the
  order of the group has order the order of the subgroup.**
* `InverseGalois.CFT.Tate.isTateClassTwo_of_card`: **the classical hypotheses of Tate's theorem
  follow from a count.**
* `InverseGalois.CFT.Tate.tateTheoremTwoEquivOfCard`: **Tate's theorem** from that count.
* `InverseGalois.CFT.Tate.tateNakayamaFlatEquivOfCard`: **the theorem of Tate and Nakayama** from
  that count, for coefficients flat over the integers.

## Tags

Tate cohomology, Tate's theorem, fundamental class, class formation, Tate-Nakayama
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### An element that generates by a count -/

/-- **An element of a finite commutative group annihilated by exactly the multiples of the order
of the group generates the group**: the subgroup of its multiples has as many elements as the
order of the element, which the annihilator pins to the order of the group. -/
theorem exists_zsmul_of_card_eq {M : Type*} [AddCommGroup M] [Finite M] {β : M} {n : ℕ}
    (hcard : Nat.card M = n) (hord : ∀ m : ℤ, m • β = 0 → (n : ℤ) ∣ m) (y : M) :
    ∃ m : ℤ, y = m • β := by
  have hdvd : addOrderOf β ∣ n := hcard ▸ addOrderOf_dvd_natCard β
  have hdvd' : n ∣ addOrderOf β := by
    have h : (addOrderOf β : ℤ) • β = 0 := by
      rw [natCast_zsmul]
      exact addOrderOf_nsmul_eq_zero β
    exact_mod_cast hord _ h
  have heq : addOrderOf β = n := Nat.dvd_antisymm hdvd hdvd'
  have htop : AddSubgroup.zmultiples β = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, heq, hcard])
  have hy : y ∈ AddSubgroup.zmultiples β := by
    rw [htop]
    trivial
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 hy
  exact ⟨m, hm.symm⟩

/-! ### The order of a restricted class -/

section Order

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **The restriction of a class annihilated by exactly the multiples of the order of the group is
annihilated by exactly the multiples of the order of the subgroup**: corestriction after
restriction is multiplication by the index, and the order of the group is the order of the subgroup
times the index. -/
theorem dvd_of_zsmul_tateRes_eq_zero {H : Subgroup G} {A : Rep k G} {n : ℤ} {α : tateModule A n}
    (hα : ∀ m : ℤ, m • α = 0 → (Nat.card G : ℤ) ∣ m) {m : ℤ}
    (hm : m • tateRes H A n α = 0) : (Nat.card ↥H : ℤ) ∣ m := by
  have h0 : tateRes H A n (m • α) = 0 := by
    rw [map_zsmul]
    exact hm
  have h1 : ((H.index : ℤ) * m) • α = 0 := by
    rw [mul_smul, natCast_zsmul]
    exact index_smul_eq_zero_of_tateRes_eq_zero h0
  have h3 := hα _ h1
  rw [← Subgroup.card_mul_index H] at h3
  push_cast at h3
  have hne : (H.index : ℤ) ≠ 0 := Int.natCast_ne_zero.2 Subgroup.index_ne_zero_of_finite
  refine (mul_dvd_mul_iff_left hne).1 ?_
  rwa [mul_comm ((H.index : ℤ)) ((Nat.card ↥H : ℤ))]

end Order

/-! ### Tate's hypotheses -/

section Criterion

variable {G : Type} [Group G] [Finite G] {A : Rep ℤ G} {α : tateModule A 2}

/-- **The classical hypotheses of Tate's theorem follow from a count**: the complete cohomology of
the subgroup vanishes in degree one, in degree two it has as many elements as the subgroup, and the
class is annihilated by exactly the multiples of the order of the whole group. -/
theorem isTateClassTwo_of_card (H : Subgroup G) (h1 : Limits.IsZero (tateModule (resObj H A) 1))
    (hfin : Finite ↥(tateModule (resObj H A) 2))
    (hcard : Nat.card ↥(tateModule (resObj H A) 2) = Nat.card ↥H)
    (hα : ∀ m : ℤ, m • α = 0 → (Nat.card G : ℤ) ∣ m) :
    IsTateClassTwo H A α := by
  haveI := hfin
  exact
    { isZero_one := h1
      exists_zsmul := fun y =>
        exists_zsmul_of_card_eq hcard (fun _ hm => dvd_of_zsmul_tateRes_eq_zero hα hm) y
      dvd_of_zsmul_eq_zero := fun _ hm => dvd_of_zsmul_tateRes_eq_zero hα hm }

variable (A α)

/-- **Tate's theorem from a count**: the complete cohomology of the integers in a degree is the
complete cohomology of the representation two degrees higher. -/
def tateTheoremTwoEquivOfCard (h1 : ∀ H : Subgroup G, Limits.IsZero (tateModule (resObj H A) 1))
    (hfin : ∀ H : Subgroup G, Finite ↥(tateModule (resObj H A) 2))
    (hcard : ∀ H : Subgroup G, Nat.card ↥(tateModule (resObj H A) 2) = Nat.card ↥H)
    (hα : ∀ m : ℤ, m • α = 0 → (Nat.card G : ℤ) ∣ m) (n : ℤ) :
    tateModule (Rep.trivial ℤ G ℤ) n ≃ₗ[ℤ] tateModule A (n + 1 + 1) :=
  tateTheoremTwoEquiv A α
    (fun _ _ P => isTateClassTwo_of_card (P : Subgroup G) (h1 _) (hfin _) (hcard _) hα) n

/-- **The theorem of Tate and Nakayama from a count**, for coefficients flat over the integers. -/
def tateNakayamaFlatEquivOfCard (h1 : ∀ H : Subgroup G, Limits.IsZero (tateModule (resObj H A) 1))
    (hfin : ∀ H : Subgroup G, Finite ↥(tateModule (resObj H A) 2))
    (hcard : ∀ H : Subgroup G, Nat.card ↥(tateModule (resObj H A) 2) = Nat.card ↥H)
    (hα : ∀ m : ℤ, m • α = 0 → (Nat.card G : ℤ) ∣ m) (M : Rep ℤ G) (hM : Module.Flat ℤ ↥M.V)
    (n : ℤ) : tateModule M n ≃ₗ[ℤ] tateModule (tensorObj A M) (n + 1 + 1) :=
  tateNakayamaFlatEquiv A α
    (fun _ _ P => isTateClassTwo_of_card (P : Subgroup G) (h1 _) (hfin _) (hcard _) hα) M hM n

end Criterion

end

end InverseGalois.CFT.Tate

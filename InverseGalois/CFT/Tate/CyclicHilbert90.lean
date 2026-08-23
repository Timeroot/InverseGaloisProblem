/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Mul

/-!
# Hilbert's theorem 90 for a cyclic group acting on a field

A finite cyclic group acting faithfully on a field makes the field a cyclic Galois extension of the
subfield it fixes, and Hilbert's theorem 90 says that an element whose conjugates multiply to one is
a quotient `σ y / y`.  The classical proof produces `y` as a Lagrange resolvent: the partial products
of the conjugates weight the conjugates of a test element, and Dedekind's linear independence of
characters supplies a test element for which the resolvent does not vanish.

The statement is phrased for a group acting on a field rather than for a Galois extension, which
both avoids choosing a base field and leaves the field in an arbitrary universe.

## Main definitions

* `InverseGalois.CFT.partialConj`: the product of the first conjugates of an element.
* `InverseGalois.CFT.resolvent`: the Lagrange resolvent.
* `InverseGalois.CFT.unitsSmulAut`: the automorphism of the unit group induced by a group element.

## Main results

* `InverseGalois.CFT.mul_smul_resolvent`: an element whose conjugates multiply to one scales the
  resolvent.
* `InverseGalois.CFT.exists_resolvent_ne_zero`: some test element gives a resolvent that does not
  vanish.
* `InverseGalois.CFT.exists_smul_div_eq_of_prod_smul_eq_one`: **Hilbert's theorem 90.**
* `InverseGalois.CFT.tateHm1_unitsSmulAut_eq_zero`: **the Tate group `Ĥ⁻¹` of the unit group of the
  field vanishes.**

## Tags

Hilbert theorem 90, cyclic extension, Lagrange resolvent, linear independence of characters
-/

namespace InverseGalois.CFT

variable {G A : Type*} [Group G] [Field A] [MulSemiringAction G A]

/-! ### Partial products of the conjugates -/

variable (σ : G) (x : A)

/-- **The product of the first conjugates of an element.** -/
def partialConj (i : ℕ) : A :=
  ∏ j ∈ Finset.range i, (σ ^ j) • x

@[simp]
theorem partialConj_zero : partialConj σ x 0 = 1 := by
  simp [partialConj]

/-- Conjugating the product of the first conjugates and multiplying by the element itself gives the
product of one more conjugate. -/
theorem smul_partialConj_mul (i : ℕ) : (σ • partialConj σ x i) * x = partialConj σ x (i + 1) := by
  have hmap : σ • ∏ j ∈ Finset.range i, (σ ^ j) • x
      = ∏ j ∈ Finset.range i, σ • ((σ ^ j) • x) :=
    map_prod (MulSemiringAction.toRingHom G A σ) (fun j => (σ ^ j) • x) (Finset.range i)
  rw [partialConj, hmap, partialConj, Finset.prod_range_succ']
  simp [smul_smul, ← pow_succ']

/-! ### The Lagrange resolvent -/

variable (d : ℕ)

/-- **The Lagrange resolvent**: the conjugates of a test element weighted by the partial products of
the conjugates of a given element. -/
def resolvent (c : A) : A :=
  ∑ i ∈ Finset.range d, partialConj σ x i * (σ ^ i) • c

variable {σ x d}

/-- **An element whose conjugates multiply to one scales the resolvent.** -/
theorem mul_smul_resolvent (hσ : σ ^ d = 1) (hx : partialConj σ x d = 1) (c : A) :
    x * σ • resolvent σ x d c = resolvent σ x d c := by
  have hmap : σ • ∑ i ∈ Finset.range d, partialConj σ x i * (σ ^ i) • c
      = ∑ i ∈ Finset.range d, σ • (partialConj σ x i * (σ ^ i) • c) :=
    map_sum (MulSemiringAction.toRingHom G A σ) _ (Finset.range d)
  have hstep : ∀ i : ℕ, x * σ • (partialConj σ x i * (σ ^ i) • c)
      = partialConj σ x (i + 1) * (σ ^ (i + 1)) • c := by
    intro i
    rw [smul_mul', smul_smul, ← pow_succ', ← smul_partialConj_mul σ x i]
    ring
  have hsum : x * σ • resolvent σ x d c
      = ∑ i ∈ Finset.range d, partialConj σ x (i + 1) * (σ ^ (i + 1)) • c := by
    rw [resolvent, hmap, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hstep i
  have hshift : (∑ i ∈ Finset.range d, partialConj σ x (i + 1) * (σ ^ (i + 1)) • c)
        + partialConj σ x 0 * (σ ^ 0) • c
      = (∑ i ∈ Finset.range d, partialConj σ x i * (σ ^ i) • c)
        + partialConj σ x d * (σ ^ d) • c := by
    rw [← Finset.sum_range_succ' (fun k => partialConj σ x k * (σ ^ k) • c) d,
      Finset.sum_range_succ (fun k => partialConj σ x k * (σ ^ k) • c) d]
  have hz : partialConj σ x 0 * (σ ^ 0) • c = c := by simp
  have hl : partialConj σ x d * (σ ^ d) • c = c := by rw [hx, hσ]; simp
  rw [hz, hl] at hshift
  rw [hsum, resolvent]
  exact add_right_cancel hshift

/-! ### The unit group -/

variable (A) in
/-- **The automorphism of the unit group induced by a group element.** -/
abbrev unitsSmulAut (σ : G) : Aˣ ≃* Aˣ :=
  Units.mapEquiv (MulSemiringAction.toRingEquiv G A σ).toMulEquiv

@[simp]
theorem coe_unitsSmulAut (σ : G) (u : Aˣ) : ((unitsSmulAut A σ u : Aˣ) : A) = σ • (u : A) := rfl

/-- Powers of the induced automorphism of the unit group are induced by powers. -/
theorem coe_unitsSmulAut_pow (σ : G) (i : ℕ) (u : Aˣ) :
    (((unitsSmulAut A σ ^ i) u : Aˣ) : A) = (σ ^ i) • (u : A) := by
  induction i with
  | zero => simp
  | succ k ih => rw [mulPow_succ_apply, coe_unitsSmulAut, ih, smul_smul, ← pow_succ']

/-! ### The resolvent does not always vanish -/

variable [FaithfulSMul G A]

/-- **Some test element gives a resolvent that does not vanish.**  The conjugation maps are distinct
characters, so a vanishing resolvent for every test element would be a nontrivial linear relation
among them. -/
theorem exists_resolvent_ne_zero (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (hcard : Nat.card G = d)
    (hd : 0 < d) (x : A) : ∃ c : A, resolvent σ x d c ≠ 0 := by
  have horder : orderOf σ = d := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, hcard]
  by_contra hcon
  push_neg at hcon
  set φ : Fin d → (A →* A) :=
    fun i => (MulSemiringAction.toRingHom G A (σ ^ (i : ℕ))).toMonoidHom with hφ
  have hinj : Function.Injective φ := by
    intro i j hij
    have h1 : σ ^ (i : ℕ) = σ ^ (j : ℕ) :=
      eq_of_smul_eq_smul (α := A) fun a => congrArg (fun f : A →* A => f a) hij
    refine Fin.ext (pow_injOn_Iio_orderOf (x := σ) ?_ ?_ h1)
    · simp [horder]
    · simp [horder]
  have hli : LinearIndependent A (fun i : Fin d => ((φ i : A → A))) :=
    (linearIndependent_monoidHom A A).comp φ hinj
  have hsum : ∑ i : Fin d, partialConj σ x (i : ℕ) • ((φ i : A → A)) = 0 := by
    funext c
    have hc := hcon c
    rw [resolvent, ← Fin.sum_univ_eq_sum_range
      (fun i => partialConj σ x i * (σ ^ i) • c) d] at hc
    simpa [hφ] using hc
  have hzero := Fintype.linearIndependent_iff.mp hli _ hsum ⟨0, hd⟩
  simp only [partialConj_zero] at hzero
  exact one_ne_zero hzero

/-! ### Hilbert's theorem 90 -/

/-- **Hilbert's theorem 90.**  For a finite cyclic group acting faithfully on a field, an element
whose conjugates multiply to one is a quotient `σ y / y`. -/
theorem exists_smul_div_eq_of_prod_smul_eq_one [Finite G] (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hcard : Nat.card G = d) (u : Aˣ)
    (hu : ∏ i ∈ Finset.range d, (σ ^ i) • (u : A) = 1) :
    ∃ y : Aˣ, σ • (y : A) / (y : A) = (u : A) := by
  have horder : orderOf σ = d := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, hcard]
  have hd : 0 < d := by
    rw [← hcard]
    exact Nat.card_pos
  have hσd : σ ^ d = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one σ
  obtain ⟨c, hc⟩ := exists_resolvent_ne_zero hgen hcard hd (u : A)
  have hkey : (u : A) * σ • resolvent σ (u : A) d c = resolvent σ (u : A) d c :=
    mul_smul_resolvent hσd hu c
  have hsw : σ • resolvent σ (u : A) d c ≠ 0 := by
    intro h
    apply hc
    have hz : σ⁻¹ • (σ • resolvent σ (u : A) d c) = σ⁻¹ • (0 : A) := by rw [h]
    rwa [inv_smul_smul, smul_zero] at hz
  refine ⟨(Units.mk0 (resolvent σ (u : A) d c) hc)⁻¹, ?_⟩
  have hval : (((Units.mk0 (resolvent σ (u : A) d c) hc)⁻¹ : Aˣ) : A)
      = (resolvent σ (u : A) d c)⁻¹ := rfl
  have hinv : σ • (resolvent σ (u : A) d c)⁻¹ = (σ • resolvent σ (u : A) d c)⁻¹ := by simp
  rw [hval, hinv, inv_div_inv, div_eq_iff hsw]
  exact hkey.symm

/-- **The Tate group `Ĥ⁻¹` of the unit group of a field with a faithful cyclic action vanishes.**
This is Hilbert's theorem 90 in the language of Tate cohomology. -/
theorem tateHm1_unitsSmulAut_eq_zero [Finite G] (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hcard : Nat.card G = d) (c : tateHm1 (addAut (unitsSmulAut A σ)) d) : c = 0 := by
  refine tateHm1_eq_zero _ d (fun u hu => ?_) c
  have hcoe : ((∏ i ∈ Finset.range d, (unitsSmulAut A σ ^ i) u : Aˣ) : A)
      = ∏ i ∈ Finset.range d, (((unitsSmulAut A σ ^ i) u : Aˣ) : A) :=
    map_prod (Units.coeHom A) _ _
  have hu' : ∏ i ∈ Finset.range d, (σ ^ i) • (u : A) = 1 := by
    rw [← Finset.prod_congr rfl fun i (_ : i ∈ Finset.range d) => coe_unitsSmulAut_pow σ i u,
      ← hcoe, hu, Units.val_one]
  obtain ⟨y, hy⟩ := exists_smul_div_eq_of_prod_smul_eq_one hgen hcard u hu'
  refine ⟨y, Units.ext ?_⟩
  rw [Units.val_div_eq_div_val, coe_unitsSmulAut]
  exact hy

end InverseGalois.CFT

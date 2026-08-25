/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CyclicCoboundary
import InverseGalois.CFT.GroupCohomology.CyclicSurjective

/-!
# Two-cocycles of a finite cyclic group with values in a subgroup of norms

Asking that *every* invariant element of the module be a norm is a strong hypothesis: for the
multiplicative group of a local field it is exactly the local reciprocity law.  A two-cocycle whose
values all lie in a small subgroup `A` needs much less, because the class of such a cocycle in the
second cohomology is represented by the product of the values of the cocycle along a generator, and
that product again lies in `A`.  So it is enough that every element of `A` be a norm.

The gain is that on the subgroups one meets in practice the norm is elementary.  If every element
of `A` is fixed by the group, then the norm of an element `y` of `A` is `y ^ (Nat.card G)`, so the
hypothesis becomes the concrete statement that every element of `A` is a `Nat.card G`-th power of an
invariant element; `exists_sub_add_eq_of_forall_exists_nsmul` is that form.

As in `InverseGalois.CFT.CyclicCoboundary`, the statements come both for an action by group
automorphisms of a commutative group and for an action by additive automorphisms of an additive
group.

## Main results

* `InverseGalois.CFT.isMulCoboundary₂_of_forall_mem`: **a multiplicative two-cocycle of a finite
  cyclic group taking values in a subgroup of invariant norms is a coboundary.**
* `InverseGalois.CFT.exists_sub_add_eq_of_forall_mem`: the same statement for an action by additive
  automorphisms.
* `InverseGalois.CFT.exists_sub_add_eq_of_forall_exists_nsmul`: **a two-cocycle for an action by
  additive automorphisms of a finite cyclic group is a coboundary** as soon as each of its values is
  the multiple by the order of the group of an invariant element.

## Tags

cyclic group, group cohomology, two-cocycle, coboundary, norm
-/

open groupCohomology

namespace InverseGalois.CFT

/-! ### An action by group automorphisms -/

section Mul

variable {G M : Type} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

/-- **A multiplicative two-cocycle of a finite cyclic group whose values lie in a subgroup of
invariant elements which are norms is a coboundary.**  Only the elements of the subgroup are asked
to be norms, because normalising the cocycle at the identity and taking the product of its values
along a generator produces an invariant element of that subgroup which carries the whole
cohomology class. -/
theorem isMulCoboundary₂_of_forall_mem {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    {A : Subgroup M} (hAinv : ∀ a ∈ A, ∀ σ : G, σ • a = a)
    (hAnorm : ∀ a ∈ A, ∃ m : M, ∏ σ : G, σ • m = a)
    {f : G × G → M} (hf : IsMulCocycle₂ f) (hfA : ∀ p, f p ∈ A) :
    IsMulCoboundary₂ f := by
  classical
  have hcA : f (1, 1) ∈ A := hfA _
  have hcinv : ∀ σ : G, σ • f (1, 1) = f (1, 1) := hAinv _ hcA
  have hf' : IsMulCocycle₂ fun p : G × G => f p / f (1, 1) := by
    have h := isMulCocycle₂_div_smul hf (f (1, 1))
    have he : (fun p : G × G => f p / p.1 • f (1, 1)) = fun p : G × G => f p / f (1, 1) := by
      funext p
      rw [hcinv]
    rwa [he] at h
  have hf'1 : (fun p : G × G => f p / f (1, 1)) (1, 1) = 1 := div_self' _
  have hf'A : ∀ p : G × G, f p / f (1, 1) ∈ A := fun p => A.div_mem (hfA p) hcA
  have hmem : cocyclePartial g (fun p : G × G => f p / f (1, 1)) (Nat.card G) ∈ A :=
    Subgroup.prod_mem _ fun j _ => hf'A _
  obtain ⟨m, hm⟩ := hAnorm _ hmem
  have h1 := isMulCoboundary₂_div_cyclicCocycle_of_map_one hg hf' hf'1
  have h2 := isMulCoboundary₂_cyclicCocycle hg hm
  have h3 : IsMulCoboundary₂ (fun p : G × G => f p / f (1, 1)) := by
    have h := Cohomologous.isMulCoboundary₂_mul h1 h2
    simpa only [div_mul_cancel] using h
  obtain ⟨x, hx⟩ := h3
  refine ⟨fun σ => x σ * f (1, 1), fun σ τ => ?_⟩
  have hxst : σ • x τ / x (σ * τ) * x σ = f (σ, τ) / f (1, 1) := hx σ τ
  show σ • (x τ * f (1, 1)) / (x (σ * τ) * f (1, 1)) * (x σ * f (1, 1)) = f (σ, τ)
  rw [smul_mul', hcinv]
  have e : σ • x τ * f (1, 1) / (x (σ * τ) * f (1, 1)) * (x σ * f (1, 1))
      = σ • x τ / x (σ * τ) * x σ * f (1, 1) := by
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_div]
    abel
  rw [e, hxst, div_mul_cancel]

end Mul

/-! ### An action by additive automorphisms -/

section Add

variable {G M : Type} [Group G] [Fintype G] [AddCommGroup M]

/-- **A two-cocycle for an action by additive automorphisms of a finite cyclic group whose values
lie in a subgroup of invariant elements which are norms is a coboundary.** -/
theorem exists_sub_add_eq_of_forall_mem (φ : G →* AddAut M) {g : G}
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) {A : AddSubgroup M}
    (hAinv : ∀ a ∈ A, ∀ σ : G, φ σ a = a)
    (hAnorm : ∀ a ∈ A, ∃ m : M, ∑ σ : G, φ σ m = a)
    {f : G → G → M} (hfA : ∀ x y, f x y ∈ A)
    (hf : ∀ x y z : G, φ x (f y z) + f x (y * z) = f (x * y) z + f x y) :
    ∃ c : G → M, ∀ x y : G, f x y = φ x (c y) - c (x * y) + c x := by
  letI := addAutMulDistribMulAction φ
  have hsmul : ∀ (σ : G) (a : Multiplicative M),
      σ • a = Multiplicative.ofAdd (φ σ a.toAdd) := fun _ _ => rfl
  have hcyc : IsMulCocycle₂ (M := Multiplicative M)
      fun p : G × G => Multiplicative.ofAdd (f p.1 p.2) := by
    intro x y z
    show Multiplicative.ofAdd (f (x * y) z) * Multiplicative.ofAdd (f x y)
      = Multiplicative.ofAdd (φ x (f y z)) * Multiplicative.ofAdd (f x (y * z))
    rw [← ofAdd_add, ← ofAdd_add]
    exact congrArg Multiplicative.ofAdd (hf x y z).symm
  have hinv : ∀ a ∈ A.toSubgroup, ∀ σ : G, σ • a = a := by
    intro a ha σ
    rw [hsmul]
    exact congrArg Multiplicative.ofAdd (hAinv a.toAdd ha σ)
  have hnorm : ∀ a ∈ A.toSubgroup, ∃ m : Multiplicative M, ∏ σ : G, σ • m = a := by
    intro a ha
    obtain ⟨m, hm⟩ := hAnorm a.toAdd ha
    refine ⟨Multiplicative.ofAdd m, ?_⟩
    have hp : ∏ σ : G, σ • Multiplicative.ofAdd m
        = Multiplicative.ofAdd (∑ σ : G, φ σ m) := by
      rw [ofAdd_sum]
      rfl
    rw [hp, hm]
    rfl
  obtain ⟨c, hc⟩ := isMulCoboundary₂_of_forall_mem hg hinv hnorm hcyc fun p => hfA p.1 p.2
  refine ⟨fun x => (c x).toAdd, fun x y => ?_⟩
  have hxy := hc x y
  rw [hsmul] at hxy
  simpa [← ofAdd_sub, ← ofAdd_add] using hxy.symm

/-- **A two-cocycle for an action by additive automorphisms of a finite cyclic group is a
coboundary as soon as each of its values is the multiple by the order of the group of an invariant
element.**  The norm of an invariant element is that multiple of it, so this is the concrete form
of the hypothesis that the values of the cocycle are norms. -/
theorem exists_sub_add_eq_of_forall_exists_nsmul (φ : G →* AddAut M) {g : G}
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) {A : AddSubgroup M}
    (hA : ∀ a ∈ A, ∃ y : M, (∀ σ : G, φ σ y = y) ∧ Nat.card G • y = a)
    {f : G → G → M} (hfA : ∀ x y, f x y ∈ A)
    (hf : ∀ x y z : G, φ x (f y z) + f x (y * z) = f (x * y) z + f x y) :
    ∃ c : G → M, ∀ x y : G, f x y = φ x (c y) - c (x * y) + c x := by
  refine exists_sub_add_eq_of_forall_mem φ hg (fun a ha σ => ?_) (fun a ha => ?_) hfA hf
  · obtain ⟨y, hy, hya⟩ := hA a ha
    rw [← hya, map_nsmul, hy]
  · obtain ⟨y, hy, hya⟩ := hA a ha
    refine ⟨y, ?_⟩
    rw [Finset.sum_congr rfl fun σ _ => hy σ, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hya]

end Add

end InverseGalois.CFT

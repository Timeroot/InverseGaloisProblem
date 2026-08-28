/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Herbrand
import InverseGalois.CFT.GroupCohomology.Cohomologous
import InverseGalois.CFT.GroupCohomology.CyclicH2

/-!
# Two-cocycles of a finite cyclic group are coboundaries when every invariant is a norm

The second cohomology of a finite cyclic group `G` acting on an abelian group `M` is the Tate
group `M ^ G / N M`, so it vanishes as soon as every `G`-invariant element of `M` is a norm.  This
file records the elementary consequence of that computation: under this hypothesis every
two-cocycle on `G` with values in `M` is a coboundary, with an explicit one-cochain.

The statement is given both for an action by group automorphisms of a commutative group and, in the
form the local theory of a valued field wants, for an action by additive automorphisms of an
additive group.  The two are exchanged through the multiplicative copy of an additive group.

A cyclic group also lets one replace the sum over the whole group in the norm by the geometric sum
over the powers of a generator, which is the shape the Tate formalism of a single automorphism
uses; `sum_eq_normHom` performs that translation.

## Main definitions

* `InverseGalois.CFT.addAutMulDistribMulAction`: an action by additive automorphisms of an additive
  group, read as an action by group automorphisms of its multiplicative copy.

## Main results

* `InverseGalois.CFT.isMulCoboundary₂_of_forall_isNorm`: **a multiplicative two-cocycle of a finite
  cyclic group is a coboundary** when every invariant element is a norm.
* `InverseGalois.CFT.exists_sub_add_eq_of_forall_isNorm`: the same statement for an action by
  additive automorphisms.
* `InverseGalois.CFT.sum_eq_normHom`: the sum over a finite cyclic group of the translates of an
  element is the geometric sum of the powers of a generator.
* `InverseGalois.CFT.exists_sub_add_eq_of_forall_exists_normHom`: **a two-cocycle for an action by
  additive automorphisms of a finite cyclic group is a coboundary** when every invariant element is
  in the range of the norm operator of a generator.

## Tags

cyclic group, group cohomology, two-cocycle, coboundary, norm, Tate group
-/

open groupCohomology

namespace InverseGalois.CFT

/-! ### An action by group automorphisms -/

section Mul

variable {G M : Type} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

/-- **A multiplicative two-cocycle of a finite cyclic group is a coboundary** as soon as every
invariant element of the module is a norm: the second cohomology of a finite cyclic group is the
quotient of the invariants by the norms. -/
theorem isMulCoboundary₂_of_forall_isNorm {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hnorm : ∀ a : M, (∀ σ : G, σ • a = a) → ∃ m : M, ∏ σ : G, σ • m = a)
    {f : G × G → M} (hf : IsMulCocycle₂ f) : IsMulCoboundary₂ f := by
  haveI := CyclicH2.subsingleton_h2 hg fun a ha => hnorm a ha
  exact (H2π_eq_zero_iff_isMulCoboundary₂ hf).1 (Subsingleton.elim _ _)

end Mul

/-! ### An action by additive automorphisms -/

section Add

variable {G M : Type} [Group G] [Fintype G] [AddCommGroup M]

/-- An action by additive automorphisms, read as an action by group automorphisms of the
multiplicative copy of the group. -/
def addAutMulDistribMulAction (φ : G →* AddAut M) :
    MulDistribMulAction G (Multiplicative M) where
  smul σ a := Multiplicative.ofAdd (φ σ a.toAdd)
  one_smul a := by
    show Multiplicative.ofAdd (φ 1 a.toAdd) = a
    rw [map_one]
    rfl
  mul_smul σ τ a := by
    show Multiplicative.ofAdd (φ (σ * τ) a.toAdd) = Multiplicative.ofAdd (φ σ (φ τ a.toAdd))
    rw [map_mul]
    rfl
  smul_mul σ a b := by
    show Multiplicative.ofAdd (φ σ (a.toAdd + b.toAdd))
      = Multiplicative.ofAdd (φ σ a.toAdd) * Multiplicative.ofAdd (φ σ b.toAdd)
    rw [map_add]
    rfl
  smul_one σ := by
    show Multiplicative.ofAdd (φ σ 0) = 1
    rw [map_zero]
    rfl

/-- **A two-cocycle for an action of a finite cyclic group by additive automorphisms is a
coboundary** as soon as every invariant element is a sum of translates. -/
theorem exists_sub_add_eq_of_forall_isNorm (φ : G →* AddAut M) {g : G}
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hnorm : ∀ a : M, (∀ σ : G, φ σ a = a) → ∃ m : M, ∑ σ : G, φ σ m = a)
    {f : G → G → M} (hf : ∀ x y z : G, φ x (f y z) + f x (y * z) = f (x * y) z + f x y) :
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
  have hn : ∀ a : Multiplicative M, (∀ σ : G, σ • a = a) →
      ∃ m : Multiplicative M, ∏ σ : G, σ • m = a := by
    intro a ha
    obtain ⟨m, hm⟩ := hnorm a.toAdd fun σ => congrArg Multiplicative.toAdd (ha σ)
    refine ⟨Multiplicative.ofAdd m, ?_⟩
    have hp : ∏ σ : G, σ • Multiplicative.ofAdd m
        = Multiplicative.ofAdd (∑ σ : G, φ σ m) := by
      rw [ofAdd_sum]
      rfl
    rw [hp, hm]
    rfl
  obtain ⟨c, hc⟩ := isMulCoboundary₂_of_forall_isNorm hg hn hcyc
  refine ⟨fun x => (c x).toAdd, fun x y => ?_⟩
  have hxy := hc x y
  rw [hsmul] at hxy
  simpa [← ofAdd_sub, ← ofAdd_add] using hxy.symm

end Add

/-! ### The norm of a generator -/

section Bridge

variable {G M : Type*} [Group G] [Fintype G] [AddCommGroup M]

/-- **The sum over a finite cyclic group of the translates of an element is the geometric sum of
the powers of a generator**: the powers below the order of the generator enumerate the group. -/
theorem sum_eq_normHom (φ : G →* AddAut M) {g : G} (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    {d : ℕ} (hd : Nat.card G = d) (m : M) :
    ∑ σ : G, φ σ m = normHom (φ g) d m := by
  classical
  have hord : orderOf g = d := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hd
  rw [normHom_apply]
  refine (Finset.sum_nbij (i := fun n : ℕ => g ^ n) (fun _ _ => Finset.mem_univ _) ?_ ?_
    ?_).symm
  · rw [Finset.coe_range, ← hord]
    exact pow_injOn_Iio_orderOf
  · intro σ _
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 ((IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
      (isOfFinOrder_of_finite g)).1 (hg σ))
    exact ⟨n, by simpa [hord] using Finset.mem_range.1 hn, rfl⟩
  · intro n _
    rw [map_pow]

end Bridge

/-! ### The two statements combined -/

section Combined

variable {G M : Type} [Group G] [Fintype G] [AddCommGroup M]

/-- **A two-cocycle for an action of a finite cyclic group by additive automorphisms is a
coboundary** as soon as every invariant element lies in the range of the norm operator of a
generator. -/
theorem exists_sub_add_eq_of_forall_exists_normHom (φ : G →* AddAut M) {g : G}
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) {d : ℕ} (hd : Nat.card G = d)
    (hnorm : ∀ a : M, (∀ σ : G, φ σ a = a) → ∃ m : M, normHom (φ g) d m = a)
    {f : G → G → M} (hf : ∀ x y z : G, φ x (f y z) + f x (y * z) = f (x * y) z + f x y) :
    ∃ c : G → M, ∀ x y : G, f x y = φ x (c y) - c (x * y) + c x :=
  exists_sub_add_eq_of_forall_isNorm φ hg
    (fun a ha => (hnorm a ha).imp fun m hm => (sum_eq_normHom φ hg hd m).trans hm) hf

end Combined

end InverseGalois.CFT

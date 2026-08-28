/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The first cohomology of a cyclic group

Let `G` be a finite cyclic group with generator `g`, acting on a module `A`.  A `1`-cocycle `x` is
determined by its value at `g`, because the cocycle relation propagates that value along the powers
of `g`: one has `x (g ^ m) = ∑ i < m, g ^ i • x g`.  Taking `m` to be the order of `G` and using
`x 1 = 0` shows that `x g` lies in the kernel of the norm operator `∑ g' ∈ G, g' • -`.  Conversely,
if `x g = g • b - b` for some `b`, then the same propagation gives `x (g ^ m) = g ^ m • b - b` for
every `m`, so `x` is the coboundary of `b`.

Consequently the first cohomology of a finite cyclic group vanishes as soon as the kernel of the
norm operator is contained in the image of `g - 1`, which is the cohomological form of Hilbert's
theorem 90.

## Main results

* `InverseGalois.CFT.sum_range_card_pow`: a sum over a finite cyclic group is the sum of the values
  at the powers of a generator below the order.
* `InverseGalois.CFT.cocycles₁_apply_pow`: the value of a `1`-cocycle at a power of an element.
* `InverseGalois.CFT.norm_cocycles₁_apply`: the value of a `1`-cocycle at a generator of a finite
  cyclic group lies in the kernel of the norm operator.
* `InverseGalois.CFT.eq_zero_of_ker_norm`: **the first cohomology of a finite cyclic group vanishes
  when the kernel of the norm operator is the image of `g - 1`.**
* `InverseGalois.CFT.subsingleton_H1_of_ker_norm`: the same statement, phrased as a `Subsingleton`
  instance for the cohomology group.

## Tags

group cohomology, cyclic group, Hilbert theorem 90, norm operator
-/

universe u

open groupCohomology

namespace InverseGalois.CFT

section Sum

/-- A sum over a finite cyclic group is the sum of the values at the powers of a generator below
the order of the group. -/
theorem sum_range_card_pow {α : Type*} [Group α] [Fintype α] {a : α}
    (ha : ∀ x : α, x ∈ Subgroup.zpowers a) {H : Type*} [AddCommMonoid H] (f : α → H) :
    ∑ i ∈ Finset.range (Nat.card α), f (a ^ i) = ∑ x : α, f x := by
  classical
  have horder : orderOf a = Nat.card α := orderOf_eq_card_of_forall_mem_zpowers ha
  have hinj : Set.InjOn (fun i => a ^ i) (Finset.range (Nat.card α) : Finset ℕ) := by
    intro i hi j hj hij
    refine pow_injOn_Iio_orderOf (x := a) ?_ ?_ hij
    · simpa [horder] using Finset.mem_range.mp hi
    · simpa [horder] using Finset.mem_range.mp hj
  rw [← IsCyclic.image_range_card ha, Finset.sum_image hinj]

end Sum

section Cyclic

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {A : Rep k G}

omit [Fintype G] in
/-- The cocycle relation propagates the value of a `1`-cocycle along the powers of an element. -/
theorem cocycles₁_apply_pow (x : cocycles₁ A) (g : G) (m : ℕ) :
    (x : G → A) (g ^ m) = ∑ i ∈ Finset.range m, A.ρ (g ^ i) ((x : G → A) g) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, (mem_cocycles₁_iff (x : G → A)).1 x.2, ih, Finset.sum_range_succ, add_comm]

/-- The value of a `1`-cocycle at a generator of a finite cyclic group lies in the kernel of the
norm operator. -/
theorem norm_cocycles₁_apply {g : G} (hg : ∀ s : G, s ∈ Subgroup.zpowers g)
    (x : cocycles₁ A) : A.ρ.norm ((x : G → A) g) = 0 := by
  have h1 : ∑ i ∈ Finset.range (Nat.card G), A.ρ (g ^ i) ((x : G → A) g) = 0 := by
    rw [← cocycles₁_apply_pow x g, pow_card_eq_one']
    exact cocycles₁_map_one x
  rw [Representation.norm, LinearMap.sum_apply,
    ← sum_range_card_pow hg fun s : G => A.ρ s ((x : G → A) g)]
  exact h1

omit [Fintype G] in
/-- A `1`-cocycle whose value at `g` is `g • b - b` is the coboundary of `b` along the powers
of `g`. -/
theorem cocycles₁_apply_pow_of_sub (x : cocycles₁ A) (g : G) {b : A}
    (hb : A.ρ g b - b = (x : G → A) g) (m : ℕ) :
    (x : G → A) (g ^ m) = A.ρ (g ^ m) b - b := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, (mem_cocycles₁_iff (x : G → A)).1 x.2, ih, ← hb, map_sub,
      map_mul A.ρ (g ^ m) g, Module.End.mul_apply]
    abel

/-- **The first cohomology of a finite cyclic group vanishes** as soon as every element killed by
the norm operator is of the form `g • b - b` for a generator `g`. -/
theorem eq_zero_of_ker_norm {g : G} (hg : ∀ s : G, s ∈ Subgroup.zpowers g)
    (hker : ∀ a : A, A.ρ.norm a = 0 → ∃ b : A, A.ρ g b - b = a)
    (x : groupCohomology A 1) : x = 0 := by
  induction x using H1_induction_on with
  | h x =>
    obtain ⟨b, hb⟩ := hker _ (norm_cocycles₁_apply hg x)
    refine (H1π_eq_zero_iff _).2 ⟨b, funext fun s => ?_⟩
    obtain ⟨m, rfl⟩ := mem_powers_iff_mem_zpowers.2 (hg s)
    exact (cocycles₁_apply_pow_of_sub x g hb m).symm

/-- The first cohomology of a finite cyclic group has at most one element as soon as every element
killed by the norm operator is of the form `g • b - b` for a generator `g`. -/
theorem subsingleton_H1_of_ker_norm {g : G} (hg : ∀ s : G, s ∈ Subgroup.zpowers g)
    (hker : ∀ a : A, A.ρ.norm a = 0 → ∃ b : A, A.ρ g b - b = a) :
    Subsingleton (groupCohomology A 1) :=
  ⟨fun x y => by rw [eq_zero_of_ker_norm hg hker x, eq_zero_of_ker_norm hg hker y]⟩

end Cyclic

end InverseGalois.CFT

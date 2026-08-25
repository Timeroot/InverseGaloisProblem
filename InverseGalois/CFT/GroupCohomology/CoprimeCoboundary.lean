/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A two-cocycle killed by an integer coprime to the order of the group is a coboundary

Summing the cocycle identity over the third variable turns the order of the group into a
coboundary: for a finite group `G` acting on an abelian group `M` and a two-cocycle `f`, the
multiple `|G| • f` is the coboundary of `y ↦ ∑ z, f y z`.  A two-cocycle which is itself killed by
an integer `n` coprime to `|G|` is therefore a coboundary, because a Bézout combination of `|G|`
and `n` is one.

This is the mechanism behind the vanishing of the cohomology of a finite group with coefficients of
coprime order.  In the arithmetic of a `p`-extension of number fields with `p` odd it makes the
archimedean places invisible: the decomposition group at an infinite place has order at most two
while the coefficients are killed by an odd prime.

## Main results

* `InverseGalois.CFT.nsmul_card_eq_of_isCocycle₂`: the order of the group times a two-cocycle is
  the coboundary of the sum of the cocycle over its second variable.
* `InverseGalois.CFT.exists_sub_add_eq_of_coprime`: **a two-cocycle killed by an integer coprime to
  the order of the group is a coboundary.**

## Tags

group cohomology, two-cocycle, coboundary, coprime, transfer, Bézout
-/

namespace InverseGalois.CFT

section Add

variable {G M : Type*} [Group G] [Fintype G] [AddCommGroup M]

/-- **The order of the group times a two-cocycle is a coboundary**, namely the coboundary of the
sum of the cocycle over its second variable.  Summing the cocycle identity over the third variable
reindexes two of the three sums into that one and leaves the third as a constant sum. -/
theorem nsmul_card_eq_of_isCocycle₂ (φ : G →* AddAut M)
    {f : G → G → M} (hf : ∀ x y z : G, φ x (f y z) + f x (y * z) = f (x * y) z + f x y)
    (x y : G) :
    Nat.card G • f x y
      = φ x (∑ z : G, f y z) - (∑ z : G, f (x * y) z) + ∑ z : G, f x z := by
  classical
  have hsum : ∑ z : G, (φ x (f y z) + f x (y * z)) = ∑ z : G, (f (x * y) z + f x y) :=
    Finset.sum_congr rfl fun z _ => hf x y z
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have h1 : ∑ z : G, φ x (f y z) = φ x (∑ z : G, f y z) := (map_sum (φ x) _ _).symm
  have h2 : ∑ z : G, f x (y * z) = ∑ z : G, f x z :=
    Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun _ => rfl
  have h3 : ∑ _z : G, f x y = Nat.card G • f x y := by
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [h1, h2, h3] at hsum
  have h4 : φ x (∑ z : G, f y z) + (∑ z : G, f x z) - ∑ z : G, f (x * y) z
      = Nat.card G • f x y := by
    rw [hsum]; abel
  rw [← h4]; abel

/-- **A two-cocycle killed by an integer coprime to the order of the group is a coboundary.**  The
order of the group times the cocycle is already a coboundary, and a Bézout combination of that
multiple with the multiple that kills the cocycle is the cocycle itself. -/
theorem exists_sub_add_eq_of_coprime (φ : G →* AddAut M) {n : ℕ}
    (hcop : Nat.Coprime (Nat.card G) n)
    {f : G → G → M} (hf : ∀ x y z : G, φ x (f y z) + f x (y * z) = f (x * y) z + f x y)
    (hn : ∀ x y : G, n • f x y = 0) :
    ∃ c : G → M, ∀ x y : G, f x y = φ x (c y) - c (x * y) + c x := by
  classical
  obtain ⟨u, v, huv⟩ : IsCoprime ((Nat.card G : ℤ)) (n : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  refine ⟨fun y => u • ∑ z : G, f y z, fun x y => ?_⟩
  have hz : ((n : ℤ)) • f x y = 0 := by
    rw [natCast_zsmul]; exact hn x y
  have hm : ((Nat.card G : ℤ)) • f x y
      = φ x (∑ z : G, f y z) - (∑ z : G, f (x * y) z) + ∑ z : G, f x z := by
    rw [natCast_zsmul]; exact nsmul_card_eq_of_isCocycle₂ φ hf x y
  have hone : f x y = (u * (Nat.card G : ℤ) + v * (n : ℤ)) • f x y := by rw [huv, one_zsmul]
  rw [hone, add_zsmul, mul_zsmul, mul_zsmul, hz, hm, smul_zero, add_zero, map_zsmul, smul_add,
    smul_sub]

end Add

end InverseGalois.CFT

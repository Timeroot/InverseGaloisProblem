/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Semiabelian

/-!
# Metacyclic groups are semiabelian

A finite group `G` is **metacyclic** when it carries a normal subgroup `N` such that both `N` and
the quotient `G ⧸ N` are cyclic.  This file shows that every such group belongs to Dentzer's class
of semiabelian groups, so that the wreath-product machinery realizes it regularly over `ℚ(T)`.

The argument is a presentation argument.  Write `m` for the order of `N` and `r` for the order of
`G ⧸ N`, pick `b : G` whose class generates `G ⧸ N`, and let `c : MulAut N` be conjugation by `b`.
Then `b ^ r` lies in `N`, so `c ^ r` is conjugation by an element of the abelian group `N` and
hence trivial, while `b ^ (r * m) = (b ^ r) ^ m = 1`.  Consequently both `c` and `b` are killed by
the exponent `r * m`, so they define homomorphisms out of the cyclic group of order `r * m`, and
the split extension

`Multiplicative (ZMod m) ⋊ Multiplicative (ZMod (r * m))`

built from `c` maps onto `G`, sending the left generator into `N` and the right generator to `b`.
The split extension is semiabelian by the very definition of the class, and `G` is a homomorphic
image of it.  The non-split extensions are reached exactly through this last step: the generalized
quaternion group `QuaternionGroup n` is metacyclic but not a semidirect product, and it is the
headline application recorded below.

## Main results

* `Semiabelian.zmodHomOfPowEqOne` — the homomorphism out of `Multiplicative (ZMod j)` determined by
  an element whose `j`-th power is the identity.
* `IsSemiabelian.of_isCyclic_of_isCyclic_quotient` — a finite group with a cyclic normal subgroup
  with cyclic quotient is semiabelian.
* `IsSemiabelian.of_isCyclic_of_prime_index` — the special case of a cyclic normal subgroup of
  prime index.
* `IsSemiabelian.quaternion` — every generalized quaternion group `QuaternionGroup n` with `n ≠ 0`
  is semiabelian.
* `IsSemiabelian.semidirect_commGroup` — a semidirect product of two finite abelian groups is
  semiabelian.
-/

namespace Semiabelian

/-- If the `j`-th power of `k` is the identity, then a power of `k` only depends on its exponent
modulo `j`. -/
theorem pow_mod_eq_pow {K : Type*} [Group K] {j : ℕ} {k : K} (hk : k ^ j = 1) (a : ℕ) :
    k ^ (a % j) = k ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a j]
  rw [pow_add, pow_mul, hk, one_pow, one_mul]

/-- A homomorphism out of the multiplicative cyclic group `Multiplicative (ZMod j)` is determined
by an element `k` whose `j`-th power is the identity: the class of `x` is sent to `k ^ x.val`. -/
def zmodHomOfPowEqOne {K : Type*} [Group K] (j : ℕ) [NeZero j] (k : K) (hk : k ^ j = 1) :
    Multiplicative (ZMod j) →* K where
  toFun x := k ^ (Multiplicative.toAdd x).val
  map_one' := by
    show k ^ (0 : ZMod j).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' x y := by
    show k ^ (Multiplicative.toAdd x + Multiplicative.toAdd y).val
      = k ^ (Multiplicative.toAdd x).val * k ^ (Multiplicative.toAdd y).val
    rw [ZMod.val_add, pow_mod_eq_pow hk, pow_add]

@[simp]
theorem zmodHomOfPowEqOne_ofAdd {K : Type*} [Group K] (j : ℕ) [NeZero j] (k : K) (hk : k ^ j = 1)
    (x : ZMod j) : zmodHomOfPowEqOne j k hk (Multiplicative.ofAdd x) = k ^ x.val := rfl

/-- The homomorphism attached to `k` sends the standard generator of `Multiplicative (ZMod j)`
to `k`. -/
theorem zmodHomOfPowEqOne_ofAdd_one {K : Type*} [Group K] (j : ℕ) [NeZero j] (k : K)
    (hk : k ^ j = 1) : zmodHomOfPowEqOne j k hk (Multiplicative.ofAdd (1 : ZMod j)) = k := by
  rw [zmodHomOfPowEqOne_ofAdd, ZMod.val_one_eq_one_mod, pow_mod_eq_pow hk, pow_one]

/-- The image of the homomorphism attached to `k` contains every power of `k`. -/
theorem zpowers_le_range_zmodHomOfPowEqOne {K : Type*} [Group K] (j : ℕ) [NeZero j] (k : K)
    (hk : k ^ j = 1) : Subgroup.zpowers k ≤ (zmodHomOfPowEqOne j k hk).range :=
  Subgroup.zpowers_le.2 ⟨Multiplicative.ofAdd 1, zmodHomOfPowEqOne_ofAdd_one j k hk⟩

/-- The powers of `QuaternionGroup.a 1`, as a homomorphism from the cyclic group of order `2 * n`
into the generalized quaternion group of order `4 * n`. -/
def quaternionAHom (n : ℕ) : Multiplicative (ZMod (2 * n)) →* QuaternionGroup n where
  toFun i := QuaternionGroup.a (Multiplicative.toAdd i)
  map_one' := QuaternionGroup.a_zero
  map_mul' _ _ := (QuaternionGroup.a_mul_a _ _).symm

@[simp]
theorem quaternionAHom_apply (n : ℕ) (i : Multiplicative (ZMod (2 * n))) :
    quaternionAHom n i = QuaternionGroup.a (Multiplicative.toAdd i) := rfl

/-- Distinct exponents give distinct powers of `QuaternionGroup.a 1`. -/
theorem quaternionAHom_injective (n : ℕ) : Function.Injective (quaternionAHom n) := by
  intro i i' h
  simpa using h

end Semiabelian

namespace IsSemiabelian

/-- **Every finite metacyclic group is semiabelian**: if `N` is a cyclic normal subgroup of a
finite group `G` and the quotient `G ⧸ N` is cyclic as well, then `G` is a homomorphic image of a
semidirect product of two finite cyclic groups, namely of `N` by a cyclic group of order
`Nat.card (G ⧸ N) * Nat.card N` acting through conjugation by a lift of a generator of the
quotient. -/
theorem of_isCyclic_of_isCyclic_quotient {G : Type} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] [IsCyclic ↥N] [IsCyclic (G ⧸ N)] : IsSemiabelian G := by
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N q
  have hm0 : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
  have hr0 : Nat.card (G ⧸ N) ≠ 0 := Nat.card_pos.ne'
  haveI : NeZero (Nat.card ↥N) := ⟨hm0⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = Nat.card (G ⧸ N) * Nat.card ↥N := ⟨_, rfl⟩
  haveI : NeZero j := ⟨by rw [hj]; exact mul_ne_zero hr0 hm0⟩
  -- the `Nat.card (G ⧸ N)`-th power of the lift `b` already lies in `N`
  have hbr : b ^ Nat.card (G ⧸ N) ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact pow_card_eq_one'
  -- hence `b` is killed by the exponent `j`
  have hb : b ^ j = 1 := by
    have h1 : (⟨b ^ Nat.card (G ⧸ N), hbr⟩ : ↥N) ^ Nat.card ↥N = 1 := pow_card_eq_one'
    have h2 := congrArg (Subgroup.subtype N) h1
    rw [map_pow, map_one] at h2
    rw [hj, pow_mul]
    exact h2
  -- and so is conjugation by `b`, since `N` is abelian
  have hc1 : (MulAut.conjNormal b : MulAut ↥N) ^ Nat.card (G ⧸ N) = 1 := by
    rw [← map_pow]
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have hcomm : b ^ Nat.card (G ⧸ N) * (x : G) = (x : G) * b ^ Nat.card (G ⧸ N) := by
      simpa using congrArg (Subgroup.subtype N)
        (IsCyclic.commutative.comm (⟨b ^ Nat.card (G ⧸ N), hbr⟩ : ↥N) x)
    rw [MulAut.conjNormal_apply]
    show b ^ Nat.card (G ⧸ N) * (x : G) * (b ^ Nat.card (G ⧸ N))⁻¹ = (x : G)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hcj : (MulAut.conjNormal b : MulAut ↥N) ^ j = 1 := by
    rw [hj, pow_mul, hc1, one_pow]
  -- realize the abelian group `N` as a standard cyclic group
  have hcard : Nat.card (Multiplicative (ZMod (Nat.card ↥N))) = Nat.card ↥N := by
    simp [Nat.card_eq_fintype_card]
  obtain ⟨e⟩ : Nonempty (Multiplicative (ZMod (Nat.card ↥N)) ≃* ↥N) :=
    ⟨mulEquivOfCyclicCardEq hcard⟩
  have hcA : (MulAut.congr e.symm (MulAut.conjNormal b) :
      MulAut (Multiplicative (ZMod (Nat.card ↥N)))) ^ j = 1 := by
    rw [← map_pow, hcj, map_one]
  have hkey : ∀ (v : ℕ) (a : Multiplicative (ZMod (Nat.card ↥N))),
      ((e ((MulAut.congr e.symm (MulAut.conjNormal b) ^ v) a) : ↥N) : G)
        = b ^ v * ((e a : ↥N) : G) * (b ^ v)⁻¹ := by
    intro v a
    have h1 : (MulAut.congr e.symm (MulAut.conjNormal b) :
        MulAut (Multiplicative (ZMod (Nat.card ↥N)))) ^ v
          = MulAut.congr e.symm (MulAut.conjNormal (b ^ v)) := by
      rw [← map_pow, ← map_pow]
    have h2 : (MulAut.congr e.symm (MulAut.conjNormal (b ^ v))) a
        = e.symm (MulAut.conjNormal (b ^ v) (e a)) := rfl
    rw [h1, h2, MulEquiv.apply_symm_apply, MulAut.conjNormal_apply]
  refine (IsSemiabelian.semidirect (Semiabelian.zmodHomOfPowEqOne j _ hcA)
    (of_commGroup (Multiplicative (ZMod j)))).of_surjective
      (SemidirectProduct.lift ((Subgroup.subtype N).comp e.toMonoidHom)
        (Semiabelian.zmodHomOfPowEqOne j b hb) ?_) ?_
  · intro x
    refine MonoidHom.ext fun a => ?_
    show ((e ((MulAut.congr e.symm (MulAut.conjNormal b) ^
        (Multiplicative.toAdd x).val) a) : ↥N) : G)
      = b ^ (Multiplicative.toAdd x).val * ((e a : ↥N) : G) *
          (b ^ (Multiplicative.toAdd x).val)⁻¹
    exact hkey _ _
  · intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hq (QuotientGroup.mk' N g))
    have hmem : g * (b ^ i)⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, map_zpow, hi,
        mul_inv_cancel]
    obtain ⟨y, hy⟩ := Semiabelian.zpowers_le_range_zmodHomOfPowEqOne j b hb
      (Subgroup.mem_zpowers_iff.2 ⟨i, rfl⟩)
    refine ⟨⟨e.symm ⟨g * (b ^ i)⁻¹, hmem⟩, y⟩, ?_⟩
    show ((e (e.symm ⟨g * (b ^ i)⁻¹, hmem⟩) : ↥N) : G) *
      Semiabelian.zmodHomOfPowEqOne j b hb y = g
    rw [MulEquiv.apply_symm_apply, hy]
    show g * (b ^ i)⁻¹ * b ^ i = g
    rw [inv_mul_cancel_right]

/-- **A finite group with a cyclic normal subgroup of prime index is semiabelian**: the quotient
has prime order, hence is cyclic. -/
theorem of_isCyclic_of_prime_index {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    [IsCyclic ↥N] {p : ℕ} [Fact p.Prime] (hp : N.index = p) : IsSemiabelian G := by
  haveI : IsCyclic (G ⧸ N) := isCyclic_of_prime_card (p := p) hp
  exact of_isCyclic_of_isCyclic_quotient N

/-- **A semidirect product of two finite abelian groups is semiabelian**, for an arbitrary
action. -/
theorem semidirect_commGroup {A B : Type} [CommGroup A] [Finite A] [CommGroup B] [Finite B]
    (φ : B →* MulAut A) : IsSemiabelian (A ⋊[φ] B) :=
  IsSemiabelian.semidirect φ (of_commGroup B)

/-- **Every generalized quaternion group is semiabelian.**  The powers of `QuaternionGroup.a 1`
form a cyclic subgroup of order `2 * n`, hence of index two in the group of order `4 * n`; index
two forces normality, and the quotient has prime order two.  For `n = 2` this is the quaternion
group of order eight, which is not a semidirect product: it is reached through the passage to
homomorphic images built into the class of semiabelian groups. -/
theorem quaternion (n : ℕ) [NeZero n] : IsSemiabelian (QuaternionGroup n) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hinj := Semiabelian.quaternionAHom_injective n
  set N : Subgroup (QuaternionGroup n) := (Semiabelian.quaternionAHom n).range with hN
  haveI : IsCyclic ↥N := isCyclic_of_surjective
    (MonoidHom.ofInjective hinj).toMonoidHom (MonoidHom.ofInjective hinj).surjective
  have hcardN : Nat.card ↥N = 2 * n := by
    rw [hN, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hcardG : Nat.card (QuaternionGroup n) = 4 * n := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hindex : N.index = 2 := by
    have h := N.card_mul_index
    rw [hcardN, hcardG] at h
    refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 * n by omega) ?_
    rw [h]
    ring
  haveI : N.Normal := Subgroup.normal_of_index_eq_two hindex
  haveI : IsCyclic (QuaternionGroup n ⧸ N) := isCyclic_of_prime_card (p := 2) hindex
  exact of_isCyclic_of_isCyclic_quotient N

end IsSemiabelian

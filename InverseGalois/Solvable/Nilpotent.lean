/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.Product
import InverseGalois.Rigidity.RET.RegularCriterion
import InverseGalois.Rigidity.RET.RegularProduct

/-!
# Nilpotent groups are assembled from their Sylow subgroups

A finite nilpotent group is the direct product of its Sylow subgroups, and the orders of those
Sylow subgroups are powers of distinct primes, hence pairwise coprime.  Both realization
predicates of this development — `IsInverseGalois` over `ℚ` and `IsRegularInverseGalois` over
`ℚ(T)` — are closed under products of groups of coprime order, so the whole nilpotent group is
realized as soon as each of its Sylow subgroups is.

The two ingredients are packaged separately.  First, the binary coprime-product theorems are
promoted to an arbitrary finite family: transporting the index type to `Fin n` and peeling off one
factor at a time turns `∏ᵢ Gᵢ` into iterated binary products, and the order of the remaining
product is the product of the remaining orders, still coprime to the order of the factor that was
peeled off.  Second, `Sylow.directProductOfNormal` presents a finite nilpotent group as the
product, over the primes dividing its order, of the (unique, since normal) Sylow subgroup for that
prime; the order of the Sylow `p`-subgroup is `p ^ (Nat.card G).factorization p`, so distinct
primes give coprime orders.

## Main results

* `IsInverseGalois.pi_of_pairwise_coprime` — a finite product of inverse Galois groups of pairwise
  coprime orders is an inverse Galois group.
* `IsRegularInverseGalois.pi_of_pairwise_coprime` — the same statement over `ℚ(T)`.
* `isInverseGalois_of_isNilpotent` — a finite nilpotent group all of whose Sylow subgroups are
  inverse Galois groups is an inverse Galois group, and `isInverseGalois_of_isNilpotent'` phrases
  the hypothesis in terms of `IsPGroup` subgroups.
* `isRegularInverseGalois_of_isNilpotent` and `isRegularInverseGalois_of_isNilpotent'` — the
  regular counterparts over `ℚ(T)`.
-/

universe u

namespace SylowReduction

/-! ## Two multiplicative reindexing equivalences -/

/-- **Peeling the first factor off a product indexed by `Fin (n + 1)`.**  Evaluation at `0` and
restriction to the successors are both multiplicative. -/
def mulEquivPiFinSucc {n : ℕ} (M : Fin (n + 1) → Type u) [∀ i, Mul (M i)] :
    (∀ i, M i) ≃* M 0 × ∀ i : Fin n, M i.succ :=
  { (Fin.consEquiv M).symm with map_mul' := fun _ _ => rfl }

/-- **Reindexing a product along an equivalence of index types.**  The multiplicative version of
`Equiv.piCongrLeft'`. -/
def mulEquivPiCongrLeft' {ι ι' : Type*} (M : ι → Type u) [∀ i, Mul (M i)] (e : ι ≃ ι') :
    (∀ i, M i) ≃* ∀ i' : ι', M (e.symm i') :=
  { Equiv.piCongrLeft' M e with map_mul' := fun _ _ => rfl }

/-! ## An abstract coprime-product induction

Both realization predicates are transported along isomorphisms, hold for the trivial group and are
closed under coprime binary products.  That is all the induction below uses, so it is carried out
once for an abstract predicate `IG` and instantiated twice. -/

variable {IG : ∀ (G : Type u) [Group G], Prop}

/-- The `Fin n` case of `pi_of_pairwise_coprime`, proved by peeling off one factor at a time. -/
theorem pi_fin (htriv : ∀ (G : Type u) [Group G] [Subsingleton G], IG G)
    (hequiv : ∀ {G H : Type u} [Group G] [Group H], IG G → (G ≃* H) → IG H)
    (hprod : ∀ {G H : Type u} [Group G] [Group H] [Finite G] [Finite H],
      IG G → IG H → (Nat.card G).Coprime (Nat.card H) → IG (G × H)) (n : ℕ) :
    ∀ (M : Fin n → Type u) [∀ i, Group (M i)] [∀ i, Finite (M i)],
      Pairwise (fun i j => (Nat.card (M i)).Coprime (Nat.card (M j))) → (∀ i, IG (M i)) →
      IG (∀ i, M i) := by
  induction n with
  | zero => intro M _ _ _ _; exact htriv _
  | succ n ih =>
    intro M _ _ hcop hIG
    have hrest : IG (∀ i : Fin n, M i.succ) :=
      ih (fun i => M i.succ) (fun i j hij => hcop fun h => hij (Fin.succ_injective n h))
        fun i => hIG i.succ
    have hc : (Nat.card (M 0)).Coprime (Nat.card (∀ i : Fin n, M i.succ)) := by
      rw [Nat.card_pi]
      exact Nat.Coprime.prod_right fun i _ => hcop (Fin.succ_ne_zero i).symm
    exact hequiv (hprod (hIG 0) hrest hc) (mulEquivPiFinSucc M).symm

/-- **An abstract finite product of pairwise coprime factors.**  A predicate on finite groups that
holds for the trivial group, is invariant under isomorphism and is closed under products of coprime
order is closed under arbitrary finite products of pairwise coprime order. -/
theorem pi_of_pairwise_coprime (htriv : ∀ (G : Type u) [Group G] [Subsingleton G], IG G)
    (hequiv : ∀ {G H : Type u} [Group G] [Group H], IG G → (G ≃* H) → IG H)
    (hprod : ∀ {G H : Type u} [Group G] [Group H] [Finite G] [Finite H],
      IG G → IG H → (Nat.card G).Coprime (Nat.card H) → IG (G × H))
    {ι : Type} [Fintype ι] (M : ι → Type u) [∀ i, Group (M i)] [∀ i, Finite (M i)]
    (hcop : Pairwise fun i j => (Nat.card (M i)).Coprime (Nat.card (M j)))
    (hIG : ∀ i, IG (M i)) : IG (∀ i, M i) := by
  set e := Fintype.equivFin ι with he
  have key : IG (∀ j : Fin (Fintype.card ι), M (e.symm j)) :=
    pi_fin htriv hequiv hprod (Fintype.card ι) (fun j => M (e.symm j))
      (fun i j hij => hcop fun h => hij (e.symm.injective h)) fun j => hIG _
  exact hequiv key (mulEquivPiCongrLeft' M e).symm

/-! ## The Sylow decomposition of a finite nilpotent group -/

/-- **An abstract Sylow assembly for finite nilpotent groups.**  In a finite nilpotent group every
Sylow subgroup is normal, hence unique for its prime, and the group is the product of them over the
primes dividing its order; the orders of the factors are powers of distinct primes. -/
theorem of_isNilpotent (htriv : ∀ (G : Type u) [Group G] [Subsingleton G], IG G)
    (hequiv : ∀ {G H : Type u} [Group G] [Group H], IG G → (G ≃* H) → IG H)
    (hprod : ∀ {G H : Type u} [Group G] [Group H] [Finite G] [Finite H],
      IG G → IG H → (Nat.card G).Coprime (Nat.card H) → IG (G × H))
    {G : Type u} [Group G] [Finite G] [Group.IsNilpotent G]
    (h : ∀ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p G), IG ↥(P : Subgroup G)) : IG G := by
  classical
  -- Every Sylow subgroup of a finite nilpotent group is normal.
  have hnormal : ∀ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p G), (↑P : Subgroup G).Normal :=
    (isNilpotent_of_finite_tfae.out 0 3 rfl rfl).mp ‹Group.IsNilpotent G›
  -- Hence the group is the product of the Sylow subgroups, one for each prime factor of its order.
  let e : (∀ q : (Nat.card G).primeFactors, ∀ P : Sylow (q : ℕ) G, ↥(P : Subgroup G)) ≃* G :=
    Sylow.directProductOfNormal fun P => hnormal _ ‹_› P
  -- The `q`-th factor has order `q ^ (multiplicity of q in the order of G)`.
  have hcard : ∀ q : (Nat.card G).primeFactors,
      Nat.card (∀ P : Sylow (q : ℕ) G, ↥(P : Subgroup G))
        = (q : ℕ) ^ (Nat.card G).factorization (q : ℕ) := by
    intro q
    haveI : Fact (q : ℕ).Prime := Fact.mk (Nat.prime_of_mem_primeFactors q.2)
    letI := Sylow.unique_of_normal (default : Sylow (q : ℕ) G) (hnormal _ ‹_› _)
    rw [Nat.card_congr (Equiv.piUnique _)]
    exact Sylow.card_eq_multiplicity _
  -- Distinct primes give coprime orders.
  have hcop : Pairwise fun q r : (Nat.card G).primeFactors =>
      (Nat.card (∀ P : Sylow (q : ℕ) G, ↥(P : Subgroup G))).Coprime
        (Nat.card (∀ P : Sylow (r : ℕ) G, ↥(P : Subgroup G))) := by
    intro q r hqr
    rw [hcard q, hcard r]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors q.2)
      (Nat.prime_of_mem_primeFactors r.2)).mpr fun hh => hqr (Subtype.ext hh))
  -- Each factor is a single Sylow subgroup, since the Sylow subgroup for a prime is unique.
  have hfac : ∀ q : (Nat.card G).primeFactors,
      IG (∀ P : Sylow (q : ℕ) G, ↥(P : Subgroup G)) := by
    intro q
    haveI : Fact (q : ℕ).Prime := Fact.mk (Nat.prime_of_mem_primeFactors q.2)
    letI := Sylow.unique_of_normal (default : Sylow (q : ℕ) G) (hnormal _ ‹_› _)
    exact hequiv (h _ ‹_› default)
      (MulEquiv.piUnique fun P : Sylow (q : ℕ) G => ↥(P : Subgroup G)).symm
  exact hequiv (pi_of_pairwise_coprime htriv hequiv hprod
    (fun q : (Nat.card G).primeFactors => ∀ P : Sylow (q : ℕ) G, ↥(P : Subgroup G)) hcop hfac) e

/-- The trivial group is an inverse Galois group. -/
private theorem isInverseGalois_of_subsingleton (G : Type u) [Group G] [Subsingleton G] :
    IsInverseGalois G :=
  have : Unique G := uniqueOfSubsingleton 1
  IsInverseGalois.unit.of_mulEquiv (MulEquiv.ofUnique (M := Unit))

end SylowReduction

/-! ## Finite families of coprime order -/

/-- **A finite product of inverse Galois groups of pairwise coprime orders is an inverse Galois
group.**  The binary theorem `IsInverseGalois.prod_of_coprime` is applied one factor at a time; the
order of the remaining product is the product of the remaining orders, still coprime to the order
of the factor split off. -/
theorem IsInverseGalois.pi_of_pairwise_coprime {ι : Type} [Fintype ι] (G : ι → Type u)
    [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (hcop : Pairwise fun i j => (Nat.card (G i)).Coprime (Nat.card (G j)))
    (h : ∀ i, IsInverseGalois (G i)) : IsInverseGalois (∀ i, G i) :=
  SylowReduction.pi_of_pairwise_coprime (IG := fun G _ => IsInverseGalois G)
    SylowReduction.isInverseGalois_of_subsingleton (fun hG e => hG.of_mulEquiv e)
    (fun h₁ h₂ hc => h₁.prod_of_coprime h₂ hc) G hcop h

/-- **A finite product of regular inverse Galois groups of pairwise coprime orders is a regular
inverse Galois group.**  Same induction as over `ℚ`, on top of the coprime compositum theorem
`IsRegularInverseGalois.prod_of_coprime` over `ℚ(T)`. -/
theorem IsRegularInverseGalois.pi_of_pairwise_coprime {ι : Type} [Fintype ι] (G : ι → Type u)
    [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (hcop : Pairwise fun i j => (Nat.card (G i)).Coprime (Nat.card (G j)))
    (h : ∀ i, IsRegularInverseGalois (G i)) : IsRegularInverseGalois (∀ i, G i) :=
  SylowReduction.pi_of_pairwise_coprime (IG := fun G _ => IsRegularInverseGalois G)
    (fun _ => IsRegularInverseGalois.of_subsingleton) (fun hG e => hG.of_mulEquiv e)
    (fun h₁ h₂ hc => h₁.prod_of_coprime h₂ hc) G hcop h

/-! ## Nilpotent groups -/

/-- **A finite nilpotent group all of whose Sylow subgroups are inverse Galois groups is an inverse
Galois group.**  A finite nilpotent group is the direct product of its Sylow subgroups, whose
orders are powers of distinct primes. -/
theorem isInverseGalois_of_isNilpotent {G : Type u} [Group G] [Finite G] [Group.IsNilpotent G]
    (h : ∀ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p G), IsInverseGalois ↥(P : Subgroup G)) :
    IsInverseGalois G :=
  SylowReduction.of_isNilpotent (IG := fun G _ => IsInverseGalois G)
    SylowReduction.isInverseGalois_of_subsingleton (fun hG e => hG.of_mulEquiv e)
    (fun h₁ h₂ hc => h₁.prod_of_coprime h₂ hc) h

/-- **A finite nilpotent group all of whose Sylow subgroups are regular inverse Galois groups is a
regular inverse Galois group.** -/
theorem isRegularInverseGalois_of_isNilpotent {G : Type u} [Group G] [Finite G]
    [Group.IsNilpotent G]
    (h : ∀ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p G), IsRegularInverseGalois ↥(P : Subgroup G)) :
    IsRegularInverseGalois G :=
  SylowReduction.of_isNilpotent (IG := fun G _ => IsRegularInverseGalois G)
    (fun _ => IsRegularInverseGalois.of_subsingleton) (fun hG e => hG.of_mulEquiv e)
    (fun h₁ h₂ hc => h₁.prod_of_coprime h₂ hc) h

/-- **Every finite nilpotent group is an inverse Galois group as soon as every finite `p`-group
is.**  The hypothesis is phrased for all `p`-subgroups, which is what a general theorem about
`p`-groups provides. -/
theorem isInverseGalois_of_isNilpotent' {G : Type u} [Group G] [Finite G] [Group.IsNilpotent G]
    (h : ∀ (H : Subgroup G) (p : ℕ), p.Prime → IsPGroup p H → IsInverseGalois ↥H) :
    IsInverseGalois G :=
  isInverseGalois_of_isNilpotent fun p hp P => h _ p hp.out P.isPGroup'

/-- **Every finite nilpotent group is a regular inverse Galois group as soon as every finite
`p`-group is.** -/
theorem isRegularInverseGalois_of_isNilpotent' {G : Type u} [Group G] [Finite G]
    [Group.IsNilpotent G]
    (h : ∀ (H : Subgroup G) (p : ℕ), p.Prime → IsPGroup p H → IsRegularInverseGalois ↥H) :
    IsRegularInverseGalois G :=
  isRegularInverseGalois_of_isNilpotent fun p hp P => h _ p hp.out P.isPGroup'

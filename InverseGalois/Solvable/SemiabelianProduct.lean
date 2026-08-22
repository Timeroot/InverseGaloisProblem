/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.PiMulEquiv
import InverseGalois.Solvable.Semiabelian

/-!
# Direct products of semiabelian groups

Dentzer's class of semiabelian groups is closed under finite direct products.  Only the special
case of a product with a finite abelian group is immediate from the definition; the general case
needs an induction over the derivation of the first factor, whose one interesting step is the
observation that a direct factor may be absorbed into the acting group of a semidirect product:

`(A ⋊[φ] K) × H ≃ A ⋊[φ ∘ pr₁] (K × H)`.

The action on the right ignores the new factor, so the left-hand group is again a semidirect
product by a finite abelian group, this time over `K × H`, which is semiabelian by the inductive
hypothesis.

The consequence for the inverse Galois problem is that a finite nilpotent group is semiabelian as
soon as each of its Sylow subgroups is, since a finite nilpotent group is the direct product of its
Sylow subgroups.

## Main results

* `SemidirectProduct.prodRightMulEquiv`: a direct factor of a semidirect product may be absorbed
  into the acting group.
* `IsSemiabelian.prod'`: **the class of semiabelian groups is closed under direct products.**
* `IsSemiabelian.pi`: the same for a product indexed by a finite type.
* `IsSemiabelian.of_isNilpotent`: **a finite nilpotent group whose Sylow subgroups are all
  semiabelian is semiabelian.**
-/

open InverseGalois

/-- **A direct factor of a semidirect product may be absorbed into the acting group.**  The
product `(A ⋊[φ] K) × H` is the semidirect product of `A` by `K × H` for the action that ignores
the second coordinate; both sides are the set `A × K × H`, and the two multiplications agree
because the action does not see `H`. -/
def SemidirectProduct.prodRightMulEquiv {A K H : Type*} [Group A] [Group K] [Group H]
    (φ : K →* MulAut A) :
    (A ⋊[φ] K) × H ≃* A ⋊[φ.comp (MonoidHom.fst K H)] (K × H) where
  toFun p := ⟨p.1.left, (p.1.right, p.2)⟩
  invFun q := (⟨q.left, q.right.1⟩, q.right.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

namespace IsSemiabelian

/-- **The class of semiabelian groups is closed under direct products.**  The induction is over the
derivation of the first factor: the trivial group contributes nothing, a semidirect product absorbs
the second factor into its acting group, and a surjection may be multiplied by the identity. -/
theorem prod' {G H : Type} [Group G] [Finite G] [Group H] [Finite H] (hG : IsSemiabelian G)
    (hH : IsSemiabelian H) : IsSemiabelian (G × H) := by
  induction hG with
  | of_subsingleton G =>
    haveI : Unique G := uniqueOfSubsingleton 1
    exact hH.of_mulEquiv (MulEquiv.uniqueProd (N := G) (M := H)).symm
  | @semidirect A K _ _ _ _ φ _ ih =>
    exact (IsSemiabelian.semidirect (φ.comp (MonoidHom.fst K H)) ih).of_mulEquiv
      (SemidirectProduct.prodRightMulEquiv φ).symm
  | of_surjective f hf _ ih =>
    exact ih.of_surjective (f.prodMap (MonoidHom.id H)) (hf.prodMap Function.surjective_id)

/-- **A product of semiabelian groups indexed by `Fin n` is semiabelian.**  The first coordinate is
peeled off and the remaining ones are handled by the inductive hypothesis. -/
theorem piFin : ∀ (n : ℕ) (A : Fin n → Type) [∀ i, Group (A i)] [∀ i, Finite (A i)],
    (∀ i, IsSemiabelian (A i)) → IsSemiabelian (∀ i, A i) := by
  intro n
  induction n with
  | zero =>
    intro A _ _ _
    haveI : Subsingleton (∀ i : Fin 0, A i) := ⟨fun _ _ => funext fun i => i.elim0⟩
    exact .of_subsingleton _
  | succ n ih =>
    intro A _ _ h
    exact ((h 0).prod' (ih (fun i => A i.succ) fun i => h i.succ)).of_mulEquiv
      (piFinSuccMulEquiv A).symm

/-- **A product of semiabelian groups indexed by any finite type is semiabelian.** -/
theorem pi {ι : Type} [Finite ι] (A : ι → Type) [∀ i, Group (A i)] [∀ i, Finite (A i)]
    (h : ∀ i, IsSemiabelian (A i)) : IsSemiabelian (∀ i, A i) := by
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin ι
  exact (piFin n (fun j => A (φ.symm j)) fun j => h _).of_mulEquiv
    (piCongrLeftMulEquiv A φ).symm

/-- **A finite nilpotent group whose Sylow subgroups are all semiabelian is semiabelian.**  A
finite nilpotent group has all its Sylow subgroups normal, and is therefore their direct
product. -/
theorem of_isNilpotent {G : Type} [Group G] [Finite G] [Group.IsNilpotent G]
    (h : ∀ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G), IsSemiabelian ↥(P : Subgroup G)) :
    IsSemiabelian G := by
  obtain ⟨e⟩ : Nonempty ((∀ p : (Nat.card G).primeFactors, ∀ P : Sylow p G,
      (↑P : Subgroup G)) ≃* G) :=
    ((isNilpotent_of_finite_tfae (G := G)).out 0 4).mp ‹Group.IsNilpotent G›
  refine IsSemiabelian.of_mulEquiv ?_ e
  refine pi _ fun p => ?_
  haveI : Fact (Nat.Prime (p : ℕ)) := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  exact pi _ fun P => h p inferInstance P

end IsSemiabelian

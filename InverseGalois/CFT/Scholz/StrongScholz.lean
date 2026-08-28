/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.MultiquadraticBase

/-!
# Strong Scholz realizations of the free objects

At the prime two the residue correction of a central step is available only for the Frobenius
defects orthogonal to the square classes of the field being corrected, so the induction cannot
carry a bare Scholz field: it has to carry a Scholz field together with a family of blocks of
primes accounting for those square classes.  A field of that kind, realising the free object of a
given rank and `2`-class, is a *strong* Scholz realization.

The blocks are pairwise disjoint and their indicator vectors span the exponent vectors whose
radicand is already a square in the field, which is exactly the orthogonality condition the
correction needs, one bit per block rather than one bit per ramified prime.  Because a step of the
climb is a Frattini extension, no new square root of a rational number appears, so the same family
of blocks accounts for the enlarged field: the invariant is stable.

The free objects are universal for rank and `2`-class, so a strong Scholz realization of all of
them realises every finite `2`-group.

## Main definitions

* `InverseGalois.CFT.StrongScholzRealization`: a Scholz field realising the free object of rank `d`
  and `2`-class `c`, together with a family of blocks accounting for its square roots.
* `InverseGalois.CFT.IsStrongScholzRealizable`: the existence of such a field.

## Main results

* `InverseGalois.CFT.isStrongScholzRealizable_one`: **the multiquadratic base is a strong Scholz
  realization of `2`-class one**, at every rank and every level.
* `InverseGalois.CFT.isScholzRealizable_of_isStrongScholzRealizable`: a strong Scholz realization
  of the free object realises every group of that rank and `2`-class.
* `InverseGalois.CFT.isScholzRealizable_of_forall_isStrongScholzRealizable`: **granted a strong
  Scholz realization of every free object, every finite `2`-group is realised.**

## Tags

Scholz–Reichardt, strong Scholz field, block, free object, `2`-group
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Strong Scholz realizations -/

/-- **A strong Scholz realization of the free object of rank `d` and `2`-class `c` at level `N`**:
a subfield of the algebraic closure of `ℚ`, Galois over `ℚ` with that group and satisfying Serre's
condition, together with a pairwise disjoint family of `d` blocks of primes whose indicator vectors
account for every square root of a squarefree product of primes lying in the field. -/
structure StrongScholzRealization (d c N : ℕ) where
  /-- The subfield of `AlgebraicClosure ℚ` that realises the free object. -/
  carrier : IntermediateField ℚ (AlgebraicClosure ℚ)
  [numberField : NumberField ↥carrier]
  [isGalois : IsGalois ℚ ↥carrier]
  /-- The field satisfies Serre's condition at the prime two. -/
  isScholz : IsScholz 2 N ↥carrier
  /-- The blocks of primes accounting for the square roots of the field. -/
  block : Fin d → Finset ℕ
  /-- The blocks consist of primes. -/
  blockPrime : ∀ i, ∀ p ∈ block i, p.Prime
  /-- The blocks are pairwise disjoint. -/
  blockDisjoint : ∀ i j, i ≠ j → Disjoint (block i) (block j)
  /-- The blocks account for the square roots of the field. -/
  isBlockSpanned : IsBlockSpanned carrier block
  /-- The Galois group of the field is the free object of rank `d` and `2`-class `c`. -/
  galEquiv : Gal(↥carrier/ℚ) ≃* FreePClass 2 d c

attribute [instance] StrongScholzRealization.numberField StrongScholzRealization.isGalois

/-- The free object of rank `d` and `2`-class `c` is **strongly Scholz realizable** at level `N`
when it admits a strong Scholz realization. -/
def IsStrongScholzRealizable (d c N : ℕ) : Prop :=
  Nonempty (StrongScholzRealization d c N)

variable {d c N : ℕ}

/-- Forgetting the blocks turns a strong Scholz realization into an ordinary one. -/
def StrongScholzRealization.toScholzRealization (R : StrongScholzRealization d c N) :
    ScholzRealization (FreePClass 2 d c) 2 N where
  carrier := R.carrier
  isScholz := R.isScholz
  galEquiv := R.galEquiv

/-- **A strong Scholz realization at one level is one at every smaller level.** -/
theorem IsStrongScholzRealizable.mono {M : ℕ} (h : IsStrongScholzRealizable d c N) (hMN : M ≤ N) :
    IsStrongScholzRealizable d c M :=
  h.elim fun R => ⟨{ R with isScholz := R.isScholz.mono hMN }⟩

/-! ### The base of the induction on the `2`-class -/

/-- **The multiquadratic base is a strong Scholz realization of `2`-class one.**  Iterating the
split step at the prime two produces a field satisfying Serre's condition whose ramified primes are
exactly `d` distinct primes and whose Galois group is elementary abelian of rank `d`; the singletons
of those primes are pairwise disjoint blocks, and they account for the square roots of the field
because every prime involved in such a square root ramifies in it. -/
theorem isStrongScholzRealizable_one (d N : ℕ) : IsStrongScholzRealizable d 1 N := by
  obtain ⟨K, hNF, hGal, q, hqinj, hqp, hsch, -, hspan, ⟨e⟩⟩ := exists_scholz_freePClass_one N d
  haveI := hNF
  haveI := hGal
  exact ⟨{ carrier := K
           isScholz := hsch
           block := fun i => {q i}
           blockPrime := fun i p hp => Finset.mem_singleton.mp hp ▸ hqp i
           blockDisjoint := fun i j hij => Finset.disjoint_singleton.mpr fun h => hij (hqinj h)
           isBlockSpanned := hspan
           galEquiv := e }⟩

/-! ### From the free objects to every finite `2`-group -/

/-- **A strong Scholz realization of the free object realises every group of that rank and
`2`-class.**  Such a group is a quotient of the free object, and the fixed field of the kernel is a
Scholz field with that quotient as its Galois group. -/
theorem isScholzRealizable_of_isStrongScholzRealizable {G : Type} [Group G]
    (hc : lowerPCentralSeries 2 G c = ⊥) {f : Fin d → G}
    (hf : Subgroup.closure (Set.range f) = ⊤) (h : IsStrongScholzRealizable d c N) :
    IsScholzRealizable G 2 N := by
  obtain ⟨R⟩ := h
  obtain ⟨φ, hφ⟩ := FreePClass.exists_surjective hc hf
  exact isScholzRealizable_of_surjective ↥R.carrier R.isScholz (φ.comp R.galEquiv.toMonoidHom)
    (hφ.comp R.galEquiv.surjective)

/-- **Granted a strong Scholz realization of every free object, every finite `2`-group is
realised.**  A finite `2`-group is generated by its own elements and its lower `2`-central series
reaches the trivial subgroup, so it is a quotient of a free object of some rank and `2`-class. -/
theorem isScholzRealizable_of_forall_isStrongScholzRealizable (N : ℕ)
    (h : ∀ d c, IsStrongScholzRealizable d c N) (G : Type) [Group G] [Finite G]
    (hG : IsPGroup 2 G) : IsScholzRealizable G 2 N := by
  obtain ⟨c, hc⟩ := exists_lowerPCentralSeries_eq_bot Nat.prime_two G hG
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin G
  have hf : Subgroup.closure (Set.range φ.symm) = ⊤ := by
    rw [φ.symm.surjective.range_eq, Subgroup.closure_univ]
  exact isScholzRealizable_of_isStrongScholzRealizable hc hf (h n c)

end InverseGalois.CFT

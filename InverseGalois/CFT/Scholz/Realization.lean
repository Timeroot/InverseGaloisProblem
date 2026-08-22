import Mathlib
import InverseGalois.CFT.Scholz.SplitStep
import InverseGalois.Core.PiMulEquiv

/-!
# Realizations normalised by Serre's condition

A group is realised in the Scholz–Reichardt sense when it is the Galois group of a subfield of
`AlgebraicClosure ℚ` satisfying Serre's condition `(S_N)`.  Bundling the field, its Galois
property and the isomorphism into a single structure makes the induction of the Scholz–Reichardt
construction expressible: each step consumes a realization and returns another one.

This file records the steps that the split case supplies.  The trivial group is realised by `ℚ`
itself, which is unramified everywhere; and a realised group may be multiplied by a cyclic group
of order `ℓ ^ e`, by the compositum construction of `InverseGalois.CFT.Scholz.SplitStep`.
Iterating the second step from the first realises every finite product of cyclic `ℓ`-groups, and
the structure theorem for finite abelian groups then covers every finite abelian `ℓ`-group.

## Main definitions

* `InverseGalois.CFT.ScholzRealization`: a Galois subfield of `AlgebraicClosure ℚ` with group `G`
  satisfying `(S_N)`.
* `InverseGalois.CFT.IsScholzRealizable`: the existence of such a field.

## Main results

* `InverseGalois.CFT.isScholzRealizable_of_subsingleton`: the trivial group is realised by `ℚ`.
* `InverseGalois.CFT.IsScholzRealizable.prod_cyclic_pow`: **a realised group stays realised after
  multiplication by a cyclic group of order `ℓ ^ e`.**
* `InverseGalois.CFT.isScholzRealizable_pi`: a finite product of cyclic `ℓ`-groups is realised.
* `InverseGalois.CFT.isScholzRealizable_of_isPGroup_of_commGroup`: **every finite abelian
  `ℓ`-group is realised**, for every level `N`.
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### Fields of degree one -/

/-- **A number field of degree one is unramified everywhere.**  The decomposition group at a prime
above `p` is a subgroup of the trivial Galois group, and its order is the product of the
ramification index with the residue degree. -/
theorem ramifiedSet_eq_empty_of_finrank_eq_one (E : Type*) [Field E] [NumberField E]
    [IsGalois ℚ E] (h : finrank ℚ E = 1) : ramifiedSet E = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro p ⟨hp, P, ⟨hPprime, hPover⟩, hPe⟩
  haveI := hPprime
  haveI := hPover
  have hdvd : Ideal.ramificationIdx (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) P *
      (Ideal.span {(p : ℤ)}).inertiaDeg P ∣ 1 := by
    rw [← card_stabilizer_eq_mul E hp P, ← h, ← IsGalois.card_aut_eq_finrank ℚ E]
    exact Subgroup.card_subgroup_dvd_card _
  exact hPe (Nat.eq_one_of_mul_eq_one_right (Nat.dvd_one.mp hdvd))

/-- **A number field of degree one satisfies Serre's condition.**  It is unramified everywhere, so
both halves of the condition are vacuous. -/
theorem isScholz_of_finrank_eq_one (E : Type*) [Field E] [NumberField E] [IsGalois ℚ E]
    (h : finrank ℚ E = 1) (ℓ N : ℕ) : IsScholz ℓ N E := by
  have hempty := ramifiedSet_eq_empty_of_finrank_eq_one E h
  exact ⟨fun p hp => absurd hp (by rw [hempty]; exact Set.notMem_empty p),
    fun p hp => absurd hp (by rw [hempty]; exact Set.notMem_empty p)⟩

/-! ### Realizations -/

/-- **A realization of `G` normalised by Serre's condition `(S_N)`**: a subfield of the algebraic
closure of `ℚ`, Galois over `ℚ` with group `G`, whose ramified primes are all congruent to one
modulo `ℓ ^ N` and have residue degree one. -/
structure ScholzRealization (G : Type*) [Group G] (ℓ N : ℕ) where
  /-- The subfield of `AlgebraicClosure ℚ` that realises `G`. -/
  carrier : IntermediateField ℚ (AlgebraicClosure ℚ)
  [numberField : NumberField ↥carrier]
  [isGalois : IsGalois ℚ ↥carrier]
  /-- The field satisfies Serre's condition. -/
  isScholz : IsScholz ℓ N ↥carrier
  /-- The Galois group of the field is `G`. -/
  galEquiv : Gal(↥carrier/ℚ) ≃* G

attribute [instance] ScholzRealization.numberField ScholzRealization.isGalois

/-- A group is **Scholz realizable** at `ℓ` and level `N` when it admits a realization. -/
def IsScholzRealizable (G : Type*) [Group G] (ℓ N : ℕ) : Prop :=
  Nonempty (ScholzRealization G ℓ N)

variable {G H : Type*} [Group G] [Group H] {ℓ N : ℕ}

/-- A realization transports along an isomorphism of groups. -/
def ScholzRealization.congr (e : G ≃* H) (R : ScholzRealization G ℓ N) :
    ScholzRealization H ℓ N where
  carrier := R.carrier
  isScholz := R.isScholz
  galEquiv := R.galEquiv.trans e

/-- Realizability transports along an isomorphism of groups. -/
theorem IsScholzRealizable.of_mulEquiv (e : G ≃* H) (h : IsScholzRealizable G ℓ N) :
    IsScholzRealizable H ℓ N :=
  h.elim fun R => ⟨R.congr e⟩

/-- **The trivial group is realised by `ℚ` itself.** -/
theorem isScholzRealizable_of_subsingleton [Subsingleton G] : IsScholzRealizable G ℓ N := by
  set E : IntermediateField ℚ (AlgebraicClosure ℚ) := ⊥ with hE
  haveI : FiniteDimensional ℚ ↥E :=
    FiniteDimensional.of_finrank_eq_succ (n := 0) IntermediateField.finrank_bot
  haveI : NumberField ↥E := ⟨⟩
  haveI : IsGalois ℚ ↥E :=
    IsGalois.of_algEquiv (IntermediateField.botEquiv ℚ (AlgebraicClosure ℚ)).symm
  have hrank : finrank ℚ ↥E = 1 := IntermediateField.finrank_bot
  have hcard : Nat.card Gal(↥E/ℚ) = 1 := by
    rw [IsGalois.card_aut_eq_finrank ℚ ↥E]
    exact hrank
  haveI : Subsingleton Gal(↥E/ℚ) := (Nat.card_eq_one_iff_unique.mp hcard).1
  haveI : Unique Gal(↥E/ℚ) := uniqueOfSubsingleton 1
  haveI : Unique G := uniqueOfSubsingleton 1
  exact ⟨⟨E, isScholz_of_finrank_eq_one ↥E hrank ℓ N, MulEquiv.ofUnique⟩⟩

/-- **A realised group stays realised after multiplication by a cyclic group of order `ℓ ^ e`.**
The compositum of the realising field with the degree-`ℓ ^ e` subfield of the cyclotomic field of
a well-chosen prime realises the product, and again satisfies Serre's condition. -/
theorem IsScholzRealizable.prod_cyclic_pow (hℓ : ℓ.Prime) (e : ℕ) (h : IsScholzRealizable G ℓ N) :
    IsScholzRealizable (G × Multiplicative (ZMod (ℓ ^ e))) ℓ N := by
  haveI : NeZero (ℓ ^ e) := ⟨pow_ne_zero e hℓ.ne_zero⟩
  obtain ⟨R⟩ := h
  have hcard : Nat.card (Multiplicative (ZMod (ℓ ^ e))) = ℓ ^ e := by simp
  refine ⟨⟨stepField ↥R.carrier hℓ N e, isScholz_stepField ↥R.carrier hℓ N e R.isScholz,
    (galEquivStepField ↥R.carrier hℓ N e).trans (MulEquiv.prodCongr R.galEquiv ?_)⟩⟩
  exact mulEquivOfCyclicCardEq ((card_gal_stepAux ↥R.carrier hℓ N e).trans hcard.symm)

/-- **A realised group stays realised after multiplication by a cyclic group of order `ℓ`.** -/
theorem IsScholzRealizable.prod_cyclic (hℓ : ℓ.Prime) (h : IsScholzRealizable G ℓ N) :
    IsScholzRealizable (G × Multiplicative (ZMod ℓ)) ℓ N := by
  have h1 := h.prod_cyclic_pow hℓ 1
  rwa [pow_one] at h1

/-- **A product of cyclic `ℓ`-groups indexed by `Fin n` is realised**, at every level `N`: start
from `ℚ` and adjoin one cyclic factor at a time. -/
theorem isScholzRealizable_piFin (hℓ : ℓ.Prime) (N : ℕ) :
    ∀ (n : ℕ) (d : Fin n → ℕ),
      IsScholzRealizable (∀ i, Multiplicative (ZMod (ℓ ^ d i))) ℓ N := by
  intro n
  induction n with
  | zero => exact fun _ => isScholzRealizable_of_subsingleton
  | succ n ih =>
    intro d
    refine IsScholzRealizable.of_mulEquiv ?_
      ((ih fun i => d i.succ).prod_cyclic_pow hℓ (d 0))
    exact ((piFinSuccMulEquiv fun i => Multiplicative (ZMod (ℓ ^ d i))).trans
      MulEquiv.prodComm).symm

/-- **A product of cyclic `ℓ`-groups indexed by any finite type is realised**, at every level. -/
theorem isScholzRealizable_pi (hℓ : ℓ.Prime) (N : ℕ) {ι : Type*} [Finite ι] (d : ι → ℕ) :
    IsScholzRealizable (∀ i, Multiplicative (ZMod (ℓ ^ d i))) ℓ N := by
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin ι
  exact (isScholzRealizable_piFin hℓ N n fun j => d (φ.symm j)).of_mulEquiv
    (piCongrLeftMulEquiv (fun i => Multiplicative (ZMod (ℓ ^ d i))) φ).symm

/-- **Every finite abelian `ℓ`-group is realised**, at every level `N`.  By the structure theorem
it is a product of cyclic groups, each of order dividing the order of the group and hence a power
of `ℓ`, and each such product is realised by iterating the split step. -/
theorem isScholzRealizable_of_isPGroup_of_commGroup (hℓ : ℓ.Prime) (N : ℕ) (G : Type*)
    [CommGroup G] [Finite G] (hG : IsPGroup ℓ G) : IsScholzRealizable G ℓ N := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hG
  obtain ⟨ι, hι, n, hn, ⟨eG⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  -- each cyclic factor has order dividing the order of the group, hence a power of `ℓ`
  have hprod : ∏ i, n i = ℓ ^ k := by
    rw [← hk, Nat.card_congr eG.toEquiv, Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => by
      haveI : NeZero (n i) := ⟨by have := hn i; omega⟩
      simp
  have hdvd : ∀ i, ∃ j, n i = ℓ ^ j := by
    intro i
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ).mp
      (hprod ▸ Finset.dvd_prod_of_mem n (Finset.mem_univ i))
    exact ⟨j, hj⟩
  choose j hj using hdvd
  obtain rfl : n = fun i => ℓ ^ j i := funext hj
  exact (isScholzRealizable_pi hℓ N j).of_mulEquiv eG.symm

end InverseGalois.CFT

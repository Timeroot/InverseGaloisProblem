import Mathlib
import InverseGalois.CFT.Scholz.SplitStep

/-!
# Realizations normalised by Serre's condition

A group is realised in the Scholz–Reichardt sense when it is the Galois group of a subfield of
`AlgebraicClosure ℚ` satisfying Serre's condition `(S_N)`.  Bundling the field, its Galois
property and the isomorphism into a single structure makes the induction of the Scholz–Reichardt
construction expressible: each step consumes a realization and returns another one.

This file records the two steps that the split case supplies.  The trivial group is realised by
`ℚ` itself, which is unramified everywhere; and a realised group may be multiplied by a cyclic
group of order `ℓ`, by the compositum construction of
`InverseGalois.CFT.Scholz.SplitStep`.  Iterating the second step from the first realises every
elementary abelian `ℓ`-group.

## Main definitions

* `InverseGalois.CFT.ScholzRealization`: a Galois subfield of `AlgebraicClosure ℚ` with group `G`
  satisfying `(S_N)`.
* `InverseGalois.CFT.IsScholzRealizable`: the existence of such a field.

## Main results

* `InverseGalois.CFT.isScholzRealizable_of_subsingleton`: the trivial group is realised by `ℚ`.
* `InverseGalois.CFT.IsScholzRealizable.prod_cyclic`: **a realised group stays realised after
  multiplication by a cyclic group of order `ℓ`.**
* `InverseGalois.CFT.isScholzRealizable_pi`: **every elementary abelian `ℓ`-group is realised**,
  for every level `N`.
-/

open Module NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### An auxiliary group isomorphism -/

/-- Splitting off the first coordinate of a finite power of a group. -/
def piFinSuccMulEquiv (A : Type*) [Group A] (n : ℕ) : (Fin (n + 1) → A) ≃* A × (Fin n → A) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv := Fin.cons_self_tail
  right_inv p := Prod.ext (by simp) (by simp)
  map_mul' _ _ := rfl

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

/-- **A realised group stays realised after multiplication by a cyclic group of order `ℓ`.**  The
compositum of the realising field with the degree-`ℓ` subfield of the cyclotomic field of a
well-chosen prime realises the product, and again satisfies Serre's condition. -/
theorem IsScholzRealizable.prod_cyclic (hℓ : ℓ.Prime) (h : IsScholzRealizable G ℓ N) :
    IsScholzRealizable (G × Multiplicative (ZMod ℓ)) ℓ N := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨R⟩ := h
  have hcard : Nat.card (Multiplicative (ZMod ℓ)) = ℓ := by simp
  refine ⟨⟨stepField ↥R.carrier hℓ N, isScholz_stepField ↥R.carrier hℓ N R.isScholz,
    (galEquivStepField ↥R.carrier hℓ N).trans (MulEquiv.prodCongr R.galEquiv ?_)⟩⟩
  exact mulEquivOfPrimeCardEq (card_gal_stepAux ↥R.carrier hℓ N) hcard

/-- **Every elementary abelian `ℓ`-group is realised**, at every level `N`: start from `ℚ` and
adjoin one cyclic factor of order `ℓ` at a time. -/
theorem isScholzRealizable_pi (hℓ : ℓ.Prime) (N n : ℕ) :
    IsScholzRealizable (Fin n → Multiplicative (ZMod ℓ)) ℓ N := by
  induction n with
  | zero => exact isScholzRealizable_of_subsingleton
  | succ n ih =>
    refine IsScholzRealizable.of_mulEquiv ?_ (ih.prod_cyclic hℓ)
    exact ((piFinSuccMulEquiv (Multiplicative (ZMod ℓ)) n).trans MulEquiv.prodComm).symm

end InverseGalois.CFT

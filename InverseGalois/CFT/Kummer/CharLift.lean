/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CharLocalClass
import InverseGalois.CFT.Kummer.CharStabilizer

/-!
# Prescribing a Kummer character on a decomposition subgroup

A decomposition subgroup at a prime of an algebraically closed extension is a closed subgroup of the
Galois group, and Kummer theory there identifies its characters with the classes modulo powers of
the field it fixes; those classes are already the classes of the completion at the place below,
which the base field exhausts.  That is why **every character of a decomposition subgroup is the
Kummer character of a unit of the base field**, with no arithmetic input beyond the finiteness of
the power classes of a completion.

Along the inertia subgroup the same reading is available only away from the exponent.  At a prime
above the exponent the characters of inertia are the classes modulo powers of the maximal unramified
extension, a group the units of the completion do not exhaust, so no unit of the base field can
carry a general character there; away from the exponent the group is cyclic of the exponent, carried
by a uniformizer.  The statement for inertia is therefore made at primes away from the exponent, and
that is the arithmetic input this file names.

What it is used for is the converse of the dictionary between local classes and characters: a
character to be prescribed on a decomposition subgroup is turned into a class in the completion at
the place below, and then any unit built to have that class — by an approximation at finitely many
places, say — carries the prescribed character there.  In that form the prescription is a demand on
local classes, which is what an arithmetic construction supplies.

## Main definitions

* `InverseGalois.CFT.HasKummerCharInertiaLift` — **every character of the inertia subgroup at a
  prime away from the exponent is the Kummer character of a unit of the base field.**

## Main results

* `InverseGalois.CFT.exists_localClass_forall_kummerChar_eq` — **a character of a decomposition
  subgroup, or of the inertia subgroup at a prime away from the exponent, is named by a class in
  the completion at the place below**: every unit with that class carries the character there.

## Tags

Kummer theory, decomposition group, inertia subgroup, local class, completion, character
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

open scoped Pointwise

section Lift

variable {K : Type} {Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [IsAlgClosed Ω] {n : ℕ} [NeZero n] {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

/-- **Every character of the inertia subgroup at a prime away from the exponent is the Kummer
character of a unit of the base field.**

The character is asked to be a character — additive on the subgroup — and to be trivial on an open
subgroup, which is what a character of a finite quotient is.  The prime is asked to be away from the
exponent, where the characters of inertia are cyclic of the exponent, carried by a uniformizer. -/
def HasKummerCharInertiaLift : Prop :=
  ∀ (P : Ideal (𝓞 Ω)) [P.IsPrime], P ≠ ⊥ → (n : 𝓞 Ω) ∉ P →
    ∀ χ : ↥(Ideal.inertia Gal(Ω/K) P) → ZMod n, (∀ x y : ↥(Ideal.inertia Gal(Ω/K) P),
      χ (x * y) = χ x + χ y) →
      (∃ N : Subgroup Gal(Ω/K), IsOpen (N : Set Gal(Ω/K)) ∧
        ∀ x : ↥(Ideal.inertia Gal(Ω/K) P), (x : Gal(Ω/K)) ∈ N → χ x = 0) →
      ∃ a : Kˣ, ∀ x : ↥(Ideal.inertia Gal(Ω/K) P), kummerChar h a (x : Gal(Ω/K)) = χ x

/-- **A character of a decomposition subgroup, or of the inertia subgroup at a prime away from the
exponent, is named by a class in the completion at the place below**: every unit with that class
carries the character there.

One unit carrying the character is produced — by Kummer theory for the whole decomposition subgroup
and by the arithmetic input for inertia — and its class in the completion is the class the statement
names; a unit with the same class has the same character on the whole decomposition subgroup, hence
on the subgroup at hand. -/
theorem exists_localClass_forall_kummerChar_eq (hlift : HasKummerCharInertiaLift h)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal = Ideal.under (𝓞 K) P) {A : Subgroup Gal(Ω/K)}
    (hA : A = stabilizer Gal(Ω/K) P ∨ (A = Ideal.inertia Gal(Ω/K) P ∧ (n : 𝓞 Ω) ∉ P))
    (χ : ↥A → ZMod n) (hχ : ∀ x y : ↥A, χ (x * y) = χ x + χ y)
    (hsm : ∃ N : Subgroup Gal(Ω/K), IsOpen (N : Set Gal(Ω/K)) ∧
      ∀ x : ↥A, (x : Gal(Ω/K)) ∈ N → χ x = 0) :
    ∃ c : localClasses v n, ∀ a : Kˣ, localClassHom v n a = c →
      ∀ x : ↥A, kummerChar h a (x : Gal(Ω/K)) = χ x := by
  have hAle : A ≤ stabilizer Gal(Ω/K) P := by
    rcases hA with rfl | ⟨rfl, -⟩
    · exact le_rfl
    · exact Ideal.inertia_le_stabilizer P
  obtain ⟨a₀, ha₀⟩ : ∃ a : Kˣ, ∀ x : ↥A, kummerChar h a (x : Gal(Ω/K)) = χ x := by
    rcases hA with rfl | ⟨rfl, hnP⟩
    · exact exists_units_forall_kummerChar_eq_of_stabilizer h hP χ hχ hsm
    · exact hlift P hP hnP χ hχ hsm
  refine ⟨localClassHom v n a₀, fun a hac x => ?_⟩
  rw [kummerChar_eq_of_localClassHom_eq h hv hac (hAle x.2)]
  exact ha₀ x

/-- **Every character of a decomposition subgroup is named by a class in the completion at the place
below**: every unit with that class carries the character there.  No arithmetic input is spent. -/
theorem exists_localClass_forall_kummerChar_eq_of_stabilizer {P : Ideal (𝓞 Ω)} [P.IsPrime]
    (hP : P ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.under (𝓞 K) P)
    (χ : ↥(stabilizer Gal(Ω/K) P) → ZMod n)
    (hχ : ∀ x y : ↥(stabilizer Gal(Ω/K) P), χ (x * y) = χ x + χ y)
    (hsm : ∃ N : Subgroup Gal(Ω/K), IsOpen (N : Set Gal(Ω/K)) ∧
      ∀ x : ↥(stabilizer Gal(Ω/K) P), (x : Gal(Ω/K)) ∈ N → χ x = 0) :
    ∃ c : localClasses v n, ∀ a : Kˣ, localClassHom v n a = c →
      ∀ x : ↥(stabilizer Gal(Ω/K) P), kummerChar h a (x : Gal(Ω/K)) = χ x := by
  obtain ⟨a₀, ha₀⟩ := exists_units_forall_kummerChar_eq_of_stabilizer h hP χ hχ hsm
  refine ⟨localClassHom v n a₀, fun a hac x => ?_⟩
  rw [kummerChar_eq_of_localClassHom_eq h hv hac x.2]
  exact ha₀ x

end Lift

end InverseGalois.CFT

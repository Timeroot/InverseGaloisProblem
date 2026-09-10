/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CharLocalClass

/-!
# Prescribing a Kummer character on a decomposition subgroup

A decomposition subgroup at a prime of an algebraically closed extension is the group of
automorphisms over the field it fixes, and that field is the one in which the base field is dense
at the place below.  Kummer theory there identifies the characters of the subgroup with the classes
of that field modulo powers, and those classes are already the classes of the completion, which the
base field exhausts.  So a character of a decomposition subgroup, or of the inertia subgroup inside
it, ought to be the Kummer character of a unit of the base field.

That statement is the arithmetic input this file names.  What it is used for is the converse of the
dictionary between local classes and characters: a character to be prescribed on a decomposition
subgroup is turned into a class in the completion at the place below, and then any unit built to
have that class — by an approximation at finitely many places, say — carries the prescribed
character there.  In that form the prescription is a demand on local classes, which is what an
arithmetic construction supplies.

## Main definitions

* `InverseGalois.CFT.HasKummerCharLift` — **every character of a decomposition subgroup, or of the
  inertia subgroup inside it, is the Kummer character of a unit of the base field.**

## Main results

* `InverseGalois.CFT.exists_localClass_forall_kummerChar_eq` — **a character of a decomposition or
  inertia subgroup is named by a class in the completion at the place below**: every unit with that
  class carries the character there.

## Tags

Kummer theory, decomposition group, inertia subgroup, local class, completion, character
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

open scoped Pointwise

section Lift

variable {K : Type} {Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {n : ℕ} [NeZero n] {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

/-- **Every character of a decomposition subgroup, or of the inertia subgroup inside it, is the
Kummer character of a unit of the base field.**

The character is asked to be a character — additive on the subgroup — and to be trivial on an open
subgroup, which is what a character of a finite quotient is.  The two subgroups the statement
admits are the two the ramification of a lift is measured along. -/
def HasKummerCharLift : Prop :=
  ∀ (P : Ideal (𝓞 Ω)) [P.IsPrime], P ≠ ⊥ → ∀ A : Subgroup Gal(Ω/K),
    (A = stabilizer Gal(Ω/K) P ∨ A = Ideal.inertia Gal(Ω/K) P) →
    ∀ χ : ↥A → ZMod n, (∀ x y : ↥A, χ (x * y) = χ x + χ y) →
      (∃ N : Subgroup Gal(Ω/K), IsOpen (N : Set Gal(Ω/K)) ∧
        ∀ x : ↥A, (x : Gal(Ω/K)) ∈ N → χ x = 0) →
      ∃ a : Kˣ, ∀ x : ↥A, kummerChar h a (x : Gal(Ω/K)) = χ x

/-- **A character of a decomposition or inertia subgroup is named by a class in the completion at
the place below**: every unit with that class carries the character there.

One unit carrying the character is produced, and its class in the completion is the class the
statement names; a unit with the same class has the same character on the whole decomposition
subgroup, hence on the subgroup at hand. -/
theorem exists_localClass_forall_kummerChar_eq (hlift : HasKummerCharLift h)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal = Ideal.under (𝓞 K) P) {A : Subgroup Gal(Ω/K)}
    (hA : A = stabilizer Gal(Ω/K) P ∨ A = Ideal.inertia Gal(Ω/K) P) (χ : ↥A → ZMod n)
    (hχ : ∀ x y : ↥A, χ (x * y) = χ x + χ y)
    (hsm : ∃ N : Subgroup Gal(Ω/K), IsOpen (N : Set Gal(Ω/K)) ∧
      ∀ x : ↥A, (x : Gal(Ω/K)) ∈ N → χ x = 0) :
    ∃ c : localClasses v n, ∀ a : Kˣ, localClassHom v n a = c →
      ∀ x : ↥A, kummerChar h a (x : Gal(Ω/K)) = χ x := by
  have hAle : A ≤ stabilizer Gal(Ω/K) P := by
    rcases hA with rfl | rfl
    · exact le_rfl
    · exact Ideal.inertia_le_stabilizer P
  obtain ⟨a₀, ha₀⟩ := hlift P hP A hA χ hχ hsm
  refine ⟨localClassHom v n a₀, fun a hac x => ?_⟩
  rw [kummerChar_eq_of_localClassHom_eq h hv hac (hAle x.2)]
  exact ha₀ x

end Lift

end InverseGalois.CFT

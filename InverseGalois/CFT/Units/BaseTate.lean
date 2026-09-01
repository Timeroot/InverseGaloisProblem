/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.BaseFundamental

/-!
# Tate's theorem for the idele class group of a Galois extension of number fields

The three conditions defining a class formation hold for the idele class group of any Galois
extension of number fields, with no restriction on the base: the first cohomology vanishes on every
subgroup of the Galois group, the second is finite with at most as many elements as the subgroup,
and there is a class of the second cohomology annihilated by exactly the multiples of the degree.
Naming that class turns the conditional statements of `InverseGalois.CFT.Units.IdeleClassTate` into
unconditional ones.

Tate's theorem then computes the complete cohomology of the idele class group in every degree from
that of the trivial integral representation, and the theorem of Tate and Nakayama does the same
after tensoring with any representation flat over the integers.  In degree minus two the first of
these is the reciprocity law: the complete cohomology of the integers in degree minus two is the
abelianization of the Galois group, and that of the idele class group in degree zero is the idele
classes of the base modulo the norms.

## Main results

* `InverseGalois.CFT.baseFundamentalClass`: the class of the second cohomology of the idele class
  group of a Galois extension of number fields annihilated by exactly the multiples of the degree.
* `InverseGalois.CFT.isTateClassTwo_baseFundamentalClass`: **it satisfies the classical hypotheses
  of Tate's theorem on every subgroup of the Galois group.**
* `InverseGalois.CFT.baseTateEquiv`: **Tate's theorem for the idele class group of a Galois
  extension of number fields**, with no hypotheses.
* `InverseGalois.CFT.baseReciprocityEquiv`: **the reciprocity isomorphism** in complete cohomology,
  the case of degree minus two.
* `InverseGalois.CFT.baseTateNakayamaEquiv`: **the theorem of Tate and Nakayama for the idele class
  group of a Galois extension of number fields**, for coefficients flat over the integers.

## Tags

number field, idele class group, class formation, fundamental class, Tate's theorem,
Tate-Nakayama, reciprocity
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory groupCohomology NumberField

namespace InverseGalois.CFT

noncomputable section

open Tate

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **The fundamental class of a Galois extension of number fields**: a class of the second
cohomology of the idele class group annihilated by exactly the multiples of the degree. -/
def baseFundamentalClass : tateModule (ideleClassRep k K) 2 :=
  (exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_base k K).choose

/-- **The fundamental class is annihilated by exactly the multiples of the degree.** -/
theorem zsmul_baseFundamentalClass_eq_zero_imp_dvd :
    ∀ m : ℤ, m • baseFundamentalClass k K = 0 → (Nat.card Gal(K/k) : ℤ) ∣ m :=
  (exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_base k K).choose_spec

/-- **The idele class group of a Galois extension of number fields, with its fundamental class,
satisfies the classical hypotheses of Tate's theorem on every subgroup of the Galois group.** -/
theorem isTateClassTwo_baseFundamentalClass (S : Subgroup Gal(K/k)) :
    IsTateClassTwo S (ideleClassRep k K) (baseFundamentalClass k K) :=
  isTateClassTwo_ideleClassRep S (zsmul_baseFundamentalClass_eq_zero_imp_dvd k K)

/-- **Tate's theorem for the idele class group of a Galois extension of number fields**: the
complete cohomology of the trivial integral representation in a degree is the complete cohomology
of the idele class group two degrees higher. -/
def baseTateEquiv (n : ℤ) :
    tateModule (Rep.trivial ℤ Gal(K/k) ℤ) n ≃ₗ[ℤ] tateModule (ideleClassRep k K) (n + 1 + 1) :=
  tateIdeleClassEquiv (baseFundamentalClass k K)
    (zsmul_baseFundamentalClass_eq_zero_imp_dvd k K) n

/-- **The reciprocity isomorphism for a Galois extension of number fields**: the complete cohomology
of the trivial integral representation in degree minus two — the abelianization of the Galois group
— is the complete cohomology of the idele class group in degree zero — the idele classes of the
base modulo the norms from the extension. -/
def baseReciprocityEquiv :
    tateModule (Rep.trivial ℤ Gal(K/k) ℤ) (-2) ≃ₗ[ℤ] tateModule (ideleClassRep k K) 0 :=
  baseTateEquiv k K (-2)

/-- **The theorem of Tate and Nakayama for the idele class group of a Galois extension of number
fields**: for coefficients flat over the integers, the complete cohomology of a representation in a
degree is the complete cohomology of its tensor product with the idele class group two degrees
higher. -/
def baseTateNakayamaEquiv (M : Rep ℤ Gal(K/k)) (hM : Module.Flat ℤ ↥M.V) (n : ℤ) :
    tateModule M n ≃ₗ[ℤ] tateModule (tensorObj (ideleClassRep k K) M) (n + 1 + 1) :=
  tateNakayamaIdeleClass (baseFundamentalClass k K)
    (zsmul_baseFundamentalClass_eq_zero_imp_dvd k K) M hM n

end

end InverseGalois.CFT

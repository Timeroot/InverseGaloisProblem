/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TateClassCount
import InverseGalois.CFT.Units.IdeleClassH1Full

/-!
# The idele class group as the module of a class formation

The first cohomology of the idele class group of a Galois extension of number fields vanishes, and
the restriction of the representation to a subgroup of the Galois group is the representation
attached to the extension over the fixed field of that subgroup.  So the vanishing holds on every
subgroup at once, and in the language of complete cohomology it says that the module of degree one
is the zero module for every subgroup of the Galois group.

That is the first of the three conditions which the classical hypotheses of Tate's theorem were
reduced to: vanishing in degree one, a count in degree two, and the order of a class over the whole
group.  Supplying the other two therefore turns the idele class group into a class formation, and
the machinery of Tate and of Tate and Nakayama applies to it verbatim: the complete cohomology of
the trivial integral representation in a degree becomes the complete cohomology of the idele class
group two degrees higher, and tensoring with a representation flat over the integers does the same.

## Main results

* `InverseGalois.CFT.isZero_tateModule_resObj_ideleClassRep_one`: **the complete cohomology of the
  idele class group in degree one vanishes on every subgroup of the Galois group.**
* `InverseGalois.CFT.isTateClassTwo_ideleClassRep`: **the classical hypotheses of Tate's theorem
  hold for the idele class group** as soon as the degree two is finite of the order of the subgroup
  and the class is annihilated by exactly the multiples of the degree.
* `InverseGalois.CFT.tateIdeleClassEquiv`: **Tate's theorem for the idele class group.**
* `InverseGalois.CFT.tateNakayamaIdeleClass`: **the theorem of Tate and Nakayama for the idele class
  group**, for coefficients flat over the integers.

## Tags

number field, idele class group, class formation, Tate cohomology, Tate-Nakayama
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory Tate

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-! ### Degree one -/

/-- **The complete cohomology of the idele class group in degree one vanishes on every subgroup of
the Galois group.**  The restriction of the representation to a subgroup is the representation
attached to the extension over the fixed field of that subgroup, and the first cohomology of the
idele class group of any Galois extension of number fields vanishes. -/
theorem isZero_tateModule_resObj_ideleClassRep_one (S : Subgroup Gal(K/k)) :
    Limits.IsZero (tateModule (resObj S (ideleClassRep k K)) 1) :=
  isZero_of_forall_eq_zero fun y =>
    eq_zero_H1_res_subgroup S (fun z => eq_zero_H1_ideleClassRep_general z) y

/-! ### The hypotheses of Tate's theorem -/

/-- **The classical hypotheses of Tate's theorem hold for the idele class group** on a subgroup of
the Galois group as soon as the complete cohomology in degree two is finite with as many elements as
the subgroup and the class is annihilated by exactly the multiples of the degree of the extension.
The vanishing in degree one is already known. -/
theorem isTateClassTwo_ideleClassRep {α : tateModule (ideleClassRep k K) 2} (S : Subgroup Gal(K/k))
    (hfin : Finite ↥(tateModule (resObj S (ideleClassRep k K)) 2))
    (hcard : Nat.card ↥(tateModule (resObj S (ideleClassRep k K)) 2) = Nat.card ↥S)
    (hα : ∀ m : ℤ, m • α = 0 → (Nat.card Gal(K/k) : ℤ) ∣ m) :
    IsTateClassTwo S (ideleClassRep k K) α :=
  isTateClassTwo_of_card S (isZero_tateModule_resObj_ideleClassRep_one S) hfin hcard hα

variable (α : tateModule (ideleClassRep k K) 2)
  (hfin : ∀ S : Subgroup Gal(K/k), Finite ↥(tateModule (resObj S (ideleClassRep k K)) 2))
  (hcard : ∀ S : Subgroup Gal(K/k),
    Nat.card ↥(tateModule (resObj S (ideleClassRep k K)) 2) = Nat.card ↥S)
  (hα : ∀ m : ℤ, m • α = 0 → (Nat.card Gal(K/k) : ℤ) ∣ m)

/-- **Tate's theorem for the idele class group**: the complete cohomology of the trivial integral
representation in a degree is the complete cohomology of the idele class group two degrees higher.
-/
def tateIdeleClassEquiv (n : ℤ) :
    tateModule (Rep.trivial ℤ Gal(K/k) ℤ) n ≃ₗ[ℤ] tateModule (ideleClassRep k K) (n + 1 + 1) :=
  tateTheoremTwoEquivOfCard (ideleClassRep k K) α
    (fun S => isZero_tateModule_resObj_ideleClassRep_one S) hfin hcard hα n

/-- **The theorem of Tate and Nakayama for the idele class group**: for coefficients flat over the
integers, the complete cohomology of a representation in a degree is the complete cohomology of its
tensor product with the idele class group two degrees higher. -/
def tateNakayamaIdeleClass (M : Rep ℤ Gal(K/k)) (hM : Module.Flat ℤ ↥M.V) (n : ℤ) :
    tateModule M n ≃ₗ[ℤ] tateModule (tensorObj (ideleClassRep k K) M) (n + 1 + 1) :=
  tateNakayamaFlatEquivOfCard (ideleClassRep k K) α
    (fun S => isZero_tateModule_resObj_ideleClassRep_one S) hfin hcard hα M hM n

end

end InverseGalois.CFT

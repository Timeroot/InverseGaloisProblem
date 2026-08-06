import InverseGalois.Rigidity.RET.Pi1.Etale.AbsoluteGalois
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The fundamental theorem of Galois theory as a categorical equivalence

Assembling the Galois-category structure on finite étale `K`-algebras (`FiberFunctor` +
`GaloisCategory`) with the identification of the automorphism group of the fibre functor as the
absolute Galois group (`AbsoluteGalois`), this file states the **fundamental theorem of Galois
theory** in its Grothendieck form: an equivalence of categories.

* `etaleEquivContActionAut` — for any field `K`, the opposite of the category of finite étale
  `K`-algebras is equivalent to the category of finite continuous `Aut F`-sets, where
  `F = fibreFunctor K (AlgebraicClosure K)`.  This is the Grothendieck–Galois equivalence
  `functorToContAction` packaged as an `Equivalence`.

* `galContMulEquiv` — for a perfect field `K`, the absolute Galois group
  `Gal(K̄/K) = AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` is isomorphic, as a topological group,
  to `Aut F`.  This upgrades the group isomorphism `absoluteGaloisEquivAut` to a
  `ContinuousMulEquiv`, using the fact that the underlying bijection is a homeomorphism for the
  Krull topology on the source and the natural topology on `Aut F`.

* `etaleEquivContActionAbsoluteGalois` — transporting the equivalence along that topological-group
  isomorphism, for a perfect field `K` the opposite of the category of finite étale `K`-algebras is
  equivalent to the category of finite continuous `Gal(K̄/K)`-sets.  This is the classical
  statement: finite separable extensions of `K` correspond to finite continuous actions of the
  absolute Galois group.
-/

open CategoryTheory Limits Functor PreGaloisCategory

open scoped FintypeCatDiscrete

namespace Rigidity.RET.Etale.FiniteEtaleAlgCat

universe u
variable (K : Type u) [Field K]

/-- **Grothendieck–Galois equivalence.** For any field `K`, the opposite of the category of finite
étale `K`-algebras is equivalent to the category of finite continuous `Aut F`-sets, where
`F = fibreFunctor K (AlgebraicClosure K)` is the fibre functor. -/
noncomputable def etaleEquivContActionAut :
    (FiniteEtaleAlgCat.{u} K)ᵒᵖ ≌
      ContAction FintypeCat (Aut (fibreFunctor K (AlgebraicClosure K))) :=
  (functorToContAction (fibreFunctor K (AlgebraicClosure K))).asEquivalence

/-- For a perfect field `K`, the absolute Galois group `Gal(K̄/K)` is isomorphic, as a topological
group, to the automorphism group of the fibre functor. -/
noncomputable def galContMulEquiv [PerfectField K] :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≃ₜ*
      Aut (fibreFunctor K (AlgebraicClosure K)) :=
  ContinuousMulEquiv.mk'
    (PreGaloisCategory.toAutHomeo (fibreFunctor K (AlgebraicClosure K))
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
    (fun x y => by
      simp only [PreGaloisCategory.toAutHomeo_apply]
      exact map_mul (PreGaloisCategory.toAut (fibreFunctor K (AlgebraicClosure K))
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) x y)

/-- **Fundamental theorem of Galois theory (Grothendieck form).** For a perfect field `K`, the
opposite of the category of finite étale `K`-algebras is equivalent to the category of finite
continuous `Gal(K̄/K)`-sets. -/
noncomputable def etaleEquivContActionAbsoluteGalois [PerfectField K] :
    (FiniteEtaleAlgCat.{u} K)ᵒᵖ ≌
      ContAction FintypeCat (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
  (etaleEquivContActionAut K).trans (ContAction.resEquiv FintypeCat (galContMulEquiv K))

end Rigidity.RET.Etale.FiniteEtaleAlgCat

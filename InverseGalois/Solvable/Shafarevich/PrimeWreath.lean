/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.Solvable.WreathFunctor
import InverseGalois.Solvable.Shafarevich.FrattiniKernel
import InverseGalois.Solvable.Shafarevich.Radicand
import InverseGalois.Solvable.Shafarevich.WreathGalois

/-!
# Wreathing a realizable group by a group of prime order

Let `U` be a Galois group over `ℚ` and let `C` be a group of prime order `p`.  Enlarging a
realization of `U` by the `p`-th roots of unity gives a Galois number field `N` containing a
primitive `p`-th root of unity whose Galois group still surjects onto `U`.  Inside `N` there is an
element whose Galois orbit is independent modulo `p`-th powers, and adjoining a `p`-th root of every
member of that orbit produces a field whose Galois group over `ℚ` is the regular wreath product of
the `p`-th roots of unity by `Gal(N/ℚ)`.  Since the `p`-th roots of unity and `C` are both cyclic of
order `p`, and since a surjection between the index groups descends to the wreath products, `C ≀ᵣ U`
is a Galois group over `ℚ`.

## Main results

* `InverseGalois.Shafarevich.isInverseGalois_wreath_of_primitiveRoot` — the wreath product of a
  group of prime order `p` by the Galois group of a number field containing a primitive `p`-th root
  of unity is a Galois group over `ℚ`.
* `InverseGalois.Shafarevich.isInverseGalois_wreath_of_prime` — **wreathing a realizable group by a
  group of prime order preserves realizability over `ℚ`.**
* `Shafarevich.primeWreathEP` — the same statement in the packaged form consumed by the reduction
  of Shafarevich's theorem.
* `Shafarevich.isInverseGalois_of_isSolvable_of_frattiniKernelEP` — **every finite solvable group
  is a Galois group over `ℚ`**, granting only the embedding problems whose minimal kernel lies
  inside the Frattini subgroup.

## Tags

inverse Galois problem, wreath product, Kummer theory, cyclotomic field
-/

open Polynomial InverseGalois.CFT

namespace InverseGalois.Shafarevich

/-! ### The base already contains the roots of unity -/

/-- **The wreath product of a group of prime order `p` by the Galois group of a number field
containing a primitive `p`-th root of unity is a Galois group over `ℚ`.** -/
theorem isInverseGalois_wreath_of_primitiveRoot (C : Type) [CommGroup C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hC : Nat.card C = p) (N : Type) [Field N] [NumberField N] [IsGalois ℚ N]
    {zeta : N} (hz : IsPrimitiveRoot zeta p) :
    IsInverseGalois (C ≀ᵣ Gal(N/ℚ)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨b, hne, hinj, hindep⟩ := exists_conj_indep (p := p) N
  haveI : IsGalois ℚ (ConjRadExt ℚ p b) := isGalois_conjRadExt hinj
  haveI := isSplittingField_conjRadExt (F := ℚ) (p := p) hinj
  haveI : FiniteDimensional ℚ (ConjRadExt ℚ p b) :=
    Polynomial.IsSplittingField.finiteDimensional _ ((minpoly ℚ b).comp (X ^ p))
  haveI : HasEnoughRootsOfUnity (ConjRadExt ℚ p b) p :=
    (orbitSetup (F := ℚ) hz hne hindep).hasEnoughRootsOfUnity
  obtain ⟨ψ⟩ := nonempty_mulEquiv_wreath_conjRadExt (F := ℚ) hz hne hinj hindep
  have hbig : IsInverseGalois (rootsOfUnity p (ConjRadExt ℚ p b) ≀ᵣ Gal(N/ℚ)) :=
    ⟨ConjRadExt ℚ p b, inferInstance, inferInstance, inferInstance, inferInstance, ⟨ψ⟩⟩
  have hcard : Nat.card (rootsOfUnity p (ConjRadExt ℚ p b)) = p :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity _ _
  exact hbig.of_surjective
    (RegularWreathProduct.mapLeft (mulEquivOfPrimeCardEq hcard hC).toMonoidHom)
    (RegularWreathProduct.mapLeft_surjective (mulEquivOfPrimeCardEq hcard hC).surjective)

/-! ### The general case -/

set_option synthInstance.maxHeartbeats 800000 in
/-- **Wreathing a realizable group by a group of prime order preserves realizability over `ℚ`.**

The compositum of a realization of `U` with the `p`-th cyclotomic field is a Galois number field
containing a primitive `p`-th root of unity whose Galois group still surjects onto `U`. -/
theorem isInverseGalois_wreath_of_prime (C U : Type) [CommGroup C] [Finite C] [Group U] [Finite U]
    (hp : (Nat.card C).Prime) (hU : IsInverseGalois U) : IsInverseGalois (C ≀ᵣ U) := by
  classical
  haveI : NeZero (Nat.card C) := ⟨hp.ne_zero⟩
  obtain ⟨L, _, alg, _, _, ⟨φ⟩⟩ := hU
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  -- a field of characteristic zero carries only one `ℚ`-algebra structure
  obtain rfl : alg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  haveI : NumberField L := ⟨⟩
  -- the compositum of `L` with the cyclotomic field contains a primitive root of unity
  have hmemcyc : cycRoot (Nat.card C) ∈ cycSubfield (Nat.card C) :=
    IntermediateField.mem_adjoin_simple_self ℚ _
  have hmem : cycRoot (Nat.card C) ∈ cycCompositum L (Nat.card C) :=
    (le_sup_right : cycSubfield (Nat.card C) ≤ cycCompositum L (Nat.card C)) hmemcyc
  have hcoe : algebraMap ↥(cycCompositum L (Nat.card C)) (AlgebraicClosure ℚ)
      ⟨cycRoot (Nat.card C), hmem⟩ = cycRoot (Nat.card C) := rfl
  have hz : IsPrimitiveRoot (⟨cycRoot (Nat.card C), hmem⟩ :
      ↥(cycCompositum L (Nat.card C))) (Nat.card C) := by
    refine IsPrimitiveRoot.of_map_of_injective
      (f := algebraMap ↥(cycCompositum L (Nat.card C)) (AlgebraicClosure ℚ)) ?_
      (algebraMap ↥(cycCompositum L (Nat.card C)) (AlgebraicClosure ℚ)).injective
    rw [hcoe]
    exact cycRoot_spec _
  have hbig := isInverseGalois_wreath_of_primitiveRoot C hp rfl
    ↥(cycCompositum L (Nat.card C)) hz
  -- the Galois group of the compositum still surjects onto `U`
  set ε : Gal(↥(innerL L (Nat.card C))/ℚ) ≃* U :=
    (AlgEquiv.autCongr (innerLEquiv L (Nat.card C))).trans
      ((AlgEquiv.autCongr (embEquiv L)).symm.trans φ) with hεdef
  have hsurj : Function.Surjective (ε.toMonoidHom.comp
      (AlgEquiv.restrictNormalHom (F := ℚ)
        (K₁ := ↥(cycCompositum L (Nat.card C))) ↥(innerL L (Nat.card C)))) :=
    (MulEquiv.surjective ε).comp (AlgEquiv.restrictNormalHom_surjective (F := ℚ)
      (K₁ := ↥(innerL L (Nat.card C))) ↥(cycCompositum L (Nat.card C)))
  exact IsInverseGalois.wreath_of_surjective_right _ hsurj hbig

end InverseGalois.Shafarevich

namespace Shafarevich

/-- **Wreathing a realizable group by a group of prime order preserves realizability over `ℚ`.** -/
theorem primeWreathEP : PrimeWreathEP := by
  intro C U _ _ _ _ hp hU
  exact InverseGalois.Shafarevich.isInverseGalois_wreath_of_prime C U hp hU

/-- **Split embedding problems over `ℚ` with an elementary abelian minimal kernel are solvable.** -/
theorem elementaryAbelianKernelEP_of_frattiniKernelEP' (h : FrattiniKernelEP) :
    ElementaryAbelianKernelEP :=
  elementaryAbelianKernelEP_of_frattiniKernelEP_of_primeWreathEP h primeWreathEP

/-- **Shafarevich's theorem for the Frattini-kernel embedding problem.**

Every finite solvable group is a Galois group over `ℚ` as soon as the embedding problems whose
minimal kernel lies inside the Frattini subgroup can be solved. -/
theorem isInverseGalois_of_isSolvable_of_frattiniKernelEP (h : FrattiniKernelEP) (G : Type)
    [Group G] [Finite G] [IsSolvable G] : IsInverseGalois G :=
  isSolvable_isInverseGalois_of_frattiniKernelEP_of_primeWreathEP h primeWreathEP G

end Shafarevich

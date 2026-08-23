/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Lattice

/-!
# Commensurable lattices in a common ambient group

Two lattices sitting inside one abelian group and each carried into the other by multiplication by
a nonzero integer have the same rank, and the multiplication that carries one into the other is an
injection of lattices of equal rank.  If both are stable under an automorphism of the ambient group
the injection is equivariant, so the two Herbrand quotients agree.

This is the form the comparison takes in arithmetic.  Two lattices spanning the same rational
subspace of a real vector space -- the lattice of `S`-units under the logarithmic embedding and the
lattice of integral divisors of trace zero supported on `S`, say -- are commensurable in exactly
this sense, and the Galois group acts on the ambient space, so the computation for the second
lattice transfers to the first.

## Main results

* `InverseGalois.CFT.nsmulHom`: multiplication by an integer, as a map of one lattice into another
  that contains its multiples.
* `InverseGalois.CFT.finrank_eq_of_nsmul_mem`: **commensurable lattices have the same rank.**
* `InverseGalois.CFT.herbrand_eq_of_nsmul_mem`: an equivariant lattice of the same rank whose
  multiples lie in another has the Herbrand quotient of that other.
* `InverseGalois.CFT.herbrand_eq_of_commensurable`: **commensurable stable lattices in a common
  ambient group have the same Herbrand quotient.**

## Tags

Tate cohomology, Herbrand quotient, lattice, commensurable
-/

namespace InverseGalois.CFT

variable {V : Type*} [AddCommGroup V] {n : ℕ} {L M : AddSubgroup V}

/-! ### Multiplication by an integer as a map of lattices -/

/-- **Multiplication by an integer**, as a map of one subgroup into another that contains its
multiples. -/
def nsmulHom (L M : AddSubgroup V) (N : ℕ) (h : ∀ x ∈ L, N • x ∈ M) : L →+ M where
  toFun x := ⟨N • (x : V), h x x.2⟩
  map_zero' := by
    ext
    simp
  map_add' x y := by
    ext
    simp

@[simp]
theorem coe_nsmulHom (N : ℕ) (h : ∀ x ∈ L, N • x ∈ M) (x : L) :
    (nsmulHom L M N h x : V) = N • (x : V) := rfl

theorem injective_nsmulHom [Module.Free ℤ L] {N : ℕ} (hN : N ≠ 0) (h : ∀ x ∈ L, N • x ∈ M) :
    Function.Injective (nsmulHom L M N h) := by
  intro x y hxy
  have hV : N • (x : V) = N • (y : V) := congrArg Subtype.val hxy
  have hL : (N : ℤ) • x = (N : ℤ) • y := by
    refine Subtype.ext ?_
    rw [AddSubgroup.coe_zsmul, AddSubgroup.coe_zsmul, natCast_zsmul, natCast_zsmul, hV]
  exact smul_right_injective L (Int.natCast_ne_zero.2 hN) hL

/-! ### Equal ranks -/

/-- **Commensurable lattices have the same rank.** -/
theorem finrank_eq_of_nsmul_mem [Module.Free ℤ L] [Module.Finite ℤ L] [Module.Free ℤ M]
    [Module.Finite ℤ M] {N N' : ℕ} (hN : N ≠ 0) (hN' : N' ≠ 0) (h : ∀ x ∈ L, N • x ∈ M)
    (h' : ∀ x ∈ M, N' • x ∈ L) : Module.finrank ℤ L = Module.finrank ℤ M :=
  le_antisymm
    (LinearMap.finrank_le_finrank_of_injective (f := (nsmulHom L M N h).toIntLinearMap)
      (injective_nsmulHom hN h))
    (LinearMap.finrank_le_finrank_of_injective (f := (nsmulHom M L N' h').toIntLinearMap)
      (injective_nsmulHom hN' h'))

/-! ### The Herbrand quotient -/

variable {σV : V ≃+ V} {σL : L ≃+ L} {σM : M ≃+ M}

/-- Multiplication by an integer commutes with an automorphism of the ambient group. -/
theorem nsmulHom_equivariant (hσL : ∀ x : L, (σL x : V) = σV (x : V))
    (hσM : ∀ y : M, (σM y : V) = σV (y : V)) {N : ℕ} (h : ∀ x ∈ L, N • x ∈ M) (x : L) :
    nsmulHom L M N h (σL x) = σM (nsmulHom L M N h x) := by
  refine Subtype.ext ?_
  rw [coe_nsmulHom, hσL, hσM, coe_nsmulHom, map_nsmul]

/-- **An equivariant lattice of the same rank whose multiples lie in another has the Herbrand
quotient of that other.** -/
theorem herbrand_eq_of_nsmul_mem [Module.Free ℤ L] [Module.Finite ℤ L] [Module.Free ℤ M]
    [Module.Finite ℤ M] (hσLn : σL ^ n = 1) (hσMn : σM ^ n = 1)
    (hσL : ∀ x : L, (σL x : V) = σV (x : V)) (hσM : ∀ y : M, (σM y : V) = σV (y : V))
    {N : ℕ} (hN : N ≠ 0) (h : ∀ x ∈ L, N • x ∈ M)
    (hrank : Module.finrank ℤ L = Module.finrank ℤ M)
    [Finite (tateH0 σL n)] [Finite (tateH0 σM n)]
    [Finite (tateHm1 σL n)] [Finite (tateHm1 σM n)] :
    herbrand σL n = herbrand σM n :=
  herbrand_eq_of_injective_of_finrank_eq hσLn hσMn (nsmulHom L M N h)
    (nsmulHom_equivariant hσL hσM h) (injective_nsmulHom hN h) hrank

/-- **Commensurable stable lattices in a common ambient group have the same Herbrand quotient.** -/
theorem herbrand_eq_of_commensurable [Module.Free ℤ L] [Module.Finite ℤ L] [Module.Free ℤ M]
    [Module.Finite ℤ M] (hσLn : σL ^ n = 1) (hσMn : σM ^ n = 1)
    (hσL : ∀ x : L, (σL x : V) = σV (x : V)) (hσM : ∀ y : M, (σM y : V) = σV (y : V))
    {N N' : ℕ} (hN : N ≠ 0) (hN' : N' ≠ 0) (h : ∀ x ∈ L, N • x ∈ M) (h' : ∀ x ∈ M, N' • x ∈ L)
    [Finite (tateH0 σL n)] [Finite (tateH0 σM n)]
    [Finite (tateHm1 σL n)] [Finite (tateHm1 σM n)] :
    herbrand σL n = herbrand σM n :=
  herbrand_eq_of_nsmul_mem hσLn hσMn hσL hσM hN h (finrank_eq_of_nsmul_mem hN hN' h h')

end InverseGalois.CFT

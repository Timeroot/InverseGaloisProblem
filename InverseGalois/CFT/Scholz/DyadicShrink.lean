/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.KerField
import InverseGalois.CFT.Scholz.StrongScholz
import InverseGalois.CFT.Scholz.SubfieldScholz
import InverseGalois.Solvable.DispositionCharacter

/-!
# Shrinking a strong Scholz realization

The free object of rank `d * r` has its distinguished generators indexed by pairs, `r` copies of a
system of `d` generators, and a vector of `r` bits collapses it onto the free object of rank `d` by
keeping the selected copies and killing the rest.  A strong Scholz realization of the large free
object therefore cuts out a subfield, the fixed field of the kernel of the collapse, realising the
small one.

The blocks of the shrunken realization are the unions of the blocks of the selected copies of a
row, and its square roots are the products of the corresponding square roots.  Such a product is
fixed by the kernel of the collapse, because the sign by which an automorphism moves it is the sum
of the coordinates of the row over the selected copies, which is exactly the coordinate the collapse
computes.  For the same reason the shrunken square roots match the distinguished generators of the
small free object, so what is cut out is again a strong Scholz realization.

## Main definitions

* `InverseGalois.CFT.StrongScholzRealization.collapseHom`: the homomorphism onto the small free
  object whose fixed field is the shrunken realization.
* `InverseGalois.CFT.StrongScholzRealization.shrink`: **the shrunken strong Scholz realization.**

## Main results

* `InverseGalois.CFT.sqrtSign_eq_coordClass`: **the sign character of square roots matching the
  distinguished generators is the coordinate character of the free object.**
* `InverseGalois.CFT.StrongScholzRealization.sqrtSign_shrinkSqrtBase`: an automorphism moves the
  product of the selected square roots of a row by the coordinate the collapse computes.

## Tags

Scholz–Reichardt, strong Scholz field, block, free `2`-group, collapse, Shafarevich
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-- The subfield cut out by a homomorphism out of the Galois group of a number field is a number
field. -/
instance numberField_kerField {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A]
    [IsGalois ℚ ↥A] {G : Type*} [Group G] (π : Gal(↥A/ℚ) →* G) : NumberField ↥(kerField π) := ⟨⟩

/-! ### The sign character as the coordinate character -/

/-- **The sign character of square roots matching the distinguished generators is the coordinate
character of the free object.**  Both are homomorphisms sending the `k`-th generator to the `k`-th
standard basis vector, and the generators generate. -/
theorem sqrtSign_eq_coordClass {d c : ℕ} (hc : 1 ≤ c)
    {A : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥A] [IsGalois ℚ ↥A]
    (e : Gal(↥A/ℚ) ≃* FreePClass 2 d c) {v : Fin d → ↥A} (hv : ∀ i, v i ≠ 0) {m : Fin d → ℚ}
    (hvsq : ∀ i, v i ^ 2 = algebraMap ℚ ↥A (m i))
    (hgen : ∀ k i, sqrtSign (v i) (e.symm (FreePClass.gen 2 d c k)) = if i = k then 1 else 0)
    (σ : Gal(↥A/ℚ)) (i : Fin d) :
    sqrtSign (v i) σ = Multiplicative.toAdd (FreePClass.coordClass 2 d hc (e σ)) i := by
  set χ : Gal(↥A/ℚ) →* Multiplicative (Fin d → ZMod 2) := sqrtSignHom v hv hvsq with hχ
  have hψ : χ.comp e.symm.toMonoidHom = FreePClass.coordClass 2 d hc := by
    refine FreePClass.eq_coordClass hc fun k => ?_
    show Multiplicative.ofAdd (fun j => sqrtSign (v j) (e.symm (FreePClass.gen 2 d c k)))
      = Multiplicative.ofAdd (Pi.single k 1)
    exact congrArg _ (funext fun j => by rw [Pi.single_apply]; exact hgen k j)
  have hkey : χ σ = FreePClass.coordClass 2 d hc (e σ) := by
    have h := DFunLike.congr_fun hψ (e σ)
    simpa using h
  show Multiplicative.toAdd (χ σ) i = _
  rw [hkey]

namespace StrongScholzRealization

/-- **Each square root of a strong Scholz realization is nonzero**, its square being a nonzero
product of primes. -/
theorem sqrt_ne_zero {d c N : ℕ} (R : StrongScholzRealization d c N) (i : Fin d) :
    R.sqrt i ≠ 0 := by
  intro hzero
  have h0 : algebraMap ℚ ↥R.carrier ((∏ p ∈ R.block i, p : ℕ) : ℚ) = 0 := by
    rw [← R.sqrt_sq i, hzero, zero_pow (by norm_num : 2 ≠ 0)]
  exact prod_prime_ne_zero (R.blockPrime i)
    (by exact_mod_cast (map_eq_zero_iff _ (algebraMap ℚ ↥R.carrier).injective).mp h0)

/-! ### The collapse of a realization of the free object of composite rank -/

section Shrink

variable {d r n N : ℕ} (R : StrongScholzRealization (d * r) (n + 1) N) (a : Fin r → ZMod 2)

/-- The homomorphism onto the free object of the smaller rank whose fixed field carries the
shrunken realization. -/
noncomputable def collapseHom : Gal(↥R.carrier/ℚ) →* FreePClass 2 d (n + 1) :=
  (FreePClass.collapse a).comp R.galEquiv.toMonoidHom

theorem collapseHom_apply (σ : Gal(↥R.carrier/ℚ)) :
    R.collapseHom a σ = FreePClass.collapse a (R.galEquiv σ) := rfl

/-- **The collapse of a realization is onto as soon as one copy of the generating system is
selected.** -/
theorem collapseHom_surjective {j₀ : Fin r} (hj₀ : a j₀ = 1) :
    Function.Surjective (R.collapseHom a) :=
  (FreePClass.collapse_surjective hj₀).comp R.galEquiv.surjective

/-! ### The blocks and the square roots of the shrunken realization -/

/-- The blocks of the shrunken realization: the blocks of the selected copies of a row, merged. -/
def shrinkBlock (i : Fin d) : Finset ℕ :=
  (Finset.univ.filter fun j => a j = 1).biUnion fun j => R.block (finProdFinEquiv (i, j))

theorem shrinkBlock_prime (i : Fin d) : ∀ p ∈ R.shrinkBlock a i, p.Prime := by
  intro p hp
  obtain ⟨j, -, hpj⟩ := Finset.mem_biUnion.mp hp
  exact R.blockPrime _ p hpj

/-- The blocks of a single row of the shrunken realization are pairwise disjoint. -/
theorem shrinkBlock_pairwiseDisjoint (i : Fin d) :
    (↑(Finset.univ.filter fun j => a j = 1) : Set (Fin r)).PairwiseDisjoint
      fun j => R.block (finProdFinEquiv (i, j)) := by
  intro j _ j' _ hjj'
  exact R.blockDisjoint _ _ fun hq => hjj' (congrArg Prod.snd (finProdFinEquiv.injective hq))

theorem shrinkBlock_disjoint (i i' : Fin d) (h : i ≠ i') :
    Disjoint (R.shrinkBlock a i) (R.shrinkBlock a i') := by
  rw [shrinkBlock, shrinkBlock, Finset.disjoint_biUnion_left]
  intro j _
  rw [Finset.disjoint_biUnion_right]
  intro j' _
  exact R.blockDisjoint _ _ fun hq => h (congrArg Prod.fst (finProdFinEquiv.injective hq))

/-- The square roots of the shrunken realization, read inside the large field: the product of the
square roots of the selected copies of a row. -/
noncomputable def shrinkSqrtBase (i : Fin d) : ↥R.carrier :=
  ∏ j ∈ Finset.univ.filter fun j => a j = 1, R.sqrt (finProdFinEquiv (i, j))

theorem shrinkSqrtBase_sq (i : Fin d) :
    R.shrinkSqrtBase a i ^ 2
      = algebraMap ℚ ↥R.carrier ((∏ p ∈ R.shrinkBlock a i, p : ℕ) : ℚ) := by
  rw [shrinkSqrtBase, sq_prod_eq_algebraMap (v := fun j => R.sqrt (finProdFinEquiv (i, j)))
    (fun j => R.sqrt_sq _)]
  congr 1
  rw [shrinkBlock, Finset.prod_biUnion (R.shrinkBlock_pairwiseDisjoint a i), Nat.cast_prod]

/-- **An automorphism moves the product of the selected square roots of a row by the coordinate the
collapse computes.**  The sign of a product is the sum of the signs, each sign is a coordinate of
the automorphism read in the large free object, and summing the coordinates of a row over the
selected copies is what the collapse does. -/
theorem sqrtSign_shrinkSqrtBase (σ : Gal(↥R.carrier/ℚ)) (i : Fin d) :
    sqrtSign (R.shrinkSqrtBase a i) σ = Multiplicative.toAdd
      (FreePClass.coordClass 2 d (Nat.succ_pos n) (R.collapseHom a σ)) i := by
  have hstep : ∀ j : Fin r, sqrtSign (R.sqrt (finProdFinEquiv (i, j))) σ = Multiplicative.toAdd
      (FreePClass.coordClass 2 (d * r) (Nat.succ_pos n) (R.galEquiv σ)) (finProdFinEquiv (i, j)) :=
    fun j => sqrtSign_eq_coordClass (Nat.succ_pos n) R.galEquiv R.sqrt_ne_zero R.sqrt_sq
      R.sqrtSign_gen σ _
  have hcc : FreePClass.coordClass 2 d (Nat.succ_pos n) (FreePClass.collapse a (R.galEquiv σ))
      = FreePClass.mergeChar d a
        (FreePClass.coordClass 2 (d * r) (Nat.succ_pos n) (R.galEquiv σ)) :=
    DFunLike.congr_fun (FreePClass.coordClass_comp_collapse (n := n) (d := d) a) (R.galEquiv σ)
  rw [shrinkSqrtBase, sqrtSign_prod_apply (v := fun j => R.sqrt (finProdFinEquiv (i, j)))
      (fun j => R.sqrt_ne_zero _) (fun j => R.sqrt_sq _),
    Finset.sum_congr rfl fun j _ => hstep j, ← FreePClass.toAdd_mergeChar d a _ i, ← hcc]
  rfl

theorem shrinkSqrtBase_fixed (i : Fin d) : ∀ σ : Gal(↥R.carrier/ℚ), R.collapseHom a σ = 1 →
    σ (R.shrinkSqrtBase a i) = R.shrinkSqrtBase a i := by
  intro σ hσ
  rw [← sqrtSign_eq_zero_iff (F := ℚ), R.sqrtSign_shrinkSqrtBase a σ i, hσ, map_one]
  rfl

/-! ### The shrunken realization -/

theorem shrinkSqrt_sq (i : Fin d) :
    toKerField (R.collapseHom a) (R.shrinkSqrtBase_fixed a i) ^ 2
      = algebraMap ℚ ↥(kerField (R.collapseHom a)) ((∏ p ∈ R.shrinkBlock a i, p : ℕ) : ℚ) := by
  refine IntermediateField.inclusion_injective (kerField_le (R.collapseHom a)) ?_
  rw [map_pow, inclusion_toKerField, R.shrinkSqrtBase_sq a i, AlgHom.commutes]

/-- **The `k`-th distinguished generator of the small free object changes the sign of the `k`-th
shrunken square root and of no other.** -/
theorem sqrtSign_shrinkSqrt {j₀ : Fin r} (hj₀ : a j₀ = 1) (k i : Fin d) :
    sqrtSign (toKerField (R.collapseHom a) (R.shrinkSqrtBase_fixed a i))
        ((galEquivKerField (R.collapseHom a) (R.collapseHom_surjective a hj₀)).symm
          (FreePClass.gen 2 d (n + 1) k)) = if i = k then 1 else 0 := by
  obtain ⟨σ, hσ⟩ := R.collapseHom_surjective a hj₀ (FreePClass.gen 2 d (n + 1) k)
  have hres : (galEquivKerField (R.collapseHom a) (R.collapseHom_surjective a hj₀)).symm
      (FreePClass.gen 2 d (n + 1) k) = galRestrictLE (kerField_le (R.collapseHom a)) σ := by
    rw [MulEquiv.symm_apply_eq, galEquivKerField_galRestrictLE]
    exact hσ.symm
  rw [hres, ← sqrtSign_inclusion (kerField_le (R.collapseHom a)), inclusion_toKerField,
    R.sqrtSign_shrinkSqrtBase a σ i, hσ, FreePClass.coordClass_gen]
  show (Pi.single k (1 : ZMod 2) : Fin d → ZMod 2) i = _
  rw [Pi.single_apply]

/-- **The shrunken strong Scholz realization**: the fixed field of the kernel of the collapse,
with the merged blocks of the selected copies and the products of their square roots.  Serre's
condition is inherited by a subfield, and the shrunken square roots match the distinguished
generators of the small free object because the collapse sums the coordinates of a row over the
selected copies. -/
noncomputable def shrink {j₀ : Fin r} (hj₀ : a j₀ = 1) : StrongScholzRealization d (n + 1) N where
  carrier := kerField (R.collapseHom a)
  isScholz := IsScholz.of_le (kerField_le (R.collapseHom a)) R.isScholz
  block := R.shrinkBlock a
  blockPrime := R.shrinkBlock_prime a
  blockDisjoint := R.shrinkBlock_disjoint a
  galEquiv := galEquivKerField (R.collapseHom a) (R.collapseHom_surjective a hj₀)
  sqrt := fun i => toKerField (R.collapseHom a) (R.shrinkSqrtBase_fixed a i)
  sqrt_sq := R.shrinkSqrt_sq a
  sqrtSign_gen := R.sqrtSign_shrinkSqrt a hj₀

@[simp] theorem shrink_carrier {j₀ : Fin r} (hj₀ : a j₀ = 1) :
    (R.shrink a hj₀).carrier = kerField (R.collapseHom a) := rfl

theorem shrink_carrier_le {j₀ : Fin r} (hj₀ : a j₀ = 1) : (R.shrink a hj₀).carrier ≤ R.carrier :=
  kerField_le (R.collapseHom a)

/-- **The Galois group of the shrunken realization is the collapse of the Galois group of the
large one.** -/
theorem shrink_galEquiv_galRestrictLE {j₀ : Fin r} (hj₀ : a j₀ = 1) (σ : Gal(↥R.carrier/ℚ)) :
    (R.shrink a hj₀).galEquiv (galRestrictLE (R.shrink_carrier_le a hj₀) σ)
      = FreePClass.collapse a (R.galEquiv σ) :=
  galEquivKerField_galRestrictLE (R.collapseHom a) (R.collapseHom_surjective a hj₀) σ

end Shrink

end StrongScholzRealization

end InverseGalois.CFT

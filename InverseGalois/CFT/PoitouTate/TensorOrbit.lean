/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.OrbitCoboundary
import InverseGalois.CFT.PoitouTate.TensorValuation

/-!
# A class with coefficients in the units, trivial at every place, comes from the units of a set

Let a finite group act on a field and on a module, and let the multiplicative group of the field
carry a valuation onto the free abelian group on a set of places the group permutes, whose kernel
is the group of units for a finite set.  Tensor everything with the module.  A one-cocycle with
values in the tensor product then has, at each place, a valuation which is a one-cocycle for the
subgroup fixing that place; **if every one of those is a coboundary, the class of the cocycle comes
from the tensor product of the units with the module.**

The proof puts together the two halves prepared separately.  The valuation of the cocycle is a
cocycle with values in the permutation module on the places, and it is a coboundary at every place
on the subgroup fixing that place, so it is a coboundary; subtracting the corresponding coboundary
from the cocycle makes its valuation vanish identically.  A cocycle with vanishing valuation takes
its values in the kernel of the valuation after tensoring, because the inclusion of the kernel is
split and therefore stays exact, and the correction was by a coboundary, so the class is unchanged.

This is the mechanism which replaces the whole of the theory of the Shafarevich group by a finite
computation: a class which is locally trivial everywhere is pushed into cohomology with
coefficients in a *finitely generated* module, the units of a number field for a finite set of
places, and cohomology with finitely generated coefficients over a finite group is finite.

## Main definitions

* `InverseGalois.CFT.additiveDistribMulAction`: the action on the additive copy of a module.

## Main results

* `InverseGalois.CFT.exists_tensorVal_sub_eq_zero_of_forall_stabilizer`: **a cocycle whose
  valuation is a coboundary at every place, on the subgroup fixing that place, has vanishing
  valuation after subtracting a coboundary.**
* `InverseGalois.CFT.mem_range_map_tensorSubInclRep_of_forall_stabilizer`: **its class therefore
  comes from cohomology with coefficients in the kernel of the valuation.**

## Tags

group cohomology, permutation module, S-unit, tensor product, Shafarevich group
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction TensorProduct groupCohomology

/-! ### The additive copy of a module -/

section Additive

variable (Q C : Type*) [Group Q] [CommGroup C] [MulDistribMulAction Q C]

/-- **The action of a group on the additive copy of a module it acts on multiplicatively.**  This
is deliberately not an instance: the additive copy of a module is used as a tensor factor, and a
global instance would let the action on one factor be mistaken for the action on the product. -/
def additiveDistribMulAction : DistribMulAction Q (Additive C) where
  smul σ w := Additive.ofMul (σ • w.toMul)
  one_smul w := congrArg Additive.ofMul (one_smul Q w.toMul)
  mul_smul σ τ w := congrArg Additive.ofMul (mul_smul σ τ w.toMul)
  smul_zero σ := congrArg Additive.ofMul (smul_one σ)
  smul_add σ w w' := congrArg Additive.ofMul (smul_mul' σ w.toMul w'.toMul)

end Additive

/-! ### Correcting a cocycle until its valuation vanishes -/

section Correct

variable {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable (C : Type) [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ))

omit [Finite Q] in
/-- **A cocycle which is a coboundary on the subgroup fixing a place has a valuation which is a
coboundary there.**  The valuation at a place is equivariant for the subgroup fixing that place —
that is the whole point of restricting to it — so the valuation of the element trivialising the
cocycle trivialises the valuation of the cocycle. -/
theorem tensorVal_stabilizer_of_res_eq_sub
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    {c : Q → Additive A ⊗[ℤ] Additive C}
    (hres : ∀ x : X, ∃ b : Additive A ⊗[ℤ] Additive C,
      ∀ ρ : Q, ρ • x = x → c ρ = ρ • b - b) (x : X) :
    ∃ u : Additive C, ∀ ρ : Q, ρ • x = x →
      tensorVal C g (c ρ) x = Additive.ofMul (ρ • u.toMul) - u := by
  obtain ⟨b, hb⟩ := hres x
  refine ⟨tensorVal C g b x, fun ρ hρ => ?_⟩
  have hinv : ρ⁻¹ • x = x := inv_smul_eq_iff.2 hρ.symm
  rw [hb ρ hρ, map_sub, Finsupp.sub_apply, tensorVal_smul C g hgeq, hinv]

/-- **A cocycle with values in the tensor product whose valuation is a coboundary at every place,
on the subgroup fixing that place, has vanishing valuation after subtracting a coboundary.**  The
valuation carries the cocycle to a cocycle of the permutation module on the places, where a class
trivial at every point is trivial. -/
theorem exists_tensorVal_sub_eq_zero_of_forall_stabilizer (hg : Function.Surjective g)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    {c : Q → Additive A ⊗[ℤ] Additive C} (hc : ∀ σ τ : Q, c (σ * τ) = σ • c τ + c σ)
    (hloc : ∀ x : X, ∃ u : Additive C, ∀ ρ : Q, ρ • x = x →
      tensorVal C g (c ρ) x = Additive.ofMul (ρ • u.toMul) - u) :
    ∃ t : Additive A ⊗[ℤ] Additive C, ∀ (σ : Q) (x : X),
      tensorVal C g (c σ - (σ • t - t)) x = 0 := by
  letI : DistribMulAction Q (Additive C) := additiveDistribMulAction Q C
  exact @exists_forall_apply_sub_eq_zero_of_forall_stabilizer Q _ _ X _ (Additive C) _ _
    (Additive A ⊗[ℤ] Additive C) _ (tensorDistribMulAction Q A C)
    (tensorVal C g).toAddMonoidHom (tensorVal_smul C g hgeq) (tensorVal_surjective C g hg)
    c hc hloc

end Correct

/-! ### The class comes from the kernel of the valuation -/

section Class

variable {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable (C : Type) [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ))
variable (B : Subgroup A) [IsStableSubgroup Q B]

/-- **A class with coefficients in the tensor product whose valuation is a coboundary at every
place, on the subgroup fixing that place, comes from the tensor product of the kernel of the
valuation with the module.**  Correct the cocycle by a coboundary so that its valuation vanishes;
the corrected cocycle then takes its values in the image of the kernel, which is a submodule
because the inclusion of the kernel stays exact after tensoring, and the correction has not changed
the class. -/
theorem mem_range_map_tensorSubInclRep_of_forall_stabilizer (hg : Function.Surjective g)
    (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (c : Q → Additive A ⊗[ℤ] Additive C)
    (hcoc : c ∈ cocycles₁ (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)))
    (hloc : ∀ x : X, ∃ u : Additive C, ∀ ρ : Q, ρ • x = x →
      tensorVal C g (c ρ) x = Additive.ofMul (ρ • u.toMul) - u) :
    H1π (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)) ⟨c, hcoc⟩ ∈
      LinearMap.range (groupCohomology.map (MonoidHom.id Q)
        (A := Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C))
        (tensorSubInclRep Q C B) 1).hom := by
  have hc : ∀ σ τ : Q, c (σ * τ) = σ • c τ + c σ :=
    (mem_cocycles₁_iff (A := Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)) c).1 hcoc
  obtain ⟨t, ht⟩ := exists_tensorVal_sub_eq_zero_of_forall_stabilizer C g hg hgeq hc hloc
  have hmem : ∀ σ : Q, c σ - (σ • t - t) ∈ LinearMap.range (tensorSubIncl C B) := by
    intro σ
    rw [range_tensorSubIncl g hg hB, LinearMap.mem_ker, ← tensorVal_eq_zero_iff]
    exact Finsupp.ext fun x => ht σ x
  choose c' hc' using hmem
  have hc'coc : ∀ σ τ : Q, c' (σ * τ) = σ • c' τ + c' σ := by
    intro σ τ
    refine tensorSubIncl_injective g hg hB ?_
    simp only [map_add, tensorSubIncl_smul, hc']
    rw [hc σ τ, smul_sub, smul_sub, smul_smul]
    abel
  have hc'mem :
      c' ∈ cocycles₁ (Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C)) :=
    (mem_cocycles₁_iff (A := Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C)) c').2
      hc'coc
  refine ⟨H1π _ ⟨c', hc'mem⟩, ?_⟩
  rw [H1π_comp_map_apply, H1π_eq_iff]
  refine ⟨-t, funext fun σ => ?_⟩
  show σ • (-t) - (-t) = _
  simp only [Pi.sub_apply]
  show σ • (-t) - (-t) = tensorSubIncl C B (c' σ) - c σ
  rw [hc' σ, smul_neg]
  abel

/-- **A class with coefficients in the tensor product which is trivial on the subgroup fixing each
place comes from the tensor product of the kernel of the valuation with the module.**  This is the
form in which the everywhere locally trivial classes are carried down to coefficients in the units
of a number field for a finite set of places: the places are the primes outside the set, the
subgroup fixing a place is its decomposition group, and being everywhere locally trivial is exactly
the hypothesis. -/
theorem mem_range_map_tensorSubInclRep_of_forall_res (hg : Function.Surjective g)
    (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (c : Q → Additive A ⊗[ℤ] Additive C)
    (hcoc : c ∈ cocycles₁ (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)))
    (hres : ∀ x : X, ∃ b : Additive A ⊗[ℤ] Additive C,
      ∀ ρ : Q, ρ • x = x → c ρ = ρ • b - b) :
    H1π (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)) ⟨c, hcoc⟩ ∈
      LinearMap.range (groupCohomology.map (MonoidHom.id Q)
        (A := Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C))
        (tensorSubInclRep Q C B) 1).hom :=
  mem_range_map_tensorSubInclRep_of_forall_stabilizer C g B hg hB hgeq c hcoc
    (tensorVal_stabilizer_of_res_eq_sub C g hgeq hres)

end Class

end InverseGalois.CFT

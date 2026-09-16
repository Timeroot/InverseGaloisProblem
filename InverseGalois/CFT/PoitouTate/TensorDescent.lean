/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.TensorInvariant
import InverseGalois.CFT.PoitouTate.TensorOrbit

/-!
# Reading an obstruction at a further set of places

The obstruction to correcting a tensor to an invariant one is a class of the first cohomology with
coefficients in the kernel of the valuation it is read at.  That kernel is still a large group: over
a number field, valuing only at finitely many named places leaves the units arbitrary order
everywhere else.  The obstruction may however be read again, at a second set of places, and pushed
into the kernel of the second valuation as well; and the kernel of the second valuation is the group
of units for the union of the two sets of places, which is finitely generated as soon as the union
misses only finitely many places.

Nothing local is needed for the second reading.  The obstruction cocycle is, by construction, the
preimage of the difference between the translate of the tensor and the tensor itself, so its
valuation at a place is the difference between the translate of the valuation of the tensor and the
valuation of the tensor.  On the subgroup fixing that place the place does not move, so that
difference is a coboundary for the single element which is the valuation of the tensor there.  The
hypothesis the orbit argument makes at each place is therefore automatic, at every place at once,
and the class descends with no condition beyond surjectivity of the second valuation.

## Main results

* `InverseGalois.CFT.tensorVal_tensorSubIncl`: the valuation of the inclusion of a subgroup is the
  restriction of the valuation.
* `InverseGalois.CFT.mem_range_map_tensorSubInclRep_of_smul_sub`: **a class whose cocycle is carried
  by the inclusion of a subgroup to the obstruction to invariance of a tensor comes from the kernel
  of any second valuation of that subgroup.**
* `InverseGalois.CFT.mem_range_map_tensorSubInclRep_tensorInvariantClass`: **the obstruction class
  of a tensor whose valuation is invariant comes from the kernel of a second valuation**, whatever
  the places that second valuation is read at.

## Tags

group cohomology, permutation module, S-unit, tensor product, class group
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction TensorProduct groupCohomology

section Descent

variable {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable (C : Type) [CommGroup C] [MulDistribMulAction Q C]
variable {B : Subgroup A} [IsStableSubgroup Q B]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (G : Additive A →+ (X →₀ ℤ)) (g : Additive ↥B →+ (X →₀ ℤ))
variable (E : Subgroup ↥B) [IsStableSubgroup Q E]

omit [Finite Q] in
/-- **The valuation of the inclusion of a subgroup is the restriction of the valuation**, after
tensoring with a module. -/
theorem tensorVal_tensorSubIncl
    (hres : ∀ b : ↥B, g (Additive.ofMul b) = G (Additive.ofMul (b : A)))
    (y : Additive ↥B ⊗[ℤ] Additive C) :
    tensorVal C G (tensorSubIncl C B y) = tensorVal C g y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy']
  | tmul b w =>
    refine Finsupp.ext fun x => ?_
    have h1 : tensorVal C G (tensorSubIncl C B (b ⊗ₜ[ℤ] w)) x
        = G (Additive.ofMul ((b.toMul : ↥B) : A)) x • w :=
      tensorVal_tmul_apply C G ((b.toMul : ↥B) : A) w.toMul x
    have h2 : tensorVal C g (b ⊗ₜ[ℤ] w) x = g (Additive.ofMul b.toMul) x • w :=
      tensorVal_tmul_apply C g b.toMul w.toMul x
    rw [h1, h2, hres]

/-- **A class whose cocycle is carried by the inclusion of a subgroup to the obstruction to
invariance of a tensor comes from the kernel of any second valuation of that subgroup.**

The second valuation is asked only to be the restriction of an equivariant valuation of the
ambient group and to be surjective; no hypothesis is made on the places it is read at, and none on
the subgroups fixing them.  What makes the orbit argument go through at a place with no condition
is the shape of the cocycle: its image in the ambient group is the difference between the translate
of the tensor and the tensor, so its valuation at a place fixed by an automorphism is the difference
between the translate of the valuation of the tensor there and that valuation itself. -/
theorem mem_range_map_tensorSubInclRep_of_smul_sub
    (hres : ∀ b : ↥B, g (Additive.ofMul b) = G (Additive.ofMul (b : A)))
    (hg : Function.Surjective g)
    (hE : ∀ b : ↥B, b ∈ E ↔ g (Additive.ofMul b) = 0)
    (hGeq : ∀ (σ : Q) (a : A) (x : X),
      G (Additive.ofMul (σ • a)) x = G (Additive.ofMul a) (σ⁻¹ • x))
    {t : Additive A ⊗[ℤ] Additive C} (c : Q → Additive ↥B ⊗[ℤ] Additive C)
    (hcoc : c ∈ cocycles₁ (Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C)))
    (hct : ∀ σ : Q, tensorSubIncl C B (c σ) = σ • t - t) :
    H1π (Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C)) ⟨c, hcoc⟩ ∈
      LinearMap.range (groupCohomology.map (MonoidHom.id Q)
        (A := Rep.ofDistribMulAction ℤ Q (Additive ↥E ⊗[ℤ] Additive C))
        (tensorSubInclRep Q C E) 1).hom := by
  have hgeq : ∀ (σ : Q) (b : ↥B) (x : X),
      g (Additive.ofMul (σ • b)) x = g (Additive.ofMul b) (σ⁻¹ • x) := by
    intro σ b x
    rw [hres, hres, coe_smul_stableSubgroup, hGeq]
  refine mem_range_map_tensorSubInclRep_of_forall_stabilizer C g E hg hE hgeq c hcoc fun x => ?_
  refine ⟨tensorVal C G t x, fun ρ hρ => ?_⟩
  have hinv : ρ⁻¹ • x = x := inv_smul_eq_iff.2 hρ.symm
  rw [← tensorVal_tensorSubIncl C G g hres (c ρ), hct ρ, map_sub, Finsupp.sub_apply,
    tensorVal_smul C G hGeq, hinv]

end Descent

/-! ### The obstruction class itself -/

section Invariant

variable {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable (C : Type) [CommGroup C] [MulDistribMulAction Q C]
variable {Y : Type} [MulAction Q Y] [DecidableEq Y] (g₀ : Additive A →+ (Y →₀ ℤ))
variable (B : Subgroup A) [IsStableSubgroup Q B]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (G : Additive A →+ (X →₀ ℤ)) (g : Additive ↥B →+ (X →₀ ℤ))
variable (E : Subgroup ↥B) [IsStableSubgroup Q E]

omit [MulAction Q Y] in
/-- **The obstruction class of a tensor whose valuation is invariant comes from the kernel of a
second valuation**, whatever the places that second valuation is read at.

The first valuation is the one the tensor is prescribed at, and the coefficients of the obstruction
are the elements having no order there.  Valuing those again, at any further set of places, cuts the
coefficients down to the elements having no order at either set, and the class is still carried by
the inclusion.  Over a number field the two readings together leave only finitely many places, so
the coefficients are finitely generated and the class may be counted. -/
theorem mem_range_map_tensorSubInclRep_tensorInvariantClass
    (hres : ∀ b : ↥B, g (Additive.ofMul b) = G (Additive.ofMul (b : A)))
    (hg : Function.Surjective g)
    (hE : ∀ b : ↥B, b ∈ E ↔ g (Additive.ofMul b) = 0)
    (hGeq : ∀ (σ : Q) (a : A) (x : X),
      G (Additive.ofMul (σ • a)) x = G (Additive.ofMul a) (σ⁻¹ • x))
    (hg₀ : Function.Surjective g₀) (hB : ∀ a : A, a ∈ B ↔ g₀ (Additive.ofMul a) = 0)
    {t : Additive A ⊗[ℤ] Additive C}
    (ht : ∀ σ : Q, tensorVal C g₀ (σ • t) = tensorVal C g₀ t) :
    tensorInvariantClass C g₀ B hg₀ hB ht ∈
      LinearMap.range (groupCohomology.map (MonoidHom.id Q)
        (A := Rep.ofDistribMulAction ℤ Q (Additive ↥E ⊗[ℤ] Additive C))
        (tensorSubInclRep Q C E) 1).hom :=
  mem_range_map_tensorSubInclRep_of_smul_sub C G g E hres hg hE hGeq _
    (mem_cocycles₁_tensorInvariantCocycle C g₀ B hg₀ hB ht)
    (tensorSubIncl_tensorInvariantCocycle C g₀ B hg₀ hB ht)

end Invariant

end InverseGalois.CFT

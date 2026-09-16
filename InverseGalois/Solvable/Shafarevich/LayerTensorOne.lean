/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.TensorKill
import InverseGalois.Solvable.Shafarevich.LayerSmooth

/-!
# The count in degree one, against coefficients tensored with a finitely generated group

The ladder that climbs the generic group needs its counting argument in degree one as well as in
degree two, and there the coefficients are not a layer but a layer tensored with a finitely
generated abelian group on the left.  Such a tensor product is not finite, so the count cannot be
run against all of its elements; but a spanning family of the left factor writes every element of
the tensor product as a combination of the members of that family against coefficients in the right
factor alone, and there are only finitely many members.  A cochain on a finite group with values in
the tensor product therefore has finitely many coordinates in the right factor, and killing all of
them kills the cochain.

The right factor is not itself a layer either: it is whatever group the coefficients of the ladder
are built from, and the map applied to it is whatever map the shrinking induces.  So the count is
stated against an abstract right factor with an abstract family of induced maps, subject to the one
demand a shrinking can meet — that finitely many prescribed elements of the layer being read
through the map determine whether the induced map kills an element.  That keeps the statement free
of the actions carried by the coefficients of the ladder, which are quotients of the actions of an
infinite Galois group and do not agree definitionally with the ones a layer carries by itself.

## Main results

* `InverseGalois.Shafarevich.exists_genericShrink_map_h1_eq_zero`: **one first cohomology class of a
  finite group, with coefficients a finitely generated abelian group tensored with an abstract
  group, is annihilated by a surjective shrinking onto the intended rank.**

## Tags

group cohomology, tensor product, spanning family, shrinking, counting argument
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.Shafarevich

open CategoryTheory InverseGalois.CFT groupCohomology TensorProduct

/-! ### The count in degree one -/

section Count

variable (U : Type) [Group U] [Finite U] (r n : ℕ) (S : Type) [Group S] [Finite S]

omit [Group U] in
/-- **A shrinking homomorphism can be chosen surjective and annihilating the class of a prescribed
one cocycle with values in a tensor product**, the left factor being spanned by finitely many
elements and the map of the right factor being cut out by finitely many readings in the layer.  The
cocycle has one value at each element of the finite group, each value has one coordinate against
each member of the spanning family, and each coordinate has finitely many readings, so the count is
run against a finite index set and the bound is the one the layer already answers. -/
theorem exists_genericShrink_map_h1π_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j : ℕ} {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
    {C C' : Type} [CommGroup C] [CommGroup C'] [MulDistribMulAction Q C]
    [MulDistribMulAction Q C'] {d : ℕ} (b : Fin d → Additive A)
    (hb : Submodule.span ℤ (Set.range b) = ⊤) {ι : Type} [Finite ι]
    (coord : C → ι → ↥(layerSub ℓ (Generic U (r * n) S) j)) (Φ : (Fin r → ℕ) → C →* C')
    (hΦ : ∀ (a : Fin r → ℕ) (σ : Q) (w : C), Φ a (σ • w) = σ • Φ a w)
    (hkill : ∀ (a : Fin r → ℕ) (w : C),
      (∀ t, layerSubMap ℓ (genericShrink U r n S a) j (coord w t) = 1) → Φ a w = 1)
    (hr : (j + 1) * (Nat.card (Q × Fin d × ι) *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r)
    (c : Q → Additive A ⊗[ℤ] Additive C)
    (hcoc : c ∈ cocycles₁ (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C))) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q (Φ a) (hΦ a)) 1).hom
        (H1π (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)) ⟨c, hcoc⟩) = 0 := by
  choose v hv using fun q => exists_sum_tmul_of_span b hb (c q)
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_layerSubMap_eq_one U r n S hS hr
    fun ν : Q × Fin d × ι => coord (v ν.1 ν.2.1).toMul ν.2.2
  refine ⟨a, hsurj, ?_⟩
  have hzero : ∀ q, tensorCoeff A (Φ a) (c q) = 0 := by
    intro q
    rw [hv q, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : Φ a (v q i).toMul = 1 := hkill a _ fun t => ha (q, i, t)
    show b i ⊗ₜ[ℤ] Additive.ofMul (Φ a (v q i).toMul) = 0
    rw [h1]
    exact TensorProduct.tmul_zero _ _
  have hmap : mapCocycles₁ (MonoidHom.id Q) (tensorCoeffRep (A := A) Q (Φ a) (hΦ a))
      (⟨c, hcoc⟩ : cocycles₁ (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)))
      = 0 := Subtype.ext (funext hzero)
  rw [H1π_comp_map_apply, hmap]
  exact map_zero _

omit [Group U] in
/-- **A shrinking homomorphism can be chosen surjective and annihilating a prescribed first
cohomology class with values in a tensor product** whose left factor is spanned by finitely many
elements.  Every class is the class of a cocycle, and the reading of the map of the coefficients on
cohomology is the reading on cocycles. -/
theorem exists_genericShrink_map_h1_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j : ℕ} {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
    {C C' : Type} [CommGroup C] [CommGroup C'] [MulDistribMulAction Q C]
    [MulDistribMulAction Q C'] {d : ℕ} (b : Fin d → Additive A)
    (hb : Submodule.span ℤ (Set.range b) = ⊤) {ι : Type} [Finite ι]
    (coord : C → ι → ↥(layerSub ℓ (Generic U (r * n) S) j)) (Φ : (Fin r → ℕ) → C →* C')
    (hΦ : ∀ (a : Fin r → ℕ) (σ : Q) (w : C), Φ a (σ • w) = σ • Φ a w)
    (hkill : ∀ (a : Fin r → ℕ) (w : C),
      (∀ t, layerSubMap ℓ (genericShrink U r n S a) j (coord w t) = 1) → Φ a w = 1)
    (hr : (j + 1) * (Nat.card (Q × Fin d × ι) *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r)
    (w : H1 (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C))) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q (Φ a) (hΦ a)) 1).hom w
        = 0 := by
  induction w using H1_induction_on with
  | @h z =>
    exact exists_genericShrink_map_h1π_eq_zero U r n S hS b hb coord Φ hΦ hkill hr _ z.2

end Count

end InverseGalois.Shafarevich

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.TotallyRealInvariant

/-!
# The archimedean invariants over an arbitrary base

An infinite place of a number field is real or complex.  At a complex place the completion is
algebraically closed and splits everything, so the invariant there is trivial for any class at all.
At a real place the completion is the reals along the associated embedding, and a class split by
some extension is split there as soon as that extension admits a compatible embedding into the
reals.

A totally real extension always admits one.  Compose the real embedding of the base with the
inclusion of the reals into the complex numbers, extend the result to the extension using that the
complex numbers are algebraically closed, and observe that the extension being totally real forces
the extended embedding to be fixed by conjugation, hence to land in the reals.  The two embeddings
agree on the base because the inclusion of the reals into the complex numbers is injective.

Consequently a Brauer class of an arbitrary number field split by a totally real extension has
trivial invariant at every infinite place, and its total invariant is the product of the invariants
at the finite places alone.  This is the archimedean half of the reciprocity computation over an
arbitrary base, replacing the argument over the rationals which used that the rationals have a
single infinite place.

## Main results

* `InverseGalois.CFT.infinitePlaceInvariant_eq_one_of_isTotallyReal`: **a Brauer class of a number
  field split by a totally real extension has trivial invariant at every infinite place.**
* `InverseGalois.CFT.totalInvariant_eq_finprod_of_isTotallyReal`: **the total invariant of such a
  class is the product of its invariants at the finite places.**
* `InverseGalois.CFT.totalInvariant_cyclicBrauerHom_of_isTotallyReal`: the same for a cyclic
  algebra over an arbitrary number field with a totally real splitting field.

## Tags

Brauer group, invariant, infinite place, totally real, number field, cyclic algebra, reciprocity,
class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### A real embedding of a totally real extension -/

section RealEmbedding

variable {k F : Type} [Field k] [NumberField k] [Field F] [NumberField F] [Algebra k F]
  [IsTotallyReal F]

/-- **A totally real extension of a number field embeds into the reals over any real embedding of
the base.**  Extend the composite of the real embedding with the inclusion of the reals into the
complex numbers along the algebraically closed target; the extension is totally real, so the
extended embedding is fixed by conjugation and factors through the reals, and the factorisation
agrees with the given embedding on the base because the reals inject into the complex numbers. -/
theorem nonempty_algHom_real_of_isTotallyReal [Algebra k ℝ] : Nonempty (F →ₐ[k] ℝ) := by
  letI : Algebra k ℂ := (Complex.ofRealHom.comp (algebraMap k ℝ)).toAlgebra
  let φ : F →ₐ[k] ℂ := IsAlgClosed.lift
  have hφreal : ComplexEmbedding.IsReal (φ : F →+* ℂ) := IsTotallyReal.complexEmbedding_isReal _
  have hcomm : ∀ r : k, hφreal.embedding (algebraMap k F r) = algebraMap k ℝ r := by
    intro r
    apply Complex.ofReal_injective
    rw [ComplexEmbedding.IsReal.coe_embedding_apply]
    show φ (algebraMap k F r) = _
    rw [φ.commutes]
    rfl
  exact ⟨{ hφreal.embedding with commutes' := hcomm }⟩

end RealEmbedding

/-! ### Triviality of the archimedean invariants -/

section Archimedean

variable {k F : Type} [Field k] [NumberField k] [Field F] [NumberField F] [Algebra k F]
  [IsTotallyReal F]

/-- **A Brauer class of a number field split by a totally real extension has trivial invariant at
every infinite place.**  At a complex place every class is split, and at a real place the totally
real extension embeds into the reals over the associated embedding of the base. -/
theorem infinitePlaceInvariant_eq_one_of_isTotallyReal (u : InfinitePlace k)
    {x : BrauerGroup.{0, 0} k} (hx : x ∈ BrauerGroup.relative k F) :
    infinitePlaceInvariant k u x = 1 := by
  rcases u.isReal_or_isComplex with hu | hu
  · letI : Algebra k ℝ := (InfinitePlace.embedding_of_isReal hu).toAlgebra
    rw [infinitePlaceInvariant_eq_one_iff, relative_completion_eq_relative_real k hu rfl]
    obtain ⟨ψ⟩ : Nonempty (F →ₐ[k] ℝ) := nonempty_algHom_real_of_isTotallyReal
    exact relative_le_relative_of_algHom ψ hx
  · rw [infinitePlaceInvariant_of_isComplex k hu, MonoidHom.one_apply]

/-- **The total invariant of a Brauer class split by a totally real extension is the product of its
invariants at the finite places.** -/
theorem totalInvariant_eq_finprod_of_isTotallyReal {x : BrauerGroup.{0, 0} k}
    (hx : x ∈ BrauerGroup.relative k F) :
    totalInvariant k x = ∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v x :=
  totalInvariant_eq_finprod k x fun u => infinitePlaceInvariant_eq_one_of_isTotallyReal u hx

end Archimedean

/-! ### Cyclic algebras with a totally real splitting field -/

section Cyclic

variable {k F : Type} [Field k] [NumberField k] [Field F] [NumberField F] [Algebra k F]
  [IsGalois k F] [IsTotallyReal F] {σ₀ : Gal(F/k)}
  (hσ₀ : ∀ x : Gal(F/k), x ∈ Subgroup.zpowers σ₀)

/-- **A cyclic algebra over a number field with a totally real splitting field has trivial invariant
at every infinite place.** -/
theorem infinitePlaceInvariant_cyclicBrauerHom_of_isTotallyReal (a : kˣ) (u : InfinitePlace k) :
    infinitePlaceInvariant k u (cyclicBrauerHom hσ₀ a) = 1 :=
  infinitePlaceInvariant_eq_one_of_isTotallyReal u (cyclicBrauerHom_mem_relative hσ₀ a)

/-- **The total invariant of a cyclic algebra over a number field with a totally real splitting
field is the product of its invariants at the finite places.**  This is the archimedean half of the
reciprocity computation for such an algebra over an arbitrary base. -/
theorem totalInvariant_cyclicBrauerHom_of_isTotallyReal (a : kˣ) :
    totalInvariant k (cyclicBrauerHom hσ₀ a)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 k), placeInvariant k v (cyclicBrauerHom hσ₀ a) :=
  totalInvariant_eq_finprod_of_isTotallyReal (cyclicBrauerHom_mem_relative hσ₀ a)

end Cyclic

end InverseGalois.CFT

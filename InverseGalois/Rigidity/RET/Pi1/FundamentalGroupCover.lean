/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.FundamentalGroup
import InverseGalois.Rigidity.RET.Pi1.CoverCompletion

/-!
# The Riemann Existence Theorem in fundamental-group language

Combining the covers correspondence in profinite-completion language
(`isGeometricGaloisCover_iff_completion`) with the identification of the profinite completion of the
sphere group as the automorphism group of the fibre functor
(`sphereCompletion_mulEquiv_aut`, a *homeomorphism* of profinite groups), the Riemann Existence
Theorem reads directly in terms of Mathlib's own Galois-category fundamental group:

> A finite group `G` is realized by a geometric Galois cover of `ℙ¹_ℚ̄` **iff** it is a continuous
> quotient of the tame fundamental group `Aut (sphereFiber r)` — the automorphism group of the fibre
> functor of the Galois category of finite `SphereGroup r`-sets — for some number of branch points
> `r`.

The two sides live in different universes (`sphereCompletion r` is a `ProfiniteGrp.{0}` object while
`Aut (sphereFiber r)` lands one universe up), so the quotient map is phrased as a universe-
heterogeneous `ContinuousMonoidHom` rather than a morphism in a single `ProfiniteGrp` universe.

## Main results

* `isGeometricGaloisCover_iff_aut` — `IsGeometricGaloisCover G` iff `G` is a continuous quotient of
  `Aut (sphereFiber r)` for some `r`.
-/

namespace Rigidity.RET

open CategoryTheory PreGaloisCategory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion
open scoped CategoryTheory.PreGaloisCategory

variable {G : Type} [Group G] [Finite G]

/-- **The Riemann Existence Theorem, in fundamental-group language.**  A finite group `G` is realized
by a geometric Galois cover of `ℙ¹_ℚ̄` iff it is a continuous quotient of the tame fundamental group
`Aut (sphereFiber r)` — the automorphism group of the fibre functor of the Galois category of finite
`SphereGroup r`-sets — for some number of branch points `r`.

This transfers `isGeometricGaloisCover_iff_completion` across the fundamental-group identification
`sphereCompletion_mulEquiv_aut : sphereCompletion r ≃* Aut (sphereFiber r)`, which is a homeomorphism
of profinite groups (`cmhSphereToAut` / `cmhAutToSphere` are the two continuous directions). -/
theorem isGeometricGaloisCover_iff_aut :
    IsGeometricGaloisCover G ↔
      ∃ (r : ℕ) (φ : ContinuousMonoidHom (Aut (sphereFiber.{0} r))
          (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of G))),
        Function.Surjective φ := by
  rw [isGeometricGaloisCover_iff_completion]
  constructor
  · rintro ⟨r, f, hf⟩
    refine ⟨r, f.hom.comp cmhAutToSphere, ?_⟩
    rw [ContinuousMonoidHom.coe_comp]
    exact hf.comp cmhAutToSphere_surjective
  · rintro ⟨r, φ, hφs⟩
    refine ⟨r, ConcreteCategory.ofHom (φ.comp cmhSphereToAut), ?_⟩
    show Function.Surjective ⇑(ConcreteCategory.ofHom (φ.comp cmhSphereToAut)
      : sphereCompletion r ⟶ _)
    rw [show ⇑(ConcreteCategory.ofHom (φ.comp cmhSphereToAut)
        : sphereCompletion r ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of G))
        = ⇑(φ.comp cmhSphereToAut) from rfl, ContinuousMonoidHom.coe_comp]
    exact hφs.comp cmhSphereToAut_surjective

end Rigidity.RET

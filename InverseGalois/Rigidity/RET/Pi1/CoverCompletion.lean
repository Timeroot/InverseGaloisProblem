/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Existence
import InverseGalois.Rigidity.RET.ExistenceCovers
import InverseGalois.Rigidity.RET.Pi1.SphereCompletion

/-!
# The Riemann Existence Theorem in profinite fundamental-group language

The covers correspondence (`riemann_existence_cover`, `RET.Existence`) states that a finite group
`G` is realized by a geometric Galois cover of `ℙ¹_ℚ̄` iff it is a quotient of some sphere group
`SphereGroup r`.  Composed with the finite-quotient dictionary of `Pi1.SphereCompletion`, this reads
directly in the language of the **profinite tame fundamental group** `sphereCompletion r`:

> `G` is a geometric Galois cover of `ℙ¹_ℚ̄` **iff** `G` is a finite continuous quotient of the
> profinite tame fundamental group `sphereCompletion r` for some `r`.

This is the incarnation of the Riemann Existence Theorem that an étale-`π₁` development targets: the
geometric covers of the `r`-punctured line are the finite continuous quotients of `π̂₁`, and `π̂₁` is
the profinite completion of the sphere presentation group.

## Main results

* `isGeometricGaloisCover_iff_completion` — `IsGeometricGaloisCover G` iff `G` is a finite continuous
  quotient of `sphereCompletion r` for some `r`.
-/

namespace Rigidity.RET

open ProfiniteGrp CategoryTheory

variable {G : Type} [Group G] [Finite G]

/-- **The Riemann Existence Theorem, in profinite fundamental-group language.**  A finite group `G`
is realized by a geometric Galois cover of `ℙ¹_ℚ̄` iff `G` is a finite continuous quotient of the
profinite tame fundamental group `sphereCompletion r` of the `r`-punctured line, for some number of
branch points `r`.

The covers correspondence supplies the equivalence with a discrete sphere-group quotient
(`riemann_existence_cover`), and the finite-quotient dictionary
(`exists_surjective_completion_iff_discrete`) identifies that with a continuous quotient of the
profinite completion. -/
theorem isGeometricGaloisCover_iff_completion :
    IsGeometricGaloisCover G ↔
      ∃ (r : ℕ) (f : sphereCompletion r ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of G)),
        Function.Surjective (f : sphereCompletion r → _) := by
  rw [riemann_existence_cover]
  exact (exists_congr fun _ => exists_surjective_completion_iff_discrete).symm

end Rigidity.RET

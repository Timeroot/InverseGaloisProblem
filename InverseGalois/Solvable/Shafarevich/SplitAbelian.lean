/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.Reduction
import InverseGalois.Solvable.Wreath
import InverseGalois.Rigidity.RET.Wreath.Main
import InverseGalois.Rigidity.RET.Specialization

/-!
# Split embedding problems with abelian kernel

A *split embedding problem* over `ℚ` asks, given a finite group `U` realized as a Galois group and
an action `φ : U →* MulAut H` of it on a finite group `H`, for a realization of the semidirect
product `H ⋊[φ] U`.  When the kernel `H` is **abelian** the problem is unconditionally solvable, and
solvable regularly: the semidirect product is a quotient of the regular wreath product `H ≀ᵣ U`,
whose realizability was established by the Dentzer–Stoll construction and does not depend on `φ`.

Recorded here because it is exactly the near-miss for Shafarevich's theorem.  Ore's reduction
(`Shafarevich.isInverseGalois_of_isSolvable_of_splitNilpotentEP`) shows that all finite solvable
groups would follow from split embedding problems with **nilpotent** kernel, and the abelian case is
the first step of any filtration of a nilpotent kernel.  The two do not meet: filtering a nilpotent
`H` by, say, its centre or its commutator subgroup turns one split problem into a split problem with
abelian kernel *and* a residual problem that is no longer split, and it is that non-split lifting
which needs class field theory.  The class of groups reached by the abelian case alone is precisely
Dentzer's class of semiabelian groups.

The hypothesis on `U` is *regular* realizability, which is what the wreath construction consumes;
a bare realization of `U` over `ℚ` is not enough to run it.

## Main results

* `Shafarevich.splitAbelianEP_regular` — a split embedding problem with finite abelian kernel over a
  regularly realizable group is solvable regularly over `ℚ(T)`.
* `Shafarevich.splitAbelianEP_of_regular` — the same, read over `ℚ`.
-/

namespace Shafarevich

/-- **A split embedding problem with finite abelian kernel is solvable regularly over `ℚ(T)`.**

The semidirect product `A ⋊[φ] U` is a quotient of the regular wreath product `A ≀ᵣ U`, uniformly in
the action `φ`, and the wreath product is regularly realizable as soon as `U` is. -/
theorem splitAbelianEP_regular (A U : Type) [CommGroup A] [Finite A] [Group U] [Finite U]
    (φ : U →* MulAut A) (hU : IsRegularInverseGalois U) : IsRegularInverseGalois (A ⋊[φ] U) :=
  IsRegularInverseGalois.semidirectProduct_of_wreath φ (IsRegularInverseGalois.wreath A U hU)

/-- **Every split embedding problem over `ℚ` with abelian kernel is solvable.**

A realization of `U` over `ℚ` need not be regular, so the statement is obtained by realizing the
larger group `A ⋊[φ] U` regularly whenever it is regularly realizable; the finite abelian group `A`
and the action `φ` play no role beyond providing the wreath product. -/
theorem splitAbelianEP_of_regular (A U : Type) [CommGroup A] [Finite A] [Group U] [Finite U]
    (φ : U →* MulAut A) (hU : IsRegularInverseGalois U) : IsInverseGalois (A ⋊[φ] U) :=
  IsRegularInverseGalois.isInverseGalois (splitAbelianEP_regular A U φ hU)

end Shafarevich

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.Induction
import InverseGalois.CFT.Scholz.StrongScholz

/-!
# The dyadic Scholz–Reichardt induction

At an odd prime the Scholz–Reichardt construction climbs the order of the group one central step at
a time, and the residue correction is available at every step.  At the prime two it is not: the
correction can only reach the Frobenius defects orthogonal to the square classes of the field being
corrected, and the induction has to be organised so that the defect is orthogonal by construction.

That is done by climbing the `2`-class rather than the order, and by realising not an arbitrary
group but the free object of a given rank and `2`-class, carrying with it the blocks of primes that
account for its square classes.  The step that raises the class by one is isolated here as a single
named property, and the rest of the induction is carried out from it: the free object of class zero
is the trivial group, realised by `ℚ`, and the free object of class one is the multiquadratic base.
Granted the step, every free object is realised, and hence — the free objects being universal for
rank and `2`-class — so is every finite `2`-group.

## Main definitions

* `InverseGalois.CFT.IsDyadicClassStepSolvable`: the class-raising step of the induction.

## Main results

* `InverseGalois.CFT.isStrongScholzRealizable_of_isDyadicClassStepSolvable`: granted the step, the
  free object of every rank and every `2`-class is realised at every level.
* `InverseGalois.CFT.isScholzRealizable_of_isDyadicClassStepSolvable`: **granted the step, every
  finite `2`-group is realised by a field satisfying Serre's condition, at every level.**
* `InverseGalois.CFT.isInverseGalois_of_isDyadicClassStepSolvable`: **granted the step, every
  finite `2`-group is a Galois group over `ℚ`.**

## Tags

Scholz–Reichardt, `2`-group, `2`-class, free object, strong Scholz field
-/

namespace InverseGalois.CFT

/-! ### The class-raising step -/

/-- **The class-raising step of the dyadic Scholz–Reichardt induction.**  Whenever the free object
of every rank and `2`-class `c` admits a strong Scholz realization at every level, the free object
of rank `d` and `2`-class `c + 1` admits one at level `N`.  The step is allowed to consume
realizations of arbitrarily large rank, which is what the shrinking process needs, and to spend as
many levels as it likes, which is what the iterated correction needs. -/
def IsDyadicClassStepSolvable : Prop :=
  ∀ (c d N : ℕ), (∀ δ M, IsStrongScholzRealizable δ c M) → IsStrongScholzRealizable d (c + 1) N

/-! ### The induction on the `2`-class -/

/-- **Granted the class-raising step, the free object of every rank and every `2`-class admits a
strong Scholz realization at every level.**  The free object of class zero is trivial and is
realised by `ℚ`; the step supplies each higher class from the one below it, at every rank and every
level at once. -/
theorem isStrongScholzRealizable_of_isDyadicClassStepSolvable (h : IsDyadicClassStepSolvable) :
    ∀ c d N, IsStrongScholzRealizable d c N := by
  intro c
  induction c with
  | zero => exact isStrongScholzRealizable_zero
  | succ c ih => exact fun d N => h c d N fun δ M => ih δ M

/-- **Granted the class-raising step, every finite `2`-group is realised by a field satisfying
Serre's condition**, at every level. -/
theorem isScholzRealizable_of_isDyadicClassStepSolvable (h : IsDyadicClassStepSolvable) (N : ℕ)
    (G : Type) [Group G] [Finite G] (hG : IsPGroup 2 G) : IsScholzRealizable G 2 N :=
  isScholzRealizable_of_forall_isStrongScholzRealizable N
    (fun d c => isStrongScholzRealizable_of_isDyadicClassStepSolvable h c d N) G hG

/-- **Granted the class-raising step, every finite `2`-group is a Galois group over `ℚ`.** -/
theorem isInverseGalois_of_isDyadicClassStepSolvable (h : IsDyadicClassStepSolvable) (G : Type)
    [Group G] [Finite G] (hG : IsPGroup 2 G) : IsInverseGalois G :=
  (isScholzRealizable_of_isDyadicClassStepSolvable h 1 G hG).isInverseGalois

end InverseGalois.CFT

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The norm subgroup of a finite extension

For a finite extension `L / K` the field norm carries units to units, and its image is a subgroup
of `Kˣ`.  This subgroup is the common answer of two otherwise unrelated computations: it is the
kernel of the cyclic algebra construction, so that the relative Brauer group of a cyclic extension
is `Kˣ / N Lˣ`; and it is the group of units killed in the zeroth Tate group of `Lˣ`, so that this
Tate group is again `Kˣ / N Lˣ`.  Both towers therefore refer to the definition given here.

## Main definitions

* `InverseGalois.CFT.normSubgroup`: the image of `Lˣ` in `Kˣ` under the field norm.

## Main results

* `InverseGalois.CFT.mem_normSubgroup_iff`: a unit lies in the norm subgroup exactly when it is the
  norm of a unit of the extension.

## Tags

norm, norm subgroup, field extension
-/

namespace InverseGalois.CFT

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The norm subgroup.**  The image of `Lˣ` in `Kˣ` under the field norm of `L / K`. -/
noncomputable def normSubgroup (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  (Units.map (Algebra.norm K : L →* K)).range

/-- A unit of `K` lies in the norm subgroup exactly when it is the norm of a unit of `L`. -/
theorem mem_normSubgroup_iff (a : Kˣ) :
    a ∈ normSubgroup K L ↔ ∃ b : Lˣ, Algebra.norm K (b : L) = (a : K) := by
  simp only [normSubgroup, MonoidHom.mem_range, Units.ext_iff, Units.coe_map]

end InverseGalois.CFT

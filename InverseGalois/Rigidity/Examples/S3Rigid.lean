/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.Symmetric

/-!
# Sanity certificate: `S₃ = Equiv.Perm (Fin 3)` is rigid

This file fires the rigidity criterion end-to-end on the smallest example:

```
theorem s3_isRegularInverseGalois : IsRegularInverseGalois (Equiv.Perm (Fin 3)) :=
  s3Cert.isRegularInverseGalois
```

The certificate is the `n = 3` case of the rigid triple of `Sₙ`
(`InverseGalois.Rigidity.Symmetric`): a transposition, an `(n-1)`-cycle and an `n`-cycle.  For
`n = 3` the middle class is again a transposition class — cutting one letter out of a `3`-cycle
leaves a transposition — so the triple is the classical one for `S₃`, two transposition classes and
one `3`-cycle class, with exactly `6 = |S₃|` product-one generating tuples.

## Main results

* `Rigidity.S3Example.s3Cert` — the rigidity certificate for `S₃`.
* `Rigidity.S3Example.s3_isRegularInverseGalois` — `IsRegularInverseGalois (Equiv.Perm (Fin 3))`.
* `Rigidity.S3Example.s3_isInverseGalois` — `IsInverseGalois (Equiv.Perm (Fin 3))`.
-/

open Equiv Equiv.Perm

namespace Rigidity

namespace S3Example

/-- `S₃`, realized as `Equiv.Perm (Fin 3)`. -/
abbrev S3 := Equiv.Perm (Fin 3)

/-- The rigidity certificate for `S₃`: the `n = 3` case of the rigid triple of `Sₙ`. -/
def s3Cert : RigidityCertificate S3 := snCert 3 (by norm_num)

/-- For `n = 3` the middle class of the rigid triple is again a transposition class: cutting one
letter out of a `3`-cycle leaves a transposition. -/
theorem isSwap_stdTriple_one : (stdTriple (finRotate 3) (0 : Fin 3) 1).IsSwap := by
  refine isSwap_iff_cycleType.mpr ?_
  show (Equiv.swap 0 (finRotate 3 0) * finRotate 3).cycleType = {2}
  rw [cycleType_cut (isFullCycle_finRotate (by norm_num)) (by simp) 0]
  simp

/-- **`S₃` is a regular Galois group over `ℚ(T)`**, via the rigidity criterion applied to the
concrete certificate `s3Cert`. -/
theorem s3_isRegularInverseGalois : IsRegularInverseGalois (Equiv.Perm (Fin 3)) :=
  s3Cert.isRegularInverseGalois

/-- **`S₃` is an inverse Galois group over `ℚ`**, by Hilbert specialization of the regular
extension `s3_isRegularInverseGalois`. -/
theorem s3_isInverseGalois : IsInverseGalois (Equiv.Perm (Fin 3)) :=
  s3_isRegularInverseGalois.isInverseGalois

end S3Example

end Rigidity

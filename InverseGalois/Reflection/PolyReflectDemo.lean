/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Reflection.PolyReflect

/-!

This file demonstrates the `PolyReflect` engine on several polynomial identities in four
variables over an arbitrary commutative ring, including products that get expanded.

The statements use `Int.cast` coefficients (`((n : ℤ) : L)`): keeping coefficients in
`Int.cast` form lets the `RE.eval` bridge close without the per-coefficient
`Int.cast_ofNat` renormalisation that a generic `[CommRing L]` would otherwise require.

The examples are retained directly as Lean expressions. -/

open PolyReflect RE

namespace PolyReflectDemo

/- Warm-up: a binomial square is expanded. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem demo_sq {L : Type*} [CommRing L] (v0 v1 v2 v3 : L) :
    ((v0 + v1) ^ 2) =
      (((v0 ^ 2) + ((((2 : ℤ) : L) * v0) * v1)) + (v1 ^ 2)) := by
  have e := eval_eq_of_toNF (fun i ↦ [v0,v1,v2,v3].getD i 0)
    (.pow (.add (.atom 0) (.atom 1)) 2)
    (.add (.add (.pow (.atom 0) 2) (.mul (.mul (.lit 2) (.atom 0)) (.atom 1))) (.pow (.atom 1) 2))
    (by native_decide)
  simpa [RE.eval] using e

/- Warm-up: commutativity of a product (both sides are products). -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem demo_prod_comm {L : Type*} [CommRing L] (v0 v1 v2 v3 : L) :
    ((v0 + v1) * (v2 + v3)) =
      ((v2 + v3) * (v0 + v1)) := by
  have e := eval_eq_of_toNF (fun i ↦ [v0,v1,v2,v3].getD i 0)
    (.mul (.add (.atom 0) (.atom 1)) (.add (.atom 2) (.atom 3)))
    (.mul (.add (.atom 2) (.atom 3)) (.add (.atom 0) (.atom 1)))
    (by native_decide)
  simpa [RE.eval] using e

/- Warm-up: a trinomial square is expanded. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem demo_distrib {L : Type*} [CommRing L] (v0 v1 v2 v3 : L) :
    (((v0 + v1) + v2) * ((v0 + v1) + v2)) =
      ((((((v0 ^ 2) + (v1 ^ 2)) + (v2 ^ 2)) + ((((2 : ℤ) : L) * v0) * v1)) + ((((2 : ℤ) : L) * v0) * v2)) + ((((2 : ℤ) : L) * v1) * v2)) := by
  have e := eval_eq_of_toNF (fun i ↦ [v0,v1,v2,v3].getD i 0)
    (.mul (.add (.add (.atom 0) (.atom 1)) (.atom 2)) (.add (.add (.atom 0) (.atom 1)) (.atom 2)))
    (.add (.add (.add (.add (.add (.pow (.atom 0) 2) (.pow (.atom 1) 2)) (.pow (.atom 2) 2))
      (.mul (.mul (.lit 2) (.atom 0)) (.atom 1))) (.mul (.mul (.lit 2) (.atom 0)) (.atom 2)))
      (.mul (.mul (.lit 2) (.atom 1)) (.atom 2)))
    (by native_decide)
  simpa [RE.eval] using e

/- A degree-8 product identity: the same four squared binomials in a different order.
   `native_decide` expands and compares both normal forms. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem demo_deg8 {L : Type*} [CommRing L] (v0 v1 v2 v3 : L) :
    (((((v0 + v1) ^ 2) * ((v0 + v2) ^ 2)) * ((v1 + v3) ^ 2)) * ((v2 + v3) ^ 2)) =
      (((((v0 + v2) ^ 2) * ((v2 + v3) ^ 2)) * ((v0 + v1) ^ 2)) * ((v1 + v3) ^ 2)) := by
  have e := eval_eq_of_toNF (fun i ↦ [v0,v1,v2,v3].getD i 0)
    (.mul (.mul (.mul (.pow (.add (.atom 0) (.atom 1)) 2) (.pow (.add (.atom 0) (.atom 2)) 2))
      (.pow (.add (.atom 1) (.atom 3)) 2)) (.pow (.add (.atom 2) (.atom 3)) 2))
    (.mul (.mul (.mul (.pow (.add (.atom 0) (.atom 2)) 2) (.pow (.add (.atom 2) (.atom 3)) 2))
      (.pow (.add (.atom 0) (.atom 1)) 2)) (.pow (.add (.atom 1) (.atom 3)) 2))
    (by native_decide)
  simpa [RE.eval] using e

end PolyReflectDemo

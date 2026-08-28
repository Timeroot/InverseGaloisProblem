/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNTorsion
import InverseGalois.CFT.GroupCohomology.IndexTwo

/-!
# Twisting a two-cocycle does not disturb the local conditions

Correcting a two-cocycle by the coboundary of a one-cochain changes nothing locally: the embedding
of the units of a number field into the units of a completion is equivariant for the decomposition
group, so it carries the coboundary of a one-cochain to the coboundary of a one-cochain.  A cocycle
which is locally a coboundary at a finite place therefore stays locally a coboundary at that place
after any twist.

## Main results

* `InverseGalois.CFT.exists_sub_add_eq_adicUnits_coboundary₂`: the coboundary of a one-cochain is
  locally a coboundary at every finite place.
* `InverseGalois.CFT.exists_sub_add_eq_adicUnits_twist`: **a two-cochain which is locally a
  coboundary at a finite place remains so after twisting by the coboundary of a one-cochain.**

## Tags

number field, completion, decomposition group, two-cocycle, coboundary, twist
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K]

/-- **The coboundary of a one-cochain is locally a coboundary at every finite place**, the
one-cochain of local units being the image of the given one. -/
theorem exists_sub_add_eq_adicUnits_coboundary₂ (v : HeightOneSpectrum (𝓞 K))
    (u : Gal(K/k) → Kˣ) :
    ∃ d : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (coboundary₂ u (s.1, t.1)))
          = smulUnitsAut s (d t) - d (s * t) + d s := by
  refine ⟨fun s => Additive.ofMul (adicUnitHom v (u s.1)), fun s t => ?_⟩
  have hs := smulUnitsAut_adicUnitHom (k := k) v s (Additive.ofMul (u t.1))
  have hg : (globalUnitsAut (k := k) s.1 (Additive.ofMul (u t.1))).toMul = s.1 • u t.1 :=
    Units.ext rfl
  rw [toMul_ofMul, hg] at hs
  rw [hs, coboundary₂_apply, map_mul, map_div]
  show Additive.ofMul (adicUnitHom v (s.1 • u t.1) / adicUnitHom v (u (s.1 * t.1))
      * adicUnitHom v (u s.1))
    = Additive.ofMul (adicUnitHom v (s.1 • u t.1)) - Additive.ofMul (adicUnitHom v (u (s * t).1))
      + Additive.ofMul (adicUnitHom v (u s.1))
  rw [ofMul_mul, ofMul_div]
  rfl

/-- **A two-cochain which is locally a coboundary at a finite place remains so after twisting by
the coboundary of a one-cochain.** -/
theorem exists_sub_add_eq_adicUnits_twist (v : HeightOneSpectrum (𝓞 K))
    {a : Gal(K/k) × Gal(K/k) → Kˣ} (u : Gal(K/k) → Kˣ)
    (h : ∃ b : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (a (s.1, t.1)))
          = smulUnitsAut s (b t) - b (s * t) + b s) :
    ∃ b : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (twist a u (s.1, t.1)))
          = smulUnitsAut s (b t) - b (s * t) + b s := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨d, hd⟩ := exists_sub_add_eq_adicUnits_coboundary₂ (k := k) v u
  refine ⟨fun s => b s - d s, fun s t => ?_⟩
  have hdiv : Additive.ofMul (adicUnitHom v (twist a u (s.1, t.1)))
      = Additive.ofMul (adicUnitHom v (a (s.1, t.1)))
        - Additive.ofMul (adicUnitHom v (coboundary₂ u (s.1, t.1))) := by
    rw [← ofMul_div, ← map_div]
    rfl
  rw [hdiv, hb s t, hd s t]
  simp only [map_sub]
  abel

end InverseGalois.CFT

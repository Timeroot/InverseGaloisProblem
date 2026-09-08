/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.PiTwo

/-!
# The everywhere locally trivial classes of the first cohomology, along a map of the coefficients

Restriction to a subgroup composes a cocycle with the inclusion, and a map of the coefficients
composes a cocycle with that map; the two compositions are on opposite sides and so commute.  A
class which dies on every subgroup of a family therefore still dies on every subgroup of the family
after the coefficients are moved, and the map of the coefficients cuts down to the everywhere
locally trivial classes.

The same statements in the second cohomology are already available; what is added here is the first
cohomology, which is the degree a duality argument reads the dual side in.

## Main definitions

* `InverseGalois.CFT.shaCoeffH1`: the everywhere locally trivial classes of the first cohomology,
  carried along a map of the coefficients.
* `InverseGalois.CFT.shaCoeffH2`: the everywhere locally trivial classes of the second cohomology,
  carried along a map of the coefficients.

## Main results

* `InverseGalois.CFT.resH1_coeffH1`: restriction to a subgroup commutes with a map of the
  coefficients, in the first cohomology.
* `InverseGalois.CFT.coeffH1_mem_sha1`: **a map of the coefficients carries everywhere locally
  trivial classes of the first cohomology to everywhere locally trivial classes.**

## Tags

Galois cohomology, local-global principle, Shafarevich group, coefficients
-/

namespace InverseGalois.CFT

/-! ### Restriction and the coefficients in degree one -/

section Restrict

variable {G M N : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup N]
variable [MulDistribMulAction G M] [MulDistribMulAction G N] (φ : M →* N)
variable (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)

include hφ

/-- **Restriction to a subgroup commutes with a map of the coefficients**: both are composition of
the cocycle with something, and on opposite sides. -/
theorem resH1_coeffH1 (H : Subgroup G) (x : SmoothH1 G M) :
    resH1 H (coeffH1 φ hφ x)
      = coeffH1 φ (fun (h : H) (m : M) => hφ (h : G) m) (resH1 H x) := by
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective x
  rfl

/-- **A map of the coefficients carries everywhere locally trivial classes to everywhere locally
trivial classes**, in the first cohomology. -/
theorem coeffH1_mem_sha1 {S : Set (Subgroup G)} {x : SmoothH1 G M} (hx : x ∈ sha1 M S) :
    coeffH1 φ hφ x ∈ sha1 N S := by
  refine mem_sha1.2 fun D hD => ?_
  rw [resH1_coeffH1 φ hφ D x, mem_sha1.1 hx D hD, map_one]

/-- **The everywhere locally trivial classes of the first cohomology, along a map of the
coefficients.** -/
def shaCoeffH1 (S : Set (Subgroup G)) : ↥(sha1 M S) →* ↥(sha1 N S) where
  toFun z := ⟨coeffH1 φ hφ (z : SmoothH1 G M), coeffH1_mem_sha1 φ hφ z.2⟩
  map_one' := Subtype.ext (_root_.map_one _)
  map_mul' _ _ := Subtype.ext (_root_.map_mul _ _ _)

@[simp]
theorem coe_shaCoeffH1 (S : Set (Subgroup G)) (z : ↥(sha1 M S)) :
    (shaCoeffH1 φ hφ S z : SmoothH1 G N) = coeffH1 φ hφ (z : SmoothH1 G M) := rfl

/-- **The everywhere locally trivial classes of the second cohomology, along a map of the
coefficients.** -/
def shaCoeffH2 (S : Set (Subgroup G)) : ↥(sha2 M S) →* ↥(sha2 N S) where
  toFun z := ⟨coeffH2 φ hφ (z : SmoothH2 G M), coeffH2_mem_sha2 φ hφ z.2⟩
  map_one' := Subtype.ext (_root_.map_one _)
  map_mul' _ _ := Subtype.ext (_root_.map_mul _ _ _)

@[simp]
theorem coe_shaCoeffH2 (S : Set (Subgroup G)) (z : ↥(sha2 M S)) :
    (shaCoeffH2 φ hφ S z : SmoothH2 G N) = coeffH2 φ hφ (z : SmoothH2 G M) := rfl

end Restrict

end InverseGalois.CFT

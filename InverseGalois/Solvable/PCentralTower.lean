/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.PCentralFree
import InverseGalois.Solvable.PCentralFrattini
import InverseGalois.Solvable.PCentralShrink

/-!
# The tower of free objects of increasing `p`-class

Raising the `p`-class by one passes from the free object of rank `d` and class `c` to the free
object of rank `d` and class `c + 1`, and the projection between them is the quotient by the `c`-th
term of the lower `p`-central series of the larger one.  That term is central, of exponent `p`, and
made of non-generating elements, so each rung of the tower is a central Frattini extension with
elementary abelian kernel: exactly the shape of embedding problem that the Scholz–Reichardt
induction climbs.

## Main results

* `InverseGalois.FreePClass.proj`: the projection onto the free object of one lower `p`-class.
* `InverseGalois.FreePClass.ker_proj`: **its kernel is the `c`-th term of the lower `p`-central
  series**, which is central, of exponent `p`, and inside the Frattini subgroup.

## Tags

`p`-group, lower central series, free object, central extension, Frattini extension
-/

namespace InverseGalois

namespace FreePClass

/-! ## The rung of the tower -/

variable (p d c : ℕ)

/-- The projection of the free object of `p`-class at most `c + 1` onto the free object of
`p`-class at most `c`. -/
def proj : FreePClass p d (c + 1) →* FreePClass p d c :=
  (quotientEquiv p d (Nat.le_succ c)).toMonoidHom.comp
    (QuotientGroup.mk' (lowerPCentralSeries p (FreePClass p d (c + 1)) c))

@[simp] theorem proj_gen (i : Fin d) : proj p d c (gen p d (c + 1) i) = gen p d c i := rfl

theorem proj_surjective : Function.Surjective (proj p d c) :=
  (quotientEquiv p d (Nat.le_succ c)).surjective.comp (QuotientGroup.mk'_surjective _)

/-- **The kernel of the projection is the `c`-th term of the lower `p`-central series** of the free
object of `p`-class at most `c + 1`. -/
theorem ker_proj : (proj p d c).ker = lowerPCentralSeries p (FreePClass p d (c + 1)) c := by
  ext x
  have hmk : (QuotientGroup.mk' (lowerPCentralSeries p (FreePClass p d (c + 1)) c)) x = 1 ↔
      x ∈ lowerPCentralSeries p (FreePClass p d (c + 1)) c := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  rw [MonoidHom.mem_ker, ← hmk]
  show (quotientEquiv p d (Nat.le_succ c))
      ((QuotientGroup.mk' (lowerPCentralSeries p (FreePClass p d (c + 1)) c)) x) = 1 ↔ _
  exact map_eq_one_iff _ (quotientEquiv p d (Nat.le_succ c)).injective

/-- The kernel of the projection is central. -/
theorem ker_proj_le_center : (proj p d c).ker ≤ Subgroup.center (FreePClass p d (c + 1)) := by
  rw [ker_proj]
  exact lowerPCentralSeries_le_center (lowerPCentralSeries_eq_bot p d (c + 1))

/-- The kernel of the projection has exponent dividing `p`. -/
theorem pow_eq_one_of_mem_ker_proj {x : FreePClass p d (c + 1)} (hx : x ∈ (proj p d c).ker) :
    x ^ p = 1 :=
  pow_eq_one_of_mem_lowerPCentralSeries (lowerPCentralSeries_eq_bot p d (c + 1))
    ((ker_proj p d c) ▸ hx)

/-- **The kernel of the projection consists of non-generating elements** once the class below is at
least one, the first term of the lower `p`-central series of a finite `p`-group lying inside its
Frattini subgroup. -/
theorem ker_proj_le_frattini [Fact p.Prime] (hc : 1 ≤ c) :
    (proj p d c).ker ≤ frattini (FreePClass p d (c + 1)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [ker_proj]
  exact lowerPCentralSeries_le_frattini (isPGroup p d (c + 1)) hc

end FreePClass

end InverseGalois

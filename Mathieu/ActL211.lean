import Mathieu.EnumL211
import Mathieu.DefM11

/-!
# The exceptional action of `SL(2,𝔽₁₁)` on `11` points: definitions

This file sets up the concrete data for the exceptional `2`-transitive action of `PSL(2,11)`
on `11` points (see `PSL211.lean` for the assembled embedding `PSL(2,11) ↪ M₁₁`):

* `reps : Fin 11 → SL(2,𝔽₁₁)` — an explicit transversal of the index-`11` subgroup
  `K = ⟨A,B⟩` (order `120`, an `SL(2,5)≅2.A₅`, from `EnumL211`);
* `inKb` — the Boolean `K`-membership test, via the verified enumeration `EnumL211.KK`;
* `cIdx g` — the index `i` of the coset `reps i · K` containing `g`;
* small `native_decide` certificates: the generators `T,S` act as `m11a` / the word `wS`, and
  `±1` act trivially.

The heavier `native_decide` certificates (`cover`, `distinctb`, kernel/centre filters) live in
the separate files `CoverL211.lean` and `FilterL211.lean` to keep per-file memory bounded.
-/

namespace Mathieu

open Matrix Equiv
open scoped MatrixGroups

namespace PSL211

set_option maxRecDepth 400000
set_option maxHeartbeats 8000000

/-- Decidable equality on `SL(2, 𝔽₁₁)` (needed for the `native_decide` certificates). -/
instance instDecEqSL11 : DecidableEq (SL(2, ZMod 11)) :=
  fun a b => decidable_of_iff (a.1 = b.1) (by rw [Subtype.ext_iff])

/-- The index-`11` subgroup `K = ⟨A, B⟩` of order `120`. -/
def K : Subgroup (SL(2, ZMod 11)) := Subgroup.closure {EnumL211.Amat, EnumL211.Bmat}

/-- The explicit transversal of `K` in `SL(2, 𝔽₁₁)`: `11` coset representatives, chosen so that
the standard generators act as elements of `M₁₁`. -/
def reps : Fin 11 → SL(2, ZMod 11) := ![
  ⟨!![10,10;10,9], by decide⟩, ⟨!![10,10;9,8], by decide⟩, ⟨!![10,10;8,7], by decide⟩,
  ⟨!![10,10;7,6], by decide⟩, ⟨!![10,10;6,5], by decide⟩, ⟨!![10,10;5,4], by decide⟩,
  ⟨!![10,10;4,3], by decide⟩, ⟨!![10,10;3,2], by decide⟩, ⟨!![10,10;2,1], by decide⟩,
  ⟨!![10,10;1,0], by decide⟩, ⟨!![10,10;0,10], by decide⟩]

/-- The Boolean membership test for `K`, via the verified enumeration `EnumL211.KK`. -/
def inKb (g : SL(2, ZMod 11)) : Bool := EnumL211.encM g.1 ∈ EnumL211.KK

/-- The coset index of `g`: the index `i` such that `g ∈ reps i · K`. -/
def cIdx (g : SL(2, ZMod 11)) : Fin 11 :=
  ((List.finRange 11).find? (fun i => inKb ((reps i)⁻¹ * g))).getD 0

/-- The standard generator `S = !![1,1;0,1]` maps to this word in the `M₁₁` generators. -/
def wS : Equiv.Perm (Fin 11) := m11b * m11a * m11b⁻¹ * m11a ^ 3 * m11b * m11a⁻¹

/-- `1` acts trivially: `cIdx (1 · reps i) = i`. -/
lemma oneCIdx (i : Fin 11) : cIdx ((1 : SL(2, ZMod 11)) * reps i) = i := by
  revert i; decide

/-- `-1` acts trivially: `cIdx (-1 · reps i) = i`. -/
lemma negCIdx (i : Fin 11) : cIdx ((-1 : SL(2, ZMod 11)) * reps i) = i := by
  revert i; decide

/-- `T = !![1,0;1,1]` acts as the `11`-cycle `m11a`. -/
lemma tmatPerm (i : Fin 11) : cIdx (EnumL211.Tmat * reps i) = m11a i := by
  revert i; decide

/-- `S = !![1,1;0,1]` acts as the word `wS`. -/
lemma smatPerm (i : Fin 11) : cIdx (EnumL211.Smat * reps i) = wS i := by
  revert i; decide

end PSL211

end Mathieu

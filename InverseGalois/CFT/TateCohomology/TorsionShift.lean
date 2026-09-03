/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Acyclic
import InverseGalois.CFT.TateCohomology.Iterate
import InverseGalois.CFT.TateCohomology.Restrict
import InverseGalois.CFT.TateCohomology.TorsionFree

/-!
# The reduction and the torsion of a representation with no complete cohomology

Multiplication by a natural number factors through the multiples of that number: the vectors it
kills, the representation, and its multiples form one short exact sequence, and the multiples, the
representation, and the reduction form another.  Both have the representation itself in the middle,
so if the representation has no complete cohomology at all then both connecting maps are bijective.

Running them one after the other, **the complete cohomology of the reduction in a degree is the
complete cohomology of the vectors killed by the number two degrees higher.**  Nothing else about
the representation is used, and neither sequence needs the number to act without torsion — that
hypothesis is precisely what makes the first sequence degenerate and the torsion vanish.

The statement is what the theorem of Tate and Nakayama needs for coefficients with torsion.  There
the representation in the middle is the extension attached to the fundamental class, which is
cohomologically trivial; the hypothesis that its reduction has no first cohomology is therefore not
opaque but a statement about the vectors of the extension killed by the prime, three degrees up.

## Main definitions

* `InverseGalois.CFT.Tate.nsmulTorsion`: the vectors killed by a natural number, as a
  representation.
* `InverseGalois.CFT.Tate.nsmulMultiples`: the multiples of a natural number, as a representation.
* `InverseGalois.CFT.Tate.nsmulTorsionSeq`, `InverseGalois.CFT.Tate.nsmulMultiplesSeq`: the two
  short exact sequences into which multiplication by the number factors.

## Main results

* `InverseGalois.CFT.Tate.nsmulTorsionShiftEquiv`,
  `InverseGalois.CFT.Tate.nsmulMultiplesShiftEquiv`: **each of the two sequences shifts the degree
  by one** when the representation in the middle has no complete cohomology.
* `InverseGalois.CFT.Tate.modNsmulTorsionEquiv`: **the complete cohomology of the reduction of a
  representation with no complete cohomology is the complete cohomology of the vectors killed by
  the number two degrees higher.**
* `InverseGalois.CFT.Tate.isZero_groupCohomology_one_modNsmul`: **the reduction has no first
  cohomology as soon as those vectors have none in degree three.**

## Tags

Tate cohomology, dimension shifting, torsion, cohomologically trivial, Tate-Nakayama
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G) (m : ℕ)

/-! ### The vectors killed by a number and the multiples of it -/

section Objects

omit [Finite G] in
/-- The vectors killed by a number form a stable submodule. -/
theorem ker_nsmulLinear_le_comap (g : G) :
    LinearMap.ker (nsmulLinear k m ↥A.V)
      ≤ (LinearMap.ker (nsmulLinear k m ↥A.V)).comap (A.ρ g) := by
  intro v hv
  have hv' : m • v = (0 : ↥A.V) := LinearMap.mem_ker.mp hv
  refine Submodule.mem_comap.mpr (LinearMap.mem_ker.mpr ?_)
  show m • A.ρ g v = (0 : ↥A.V)
  rw [← map_nsmul (A.ρ g) m v, hv', map_zero]

/-- **The vectors killed by a natural number**, as a representation. -/
def nsmulTorsion : Rep k G :=
  Rep.of (A.ρ.subrepresentation _ (ker_nsmulLinear_le_comap A m))

/-- **The multiples of a natural number**, as a representation. -/
def nsmulMultiples : Rep k G :=
  Rep.of (A.ρ.subrepresentation _ (range_nsmulLinear_le_comap A m))

omit [Finite G] in
/-- **Every vector killed by the number is killed by it.** -/
theorem nsmul_nsmulTorsion_eq_zero (v : ↥(nsmulTorsion A m).V) : m • v = 0 :=
  Subtype.ext (LinearMap.mem_ker.mp v.2)

omit [Finite G] in
/-- **Restriction to a subgroup commutes with taking the vectors killed by a number.** -/
theorem resObj_nsmulTorsion (H : Subgroup G) :
    resObj H (nsmulTorsion A m) = nsmulTorsion (resObj H A) m := rfl

omit [Finite G] in
/-- **Restriction to a subgroup commutes with taking the multiples of a number.** -/
theorem resObj_nsmulMultiples (H : Subgroup G) :
    resObj H (nsmulMultiples A m) = nsmulMultiples (resObj H A) m := rfl

end Objects

/-! ### The two short exact sequences -/

section Sequences

/-- **The vectors killed by a number, the representation, and its multiples.** -/
def nsmulTorsionSeq : ShortComplex (Rep k G) where
  X₁ := nsmulTorsion A m
  X₂ := A
  X₃ := nsmulMultiples A m
  f := mkHom (LinearMap.ker (nsmulLinear k m ↥A.V)).subtype fun _ => LinearMap.ext fun _ => rfl
  g := mkHom ((nsmulLinear k m ↥A.V).codRestrict (LinearMap.range (nsmulLinear k m ↥A.V))
        fun v => ⟨v, rfl⟩)
      fun g => LinearMap.ext fun v => Subtype.ext (map_nsmul (A.ρ g) m v).symm
  zero := by
    ext v
    exact Subtype.ext (LinearMap.mem_ker.mp v.2)

omit [Finite G] in
/-- **The vectors killed by a number, the representation, and its multiples form a short exact
sequence.** -/
theorem nsmulTorsionSeq_shortExact : (nsmulTorsionSeq A m).ShortExact := by
  refine shortExact_of_linearMap (fun _ _ h => Subtype.ext h) (fun w => ?_) fun x hx => ?_
  · obtain ⟨v, hv⟩ := w.2
    exact ⟨v, Subtype.ext hv⟩
  · exact ⟨⟨x, LinearMap.mem_ker.mpr (congrArg Subtype.val hx)⟩, rfl⟩

/-- **The multiples of a number, the representation, and its reduction.** -/
def nsmulMultiplesSeq : ShortComplex (Rep k G) where
  X₁ := nsmulMultiples A m
  X₂ := A
  X₃ := modNsmul A m
  f := mkHom (LinearMap.range (nsmulLinear k m ↥A.V)).subtype fun _ => LinearMap.ext fun _ => rfl
  g := mkHom (LinearMap.range (nsmulLinear k m ↥A.V)).mkQ fun _ => LinearMap.ext fun _ => rfl
  zero := by
    ext v
    exact (Submodule.Quotient.mk_eq_zero _).2 v.2

omit [Finite G] in
/-- **The multiples of a number, the representation, and its reduction form a short exact
sequence.** -/
theorem nsmulMultiplesSeq_shortExact : (nsmulMultiplesSeq A m).ShortExact :=
  shortExact_of_linearMap (fun _ _ h => Subtype.ext h) (Submodule.mkQ_surjective _)
    fun x hx => ⟨⟨x, (Submodule.Quotient.mk_eq_zero _).1 hx⟩, rfl⟩

end Sequences

/-! ### The two shifts of the degree -/

section Shift

variable (h : ∀ i : ℤ, Limits.IsZero (tateModule A i))

include h

/-- **The complete cohomology of the multiples of a number in a degree is the complete cohomology
of the vectors it kills in the following degree**, when the representation has none. -/
def nsmulTorsionShiftEquiv (n : ℤ) :
    ↥(tateModule (nsmulMultiples A m) n) ≃ₗ[k] ↥(tateModule (nsmulTorsion A m) (n + 1)) :=
  LinearEquiv.ofBijective (tateδ (nsmulTorsionSeq_shortExact A m) n).hom
    (bijective_tateδ (nsmulTorsionSeq_shortExact A m) n (h n) (h (n + 1)))

/-- **The complete cohomology of the reduction of a representation modulo a number in a degree is
the complete cohomology of the multiples of that number in the following degree**, when the
representation has none. -/
def nsmulMultiplesShiftEquiv (n : ℤ) :
    ↥(tateModule (modNsmul A m) n) ≃ₗ[k] ↥(tateModule (nsmulMultiples A m) (n + 1)) :=
  LinearEquiv.ofBijective (tateδ (nsmulMultiplesSeq_shortExact A m) n).hom
    (bijective_tateδ (nsmulMultiplesSeq_shortExact A m) n (h n) (h (n + 1)))

/-- **The complete cohomology of the reduction of a representation with no complete cohomology is
the complete cohomology of the vectors killed by the number two degrees higher.** -/
def modNsmulTorsionEquiv (n : ℤ) :
    ↥(tateModule (modNsmul A m) n) ≃ₗ[k] ↥(tateModule (nsmulTorsion A m) (n + 1 + 1)) :=
  (nsmulMultiplesShiftEquiv A m h n).trans (nsmulTorsionShiftEquiv A m h (n + 1))

/-- **The reduction has no complete cohomology in a degree in which the vectors killed by the
number have none two degrees higher.** -/
theorem isZero_tateModule_modNsmul (n : ℤ)
    (ht : Limits.IsZero (tateModule (nsmulTorsion A m) (n + 1 + 1))) :
    Limits.IsZero (tateModule (modNsmul A m) n) :=
  isZero_of_forall_eq_zero fun x =>
    (modNsmulTorsionEquiv A m h n).injective
      (by rw [map_zero]; exact eq_zero_of_isZero ht _)

/-- **The vectors killed by the number have no complete cohomology two degrees above a degree in
which the reduction has none.** -/
theorem isZero_tateModule_nsmulTorsion (n : ℤ)
    (hq : Limits.IsZero (tateModule (modNsmul A m) n)) :
    Limits.IsZero (tateModule (nsmulTorsion A m) (n + 1 + 1)) :=
  isZero_of_forall_eq_zero fun y => by
    obtain ⟨x, rfl⟩ := (modNsmulTorsionEquiv A m h n).surjective y
    rw [eq_zero_of_isZero hq x, map_zero]

/-- **The reduction of a representation with no complete cohomology has no first cohomology as soon
as the vectors killed by the number have none in degree three.** -/
theorem isZero_groupCohomology_one_modNsmul
    (ht : Limits.IsZero (tateModule (nsmulTorsion A m) 3)) :
    Limits.IsZero (groupCohomology (modNsmul A m) 1) :=
  isZero_tateModule_modNsmul A m h 1
    (isZero_tateModule_congr (show (3 : ℤ) = 1 + 1 + 1 by norm_num) ht)

end Shift

end

end InverseGalois.CFT.Tate

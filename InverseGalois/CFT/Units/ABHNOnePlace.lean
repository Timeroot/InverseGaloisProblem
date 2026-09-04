/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.InfiniteInvariant
import InverseGalois.CFT.Brauer.InfinitePlaceCrossedProduct
import InverseGalois.CFT.Brauer.PlaceCoboundary
import InverseGalois.CFT.Units.ABHN
import InverseGalois.CFT.Units.DecompositionReciprocity

/-!
# A two-cocycle of the units which is a coboundary at every place but one

The theorem of Albert, Brauer, Hasse and Noether says that a two-cocycle of the Galois group of an
extension of number fields with values in the units of the top field is a coboundary as soon as it
is one at every place.  The product formula for the local invariants improves that hypothesis: the
invariants multiply to one, so the invariant at any single place is determined by all the others,
and **one place may be left out of the local hypotheses for free**.

The statement below is the form the improvement takes at the level of explicit cochains, which is
the form in which a cocycle is produced by a long exact sequence: the coboundary data are given at
every infinite place and at every finite place whose trace to the base differs from that of a
distinguished one, and the conclusion is a global one-cochain whose coboundary is the given
two-cocycle.

## Main results

* `InverseGalois.CFT.exists_sub_add_eq_globalUnits_of_forall_ne`: **a two-cocycle of the Galois
  group with values in the units of the top field which is a coboundary at every infinite place and
  at every finite place but one is a coboundary.**

## Tags

number field, Brauer group, group cohomology, two-cocycle, coboundary, local invariant,
reciprocity, Albert-Brauer-Hasse-Noether
-/

set_option synthInstance.maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField groupCohomology

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **A two-cocycle of the Galois group with values in the units of the top field which is a
coboundary at every infinite place and at every finite place but one is a coboundary.**  The
invariant of the associated Brauer class vanishes at every place but the one left out, and the
product formula forces the remaining invariant to vanish as well. -/
theorem exists_sub_add_eq_globalUnits_of_forall_ne (w : HeightOneSpectrum (𝓞 K))
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (ha : ∀ x y z : Gal(K/k),
      globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y)
    (hinf : ∀ u : InfinitePlace K, ∃ c : ↥(stabilizer Gal(K/k) u) → Additive u.Completionˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) u),
        Additive.ofMul (infiniteUnitHom u (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) v ≠ primeUnder (𝓞 k) w →
      ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ b : Gal(K/k) → Additive Kˣ,
      ∀ x y : Gal(K/k), a x y = globalUnitsAut x (b y) - b (x * y) + b x := by
  have hact : ∀ (σ : Gal(K/k)) (y : Additive Kˣ),
      Additive.toMul (globalUnitsAut (k := k) σ y) = σ • Additive.toMul y :=
    fun _ _ => Units.ext rfl
  have hf : IsMulCocycle₂ (fun p : Gal(K/k) × Gal(K/k) => (a p.1 p.2).toMul) := by
    intro g h j
    have h1 := congrArg Additive.toMul (ha g h j)
    rw [_root_.toMul_add, _root_.toMul_add, hact] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := isMulCoboundary₂_of_forall_ne k w hf
    (fun W hW => (isMulCoboundary₂_localCocycle_iff k W _).2 (hfin W hW))
    (fun u => by
      obtain ⟨U, rfl⟩ := InfinitePlace.comap_surjective (k := k) (K := K) u
      exact (infinitePlaceInvariant_eq_one_iff k _ _).2
        ((mem_relative_mk_csa_infiniteCompletion_iff_exists k U hf).2 (hinf U)))
  refine ⟨fun g => Additive.ofMul (c g), fun x y => Additive.toMul.injective ?_⟩
  simp only [_root_.toMul_add, _root_.toMul_sub, hact, _root_.toMul_ofMul]
  exact (hc x y).symm

end InverseGalois.CFT

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicProduct
import InverseGalois.CFT.Brauer.InfiniteCyclic
import InverseGalois.CFT.Brauer.TotalInvariant
import InverseGalois.CFT.Units.OrbitPlaces

/-!
# The Hasse norm theorem

Let `K / k` be a cyclic extension of number fields.  An element of the base field which is a norm
from the extension is a norm locally at every place, simply because a norm stays a norm after any
extension of scalars.  The Hasse norm theorem is the converse: an element which is everywhere
locally a norm is a norm.

Both directions are statements about a single Brauer class.  The cyclic algebra `(K / k, σ₀, a)` is
trivial exactly when `a` is a norm, and its base change to a completion is the cyclic algebra of the
decomposition group with the same coefficient, so the local invariant at a place vanishes exactly
when `a` is a norm from the completion of `K` there.  The forward direction is then the vanishing of
a trivial class, and the converse is the Albert-Brauer-Hasse-Noether theorem: a class all of whose
local invariants vanish is trivial.

Every place of the base carries a place of the extension above it, so quantifying over the places
of the extension quantifies over the places of the base as well, and the local conditions can be
written at the primes and infinite places of `K`.

## Main results

* `InverseGalois.CFT.exists_adicCompletion_norm_eq_of_exists_norm_eq` and
  `InverseGalois.CFT.exists_infiniteCompletion_norm_eq_of_exists_norm_eq`: a norm is a local norm at
  every finite and at every infinite place.
* `InverseGalois.CFT.exists_norm_eq_of_forall_local`: **the Hasse norm theorem** — an element of the
  base field of a cyclic extension of number fields which is a norm at every place is a norm.
* `InverseGalois.CFT.exists_norm_eq_iff_forall_local`: the two directions together.

## Tags

Hasse norm theorem, cyclic extension, local norm, Brauer group, local invariant,
Albert-Brauer-Hasse-Noether, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section HasseNorm

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

variable (k) in
/-- **A norm from a cyclic extension of number fields is a norm from the completion at every finite
place.**  The cyclic algebra with the given coefficient is trivial, hence so is its base change to
the completion, which is the cyclic algebra of the decomposition group with the same
coefficient. -/
theorem exists_adicCompletion_norm_eq_of_exists_norm_eq {σ₀ : Gal(K/k)}
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) {a : kˣ}
    (ha : ∃ b : Kˣ, Algebra.norm k (b : K) = (a : k)) (w : HeightOneSpectrum (𝓞 K)) :
    ∃ b : (w.adicCompletion K)ˣ,
      Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) (b : w.adicCompletion K)
        = algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k) (a : k) := by
  have hker : cyclicBrauerHom hσ₀ a = 1 :=
    MonoidHom.mem_ker.mp ((mem_ker_cyclicBrauerHom_iff hσ₀ a).mpr ha)
  refine (placeInvariant_cyclicBrauerHom_eq_one_iff k w hσ₀ a).mp ?_
  rw [hker, map_one]

variable (k) in
/-- **A norm from a cyclic extension of number fields is a norm from the completion at every
infinite place.** -/
theorem exists_infiniteCompletion_norm_eq_of_exists_norm_eq {σ₀ : Gal(K/k)}
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) {a : kˣ}
    (ha : ∃ b : Kˣ, Algebra.norm k (b : K) = (a : k)) (w : InfinitePlace K) :
    ∃ b : (w.Completion)ˣ,
      Algebra.norm (w.comap (algebraMap k K)).Completion (b : w.Completion)
        = algebraMap k (w.comap (algebraMap k K)).Completion (a : k) := by
  have hker : cyclicBrauerHom hσ₀ a = 1 :=
    MonoidHom.mem_ker.mp ((mem_ker_cyclicBrauerHom_iff hσ₀ a).mpr ha)
  refine (infinitePlaceInvariant_cyclicBrauerHom_eq_one_iff k w hσ₀ a).mp ?_
  rw [hker, map_one]

variable (k) in
/-- **The Hasse norm theorem.**  An element of the base field of a cyclic extension of number fields
which is a norm from the completion of the extension at every finite and every infinite place is a
norm from the extension.  All the local invariants of the cyclic algebra with that coefficient
vanish, so the class is trivial by the Albert-Brauer-Hasse-Noether theorem, and a trivial cyclic
algebra has a coefficient which is a norm. -/
theorem exists_norm_eq_of_forall_local {σ₀ : Gal(K/k)}
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) {a : kˣ}
    (hfin : ∀ w : HeightOneSpectrum (𝓞 K), ∃ b : (w.adicCompletion K)ˣ,
      Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) (b : w.adicCompletion K)
        = algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k) (a : k))
    (hinf : ∀ w : InfinitePlace K, ∃ b : (w.Completion)ˣ,
      Algebra.norm (w.comap (algebraMap k K)).Completion (b : w.Completion)
        = algebraMap k (w.comap (algebraMap k K)).Completion (a : k)) :
    ∃ b : Kˣ, Algebra.norm k (b : K) = (a : k) := by
  have hker : cyclicBrauerHom hσ₀ a = 1 := by
    refine eq_one_of_forall_invariant_eq_one k _ (fun v => ?_) fun u => ?_
    · obtain ⟨w, hw⟩ := exists_primeUnder_eq (𝓞 k) (𝓞 K) v
      subst hw
      exact (placeInvariant_cyclicBrauerHom_eq_one_iff k w hσ₀ a).mpr (hfin w)
    · obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := k) (K := K) u
      subst hw
      exact (infinitePlaceInvariant_cyclicBrauerHom_eq_one_iff k w hσ₀ a).mpr (hinf w)
  exact (mem_ker_cyclicBrauerHom_iff hσ₀ a).mp (MonoidHom.mem_ker.mpr hker)

variable (k) in
/-- **The Hasse norm theorem, in both directions**: an element of the base field of a cyclic
extension of number fields is a norm exactly when it is a norm from the completion of the extension
at every place. -/
theorem exists_norm_eq_iff_forall_local {σ₀ : Gal(K/k)}
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) (a : kˣ) :
    (∃ b : Kˣ, Algebra.norm k (b : K) = (a : k)) ↔
      ((∀ w : HeightOneSpectrum (𝓞 K), ∃ b : (w.adicCompletion K)ˣ,
          Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) (b : w.adicCompletion K)
            = algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k) (a : k)) ∧
        ∀ w : InfinitePlace K, ∃ b : (w.Completion)ˣ,
          Algebra.norm (w.comap (algebraMap k K)).Completion (b : w.Completion)
            = algebraMap k (w.comap (algebraMap k K)).Completion (a : k)) :=
  ⟨fun ha => ⟨exists_adicCompletion_norm_eq_of_exists_norm_eq k hσ₀ ha,
      exists_infiniteCompletion_norm_eq_of_exists_norm_eq k hσ₀ ha⟩,
    fun h => exists_norm_eq_of_forall_local k hσ₀ h.1 h.2⟩

end HasseNorm

end InverseGalois.CFT

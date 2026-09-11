/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.LocalSurjective
import InverseGalois.CFT.Units.CompletionGalois

/-!
# A place with trivial decomposition group

The elements of the completion of a Galois extension of number fields at a prime which are fixed by
the decomposition group there are exactly those coming from the completion of the base field at the
prime below.  When the decomposition group is trivial that condition is empty, so the completions
agree: the prime is completely split, and the extension has bought nothing at that place.

Everything the extension carries is therefore already present in the base field locally.  In
particular a root of unity of the extension, transported into the completion, comes from the
completion of the base; so a base field whose extension contains the `p`-th roots of unity contains
them itself at every completely split prime.

## Main results

* `InverseGalois.CFT.surjective_algebraMap_adicCompletion_of_stabilizer_eq_bot`: **at a prime with
  trivial decomposition group the completion of the base field is the whole completion of the
  extension.**
* `InverseGalois.CFT.exists_isPrimitiveRoot_adicCompletion_of_stabilizer_eq_bot`: **a primitive root
  of unity of the extension gives one in the completion of the base at such a prime.**

## Tags

number field, place, decomposition group, completely split, completion, root of unity
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section Split

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **At a prime with trivial decomposition group the completion of the base field is the whole
completion of the extension.**  Every element of the completion is fixed by the decomposition
group, there being nothing in it to move anything. -/
theorem surjective_algebraMap_adicCompletion_of_stabilizer_eq_bot
    (h : stabilizer Gal(K/k) w = ⊥) :
    Function.Surjective
      (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)) := by
  intro z
  refine (mem_range_algebraMap_iff_forall_stabilizer_smul_eq k w z).1 fun σ => ?_
  rw [show σ = 1 from Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 h _ σ.2), one_smul]

variable (k) in
/-- **A primitive root of unity of the extension gives a primitive root of unity in the completion
of the base at a prime with trivial decomposition group.**  Its image in the completion of the
extension is again primitive, and that completion is the completion of the base. -/
theorem exists_isPrimitiveRoot_adicCompletion_of_stabilizer_eq_bot {p : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (h : stabilizer Gal(K/k) w = ⊥) :
    ∃ ξ : (primeUnder (𝓞 k) w).adicCompletion k, IsPrimitiveRoot ξ p := by
  obtain ⟨ξ, hξ⟩ := surjective_algebraMap_adicCompletion_of_stabilizer_eq_bot k w h
    (algebraMap K (w.adicCompletion K) ζ)
  exact ⟨ξ, IsPrimitiveRoot.of_map_of_injective
    (f := algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K))
    (hξ ▸ hζ.map_of_injective (algebraMap K (w.adicCompletion K)).injective)
    (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)).injective⟩

end Split

end InverseGalois.CFT

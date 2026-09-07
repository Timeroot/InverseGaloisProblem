/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.Selmer
import InverseGalois.CFT.Units.CompletionGalois

/-!
# A radical of a completely split place is already there

The completion of a Galois extension of number fields at a prime is a Galois extension of the
completion below, with group the decomposition group at the prime.  So a prime whose decomposition
group is trivial has completion equal to the completion below: every element of the completion of
the extension comes from the completion of the base.

An element of the base which becomes a `p`-th power in the extension is therefore a `p`-th power in
the completion at such a prime — the radical lies in the completion of the extension, hence in the
completion of the base — and a unit of the base which is a `p`-th power in a completion has trivial
class there.  This is what makes a prime completely split in a radical extension detect the
radicands: it kills all of them at once.

## Main results

* `InverseGalois.CFT.mem_range_algebraMap_of_stabilizer_eq_bot`: the completion at a prime with
  trivial decomposition group is the completion below.
* `InverseGalois.CFT.localClassHom_eq_one_of_pow_eq`: **a unit of the base which becomes a `p`-th
  power in the extension has trivial class at the prime below one with trivial decomposition
  group.**

## Tags

number field, completion, decomposition group, completely split, local power, radical
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

/-! ### The completion at a completely split prime -/

section Split

variable {K : Type} {L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {V : HeightOneSpectrum (𝓞 L)}

/-- **The completion at a prime with trivial decomposition group is the completion below.**  The
decomposition group is the Galois group of the completion over the completion below, so with it
trivial every element of the completion is fixed by it, hence comes from below. -/
theorem mem_range_algebraMap_of_stabilizer_eq_bot (hV : stabilizer Gal(L/K) V = ⊥)
    (z : V.adicCompletion L) :
    z ∈ Set.range (algebraMap ((primeUnder (𝓞 K) V).adicCompletion K) (V.adicCompletion L)) := by
  refine (mem_range_algebraMap_iff_forall_stabilizer_smul_eq K V z).1 fun σ => ?_
  rw [show σ = (1 : ↥(stabilizer Gal(L/K) V)) from
    Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 hV _ σ.2), one_smul]

variable {p : ℕ} [NeZero p]

/-- **A unit of the base which becomes a `p`-th power in the extension has trivial class at the
prime below one with trivial decomposition group.**  The radical lies in the completion of the
extension, which is the completion of the base, and its `p`-th power there is the unit. -/
theorem localClassHom_eq_one_of_pow_eq (hV : stabilizer Gal(L/K) V = ⊥) {b : Kˣ} {α : L}
    (hα : α ^ p = algebraMap K L (b : K)) :
    localClassHom (primeUnder (𝓞 K) V) p b = 1 := by
  obtain ⟨c, hc⟩ := mem_range_algebraMap_of_stabilizer_eq_bot hV (toAdicCompletion V α)
  have hkey : algebraMap ((primeUnder (𝓞 K) V).adicCompletion K) (V.adicCompletion L) (c ^ p)
      = algebraMap ((primeUnder (𝓞 K) V).adicCompletion K) (V.adicCompletion L)
        (algebraMap K ((primeUnder (𝓞 K) V).adicCompletion K) (b : K)) := by
    have h1 : algebraMap ((primeUnder (𝓞 K) V).adicCompletion K) (V.adicCompletion L) (c ^ p)
        = algebraMap L (V.adicCompletion L) (α ^ p) := by
      rw [_root_.map_pow, hc, _root_.map_pow]
      rfl
    rw [h1, hα, ← IsScalarTower.algebraMap_apply K L (V.adicCompletion L),
      ← IsScalarTower.algebraMap_apply K ((primeUnder (𝓞 K) V).adicCompletion K)
        (V.adicCompletion L)]
  have hcp : c ^ p = algebraMap K ((primeUnder (𝓞 K) V).adicCompletion K) (b : K) :=
    (algebraMap ((primeUnder (𝓞 K) V).adicCompletion K) (V.adicCompletion L)).injective hkey
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne p)] at hcp
    exact (map_ne_zero_iff _
      (algebraMap K ((primeUnder (𝓞 K) V).adicCompletion K)).injective).2 b.ne_zero hcp.symm
  refine (QuotientGroup.eq_one_iff _).2 ⟨Units.mk0 c hc0, Units.ext ?_⟩
  simpa [powMonoidHom] using hcp

end Split

end InverseGalois.CFT

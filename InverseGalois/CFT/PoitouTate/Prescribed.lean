/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.LocalConditions
import InverseGalois.CFT.PoitouTate.Selmer

/-!
# Global classes with prescribed local behaviour

The classes of the `S`-units of a number field are their own orthogonal complement inside the
local classes at the finite places of `S`, under the product of the norm residue symbols.  Feeding
that self-duality into the counting theorem for a maximal isotropic subgroup gives the statement
one builds extensions with: **an assignment of local classes is congruent, modulo a set of local
conditions, to the class of a global `S`-unit exactly when it pairs trivially with those `S`-units
whose classes obey the conditions dual to the given ones.**

The two shapes of condition that occur are a condition imposing nothing, whose dual imposes
everything, and the condition of being unramified, which is its own dual at a place not dividing
the exponent.  So for a set of places split into a part where the local class is prescribed
exactly and a part where it is prescribed only up to an unramified class, the `S`-units to test
against are exactly those unramified on the second part.  Splitting a set of places this way and
enlarging the first part one place at a time is the inductive construction behind the existence
theorem for algebraic numbers with prescribed local behaviour.

## Main results

* `InverseGalois.CFT.perpSubgroupLeft_localUnramified`: the unramified classes at a finite place
  not dividing the exponent are their own orthogonal complement on the left as well as on the
  right.
* `InverseGalois.CFT.exists_sUnitClass_mul_eq`: **an assignment of local classes orthogonal to the
  `S`-units obeying the dual conditions is congruent modulo the conditions to the class of an
  `S`-unit.**
* `InverseGalois.CFT.exists_sUnitClass_mul_eq_unramified`: the same for conditions which at each
  place either prescribe the class exactly or prescribe it up to an unramified class.

## Tags

Selmer group, local conditions, unramified, norm residue symbol, Poitou-Tate duality,
class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section Prescribed

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ} {Y : Type*} [Fintype Y]

/-- The norm residue symbol at a finite place, read on the classes modulo `n`-th powers. -/
noncomputable def localClassPairing
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (v : HeightOneSpectrum (𝓞 K)) :
    localClasses v n →* localClasses v n →* Multiplicative QModZ :=
  localSymbolQuotDual (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
    (hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective)

theorem localSymbolPiPairing_eq_piPairing
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (ι : Y → HeightOneSpectrum (𝓞 K)) :
    localSymbolPiPairing hres hζ ι
      = piPairing (A := fun y => localClasses (ι y) n)
        fun y => localClassPairing hres hζ (ι y) := rfl

/-- The unramified classes of the completion of a number field at a finite place. -/
noncomputable def localUnramified (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (localClasses v n) :=
  unramifiedClasses (isUnitValGen_one (valued_adicCompletion_surjective v)) n

/-- The classes at a finite place of a number field are finite in number. -/
theorem finite_localClasses (v : HeightOneSpectrum (𝓞 K)) : Finite (localClasses v n) := by
  haveI := finiteIndex_range_powMonoidHom_units_adicCompletion v (NeZero.ne n)
  infer_instance

/-- **The unramified classes at a finite place not dividing the exponent are their own orthogonal
complement on the left** as well as on the right. -/
theorem perpSubgroupLeft_localUnramified
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) {v : HeightOneSpectrum (𝓞 K)}
    (hv : FinitePlace.mk v ((n : ℕ) : K) = 1) :
    perpSubgroupLeft (A := localClasses v n) (localClassPairing hres hζ v) (localUnramified v n)
      = localUnramified v n := by
  haveI := finite_localClasses (n := n) v
  exact @perpSubgroupLeft_eq_self (localClasses v n) inferInstance inferInstance
    (localClassPairing hres hζ v)
    (injective_flip_localSymbolQuotDual (hres v)
      (isUnitValGen_one (valued_adicCompletion_surjective v))
      (hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective))
    (localUnramified v n)
    (perpSubgroup_unramifiedClasses_adicCompletion hζ (hres v) hn
      (not_dvd_of_finitePlace_natCast_eq_one (hres v) hv) hv)

/-- **An assignment of local classes orthogonal to the `S`-units obeying the dual conditions is
congruent modulo the conditions to the class of an `S`-unit.**  The classes of the `S`-units are
their own orthogonal complement, and the counting theorem for a maximal isotropic subgroup turns
that into the prescription. -/
theorem exists_sUnitClass_mul_eq (hn : n.Prime) (hodd : 2 < n)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v)
    (L : ∀ y : Y, Subgroup (localClasses (ι y) n))
    {c : (y : Y) → localClasses (ι y) n}
    (hc : ∀ b ∈ selmerGroup ι n ⊓ Subgroup.pi Set.univ
        (fun y => perpSubgroupLeft (A := localClasses (ι y) n)
          (localClassPairing hres hζ (ι y)) (L y)),
      localSymbolPiPairing hres hζ ι b c = 1) :
    ∃ a ∈ selmerGroup ι n, ∃ l ∈ Subgroup.pi Set.univ L, a * l = c := by
  classical
  haveI : ∀ y : Y, Finite (localClasses (ι y) n) := fun y => finite_localClasses (ι y)
  haveI : Finite ((y : Y) → localClasses (ι y) n) := Pi.finite
  have hperp : perpSubgroupLeft (A := (y : Y) → localClasses (ι y) n)
        (piPairing (A := fun y => localClasses (ι y) n)
          fun y => localClassPairing hres hζ (ι y)) (Subgroup.pi Set.univ L)
      = Subgroup.pi Set.univ fun y => perpSubgroupLeft (A := localClasses (ι y) n)
        (localClassPairing hres hζ (ι y)) (L y) :=
    @perpSubgroupLeft_piPairing_pi Y _ _ (fun y => localClasses (ι y) n)
      (fun _ => inferInstance) (Multiplicative QModZ) _
      (fun y => localClassPairing hres hζ (ι y)) L
  refine @exists_mul_eq_of_forall_pairing_eq_one ((y : Y) → localClasses (ι y) n) inferInstance
    inferInstance (localSymbolPiPairing hres hζ ι)
    (@injective_flip_piPairing Y _ (fun y => localClasses (ι y) n) (fun _ => inferInstance)
      (Multiplicative QModZ) _ _ (fun y => localClassPairing hres hζ (ι y))
      fun y => injective_flip_localSymbolQuotDual (hres (ι y))
        (isUnitValGen_one (valued_adicCompletion_surjective (ι y)))
        (hζ.map_of_injective (algebraMap K ((ι y).adicCompletion K)).injective))
    (selmerGroup ι n) (perpSubgroup_selmerGroup hn hodd hres hζ hinj hnι hrepr)
    (Subgroup.pi Set.univ L) c fun b hb => hc b ?_
  rw [← hperp]
  exact hb

/-- **An assignment of local classes prescribed exactly at some places and up to an unramified
class at the others is met by the class of an `S`-unit**, as soon as it is orthogonal to the
`S`-units unramified at the places of the second kind. -/
theorem exists_sUnitClass_mul_eq_unramified (hn : n.Prime) (hodd : 2 < n)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v)
    (L D : ∀ y : Y, Subgroup (localClasses (ι y) n))
    (hLD : ∀ y : Y, (L y = ⊥ ∧ D y = ⊤) ∨
      (FinitePlace.mk (ι y) ((n : ℕ) : K) = 1 ∧ L y = localUnramified (ι y) n ∧
        D y = localUnramified (ι y) n))
    {c : (y : Y) → localClasses (ι y) n}
    (hc : ∀ b ∈ selmerGroup ι n ⊓ Subgroup.pi Set.univ D,
      localSymbolPiPairing hres hζ ι b c = 1) :
    ∃ a ∈ selmerGroup ι n, ∃ l ∈ Subgroup.pi Set.univ L, a * l = c := by
  refine exists_sUnitClass_mul_eq hn hodd hres hζ hinj hnι hrepr L fun b hb => hc b ?_
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hb).1, (Subgroup.mem_pi _).2 fun y _ => ?_⟩
  have h := (Subgroup.mem_pi _).1 (Subgroup.mem_inf.1 hb).2 y (Set.mem_univ y)
  rcases hLD y with ⟨hL, hD⟩ | ⟨hv, hL, hD⟩
  · rw [hD]
    exact Subgroup.mem_top _
  · rw [hL, perpSubgroupLeft_localUnramified hres hζ hn hv] at h
    rwa [hD]

end Prescribed

end InverseGalois.CFT

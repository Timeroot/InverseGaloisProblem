/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.Prescribed
import InverseGalois.CFT.PoitouTate.SplitFamily

/-!
# A two-place family for a prescription named at finitely many places

The prescriptions an embedding problem produces are named at finitely many places and say nothing
anywhere else: at each of those places a family of local classes is demanded, one for each
coordinate of the group being built, and at every other place the demand is that the coordinate be
a local power.  This file reads such a naming as a prescription defined at every place and feeds it
to the two-place construction.

Everything the construction asks of a prescription is then a statement about the named places
alone.  Being unramified away from the distinguished part is automatic once the named places lie
inside it, since the prescription is trivial elsewhere; lying on a line is asked only where a class
is named; being trivial above the exponent is asked only at the named places above the exponent;
and the clause forbidding a prescription and its conjugate from both being nontrivial holds as soon
as no proper conjugate of a named place is named.

What is not automatic is the global step: a prescription is realised by an `S`-unit exactly when it
is orthogonal, under the product of the norm residue symbols, to every `S`-unit which is a local
power at the infinite places.  That is the Poitou-Tate input, and with it the whole two-place
family exists for a naming and nothing else.

## Main definitions

* `InverseGalois.CFT.spreadClasses` — **a family of local classes named at finitely many places,
  read as a prescription at every place.**

## Main results

* `InverseGalois.CFT.exists_isTwoPlaceFamily_named_of_sUnits` — a naming realised by a family of
  `S`-units has a two-place family.
* `InverseGalois.CFT.exists_isTwoPlaceFamily_named` — **a naming orthogonal to the `S`-units which
  are local powers at the infinite places has a two-place family.**

## Tags

number field, place, local class, prescription, S-unit, Poitou-Tate duality
-/

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### A prescription named at finitely many places -/

section Spread

variable {K : Type} [Field K] [NumberField K] {p : ℕ}
  {Tp : Finset (HeightOneSpectrum (𝓞 K))}

open scoped Classical in
/-- **A family of local classes named at finitely many places, read as a prescription at every
place**: the class named at a named place, and the trivial class everywhere else. -/
noncomputable def spreadClasses (Tp : Finset (HeightOneSpectrum (𝓞 K)))
    (cl : (w : ↥Tp) → ℕ → localClasses (w : HeightOneSpectrum (𝓞 K)) p) (t : ℕ)
    (w : HeightOneSpectrum (𝓞 K)) : localClasses w p :=
  if h : w ∈ Tp then cl ⟨w, h⟩ t else 1

variable {cl : (w : ↥Tp) → ℕ → localClasses (w : HeightOneSpectrum (𝓞 K)) p}

/-- At a named place the prescription is the class named there. -/
theorem spreadClasses_of_mem {w : HeightOneSpectrum (𝓞 K)} (hw : w ∈ Tp) (t : ℕ) :
    spreadClasses Tp cl t w = cl ⟨w, hw⟩ t := dif_pos hw

/-- Away from the named places the prescription is trivial. -/
theorem spreadClasses_of_notMem {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ Tp) (t : ℕ) :
    spreadClasses Tp cl t w = 1 := dif_neg hw

end Spread

/-! ### The two-place family of a naming -/

section Named

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  [IsScalarTower k K A] {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω]
  {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

variable (Ω) in
/-- **A naming realised by a family of `S`-units has a two-place family.**  Each clause the
two-place construction asks of a prescription is a statement about the named places alone, the
prescription being trivial everywhere else. -/
theorem exists_isTwoPlaceFamily_named_of_sUnits (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {Tp Tr Tn : Finset (HeightOneSpectrum (𝓞 K))} (hTp : Tp ⊆ Tr) (hTr : Tr ⊆ Tn)
    (hTrst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tr → σ • v ∈ Tr)
    (hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {cl : (w : ↥Tp) → ℕ → localClasses (w : HeightOneSpectrum (𝓞 K)) p}
    (hcln : ∀ (w : ↥Tp) (t : ℕ),
      FinitePlace.mk (w : HeightOneSpectrum (𝓞 K)) ((p : ℕ) : K) ≠ 1 → cl w t = 1)
    {D : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hDgal : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
      Subgroup.zpowers (D (σ • v)) = Subgroup.zpowers (localClassesGalEquiv σ v p (D v)))
    (hDcl : ∀ (w : ↥Tp) (t : ℕ),
      cl w t ∈ Subgroup.zpowers (D (w : HeightOneSpectrum (𝓞 K))))
    {g : ℕ → Kˣ} (hg : ∀ t : ℕ, g t ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hgcl : ∀ (t : ℕ) (w : ↥Tp),
      cl w t = localClassHom (w : HeightOneSpectrum (𝓞 K)) p (g t))
    (hg1 : ∀ t : ℕ, ∀ w ∈ Tn, w ∉ Tp → localClassHom w p (g t) = 1)
    (hram : ∀ v ∉ Tn, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1) (d : ℕ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (Q R : ℕ → HeightOneSpectrum (𝓞 K)) (z : ℕ → Kˣ),
      IsTwoPlaceFamily Ω p Tr Tn (spreadClasses Tp cl) d S Q R z := by
  refine exists_isTwoPlaceFamily_zpowers (Ω := Ω) hp hodd hζ hres hTr (Finset.Subset.refl Tn)
    hTrst hTnst hpTn hrepr ?_ hg ?_ ?_ ?_ hDgal ?_ ?_ hram d
  · intro t v _ hvTr
    rw [spreadClasses_of_notMem (fun hc => hvTr (hTp hc)) t]
    exact Subgroup.one_mem _
  · intro t v hv
    by_cases hvp : v ∈ Tp
    · rw [spreadClasses_of_mem hvp t]
      exact hgcl t ⟨v, hvp⟩
    · rw [spreadClasses_of_notMem hvp t, hg1 t v hv hvp]
  · exact fun _ v hv hv' => absurd hv hv'
  · intro t v _ hvp
    by_cases hvT : v ∈ Tp
    · rw [spreadClasses_of_mem hvT t]
      exact hcln ⟨v, hvT⟩ t hvp
    · exact spreadClasses_of_notMem hvT t
  · intro t v _
    by_cases hvT : v ∈ Tp
    · rw [spreadClasses_of_mem hvT t]
      exact hDcl ⟨v, hvT⟩ t
    · rw [spreadClasses_of_notMem hvT t]
      exact Subgroup.one_mem _
  · exact fun v hv hv' => absurd hv hv'

variable (Ω) in
/-- **A naming orthogonal to the `S`-units which are local powers at the infinite places has a
two-place family.**  Orthogonality under the product of the norm residue symbols is exactly what
makes the naming the local behaviour of a global `S`-unit, one coordinate at a time, and the
two-place construction turns that family of `S`-units into the family the coordinates are read
from. -/
theorem exists_isTwoPlaceFamily_named (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {Tp Tr Tn : Finset (HeightOneSpectrum (𝓞 K))} (hTp : Tp ⊆ Tr) (hTr : Tr ⊆ Tn)
    (hTrst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tr → σ • v ∈ Tr)
    (hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {cl : (w : ↥Tp) → ℕ → localClasses (w : HeightOneSpectrum (𝓞 K)) p}
    (hcln : ∀ (w : ↥Tp) (t : ℕ),
      FinitePlace.mk (w : HeightOneSpectrum (𝓞 K)) ((p : ℕ) : K) ≠ 1 → cl w t = 1)
    {D : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hDgal : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
      Subgroup.zpowers (D (σ • v)) = Subgroup.zpowers (localClassesGalEquiv σ v p (D v)))
    (hDcl : ∀ (w : ↥Tp) (t : ℕ),
      cl w t ∈ Subgroup.zpowers (D (w : HeightOneSpectrum (𝓞 K))))
    (hortho : ∀ (t : ℕ)
      (u : ↥(sUnits K (Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))))),
      (∀ w : InfinitePlace K, infClassHom w p ((u : Kˣ)) = 1) →
      localSymbolPiPairing hres hζ (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))
        (sUnitClassHom (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K)) p u)
        (fun y => spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 K))) = 1)
    (hram : ∀ v ∉ Tn, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1) (d : ℕ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (Q R : ℕ → HeightOneSpectrum (𝓞 K)) (z : ℕ → Kˣ),
      IsTwoPlaceFamily Ω p Tr Tn (spreadClasses Tp cl) d S Q R z := by
  classical
  have hrange : Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))
      = (Tn : Set (HeightOneSpectrum (𝓞 K))) := by
    rw [Subtype.range_coe_subtype]
    exact Finset.setOf_mem
  have hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 →
      v ∈ Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K)) := by
    intro v hv
    rw [hrange]
    exact hpTn v hv
  have hrepr' : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K)),
        Rigidity.RET.ord K v (a : K) = m v := by
    intro m hm
    obtain ⟨a, ha⟩ := hrepr m hm
    exact ⟨a, fun v hv => ha v (by rwa [hrange] at hv)⟩
  have hex : ∀ t : ℕ, ∃ u : Kˣ, u ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))) ∧
      ∀ w ∈ Tn, localClassHom w p u = spreadClasses Tp cl t w := by
    intro t
    obtain ⟨u, hu⟩ := exists_sUnit_forall_localClassHom_eq hp hres hζ
      (ι := (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 K))) Subtype.val_injective hnι hrepr'
      (c := fun y => spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 K))) (hortho t)
    refine ⟨(u : Kˣ), ?_, fun w hw => hu ⟨w, hw⟩⟩
    rw [← hrange]
    exact u.2
  choose g hgS hgloc using hex
  refine exists_isTwoPlaceFamily_named_of_sUnits Ω hp hodd hζ hres hTp hTr hTrst hTnst hpTn hrepr
    hcln hDgal hDcl hgS ?_ ?_ hram d
  · intro t w
    have h := hgloc t (w : HeightOneSpectrum (𝓞 K)) (hTr (hTp w.2))
    rw [spreadClasses_of_mem w.2 t] at h
    exact h.symm
  · intro t w hw hwp
    rw [hgloc t w hw]
    exact spreadClasses_of_notMem hwp t

end Named

end InverseGalois.CFT

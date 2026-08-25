/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.InfiniteFamily
import InverseGalois.CFT.Local.UnramifiedCoboundary
import InverseGalois.CFT.Tate.FamilyCoboundary
import InverseGalois.CFT.Units.AdicSIdeles
import InverseGalois.CFT.Units.Idele
import InverseGalois.CFT.Units.IdeleNorm

/-!
# Two-cocycles of the ideles are coboundaries when they are locally so

A two-cocycle of the Galois group of an extension of number fields with values in the ideles is
built from a two-cocycle at every place, and the coordinates at the places in one Galois orbit
determine one another.  So a family of local one-cochains, one for each orbit, assembles into a
global one-cochain, provided the resulting family of ideles really is a family of ideles: all but
finitely many of its coordinates must be units of the valuation ring.

That last point is what makes the statement more than bookkeeping.  A place is called good here
when it and all of its Galois translates are unramified over the base field and all the coordinates
of the cocycle there are units.  All but finitely many places are good, because only finitely many
places are ramified and each of the finitely many values of the cocycle is an idele.  At a good
place the decomposition group is cyclic and the completion carries a uniformizer it fixes, so the
local cochain may be taken with values in the units of the valuation ring; the arbitrary local
cochains supplied at the remaining places then only spoil finitely many coordinates.

## Main results

* `InverseGalois.CFT.exists_coboundary_idele`: **a two-cocycle with values in the ideles which is a
  coboundary at every place is a coboundary.**

## Tags

number field, idele, group cohomology, two-cocycle, coboundary, unramified
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

section IdeleCoboundary

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

theorem exists_coboundary_idele {a : Gal(K/k) → Gal(K/k) → ↥(idele K)}
    (ha : ∀ x y z : Gal(K/k),
      ideleAut (k := k) x (a y z) + a x (y * z) = a (x * y) z + a x y)
    (hinf : ∀ w : InfinitePlace K, ∃ c : ↥(stabilizer Gal(K/k) w) → Additive w.Completionˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) w),
        (↑(a s.1 t.1) : FullIdele K).1 w = smulUnitsAut s (c t) - c (s * t) + c s)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        (↑(a s.1 t.1) : FullIdele K).2 v = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ b : Gal(K/k) → ↥(idele K),
      ∀ x y : Gal(K/k), a x y = ideleAut (k := k) x (b y) - b (x * y) + b x := by
  classical
  set F₁ := (infiniteRingFamily (k := k) (K := K)).unitsFamily with hF₁
  set F₂ := (adicRingFamily (k := k) (K := K)).unitsFamily with hF₂
  set f₁ : Gal(K/k) → Gal(K/k) → ∀ w : InfinitePlace K, Additive w.Completionˣ :=
    fun s t => (↑(a s t) : FullIdele K).1 with hf₁def
  set f₂ : Gal(K/k) → Gal(K/k) → ∀ v : HeightOneSpectrum (𝓞 K),
      Additive (v.adicCompletion K)ˣ := fun s t => (↑(a s t) : FullIdele K).2 with hf₂def
  have hacoe : ∀ x y z : Gal(K/k),
      fullIdeleAut (k := k) x (↑(a y z) : FullIdele K) + (↑(a x (y * z)) : FullIdele K)
        = (↑(a (x * y) z) : FullIdele K) + (↑(a x y) : FullIdele K) := by
    intro x y z
    have h := congrArg (fun u : ↥(idele K) => (u : FullIdele K)) (ha x y z)
    simpa using h
  have hf₁ : F₁.IsCocycle₂ f₁ := fun x y z => congrArg Prod.fst (hacoe x y z)
  have hf₂ : F₂.IsCocycle₂ f₂ := fun x y z => congrArg Prod.snd (hacoe x y z)
  -- the archimedean part
  obtain ⟨b₁, hb₁⟩ := FamilyAction.exists_coboundary hf₁ (by
    intro w
    obtain ⟨c, hc⟩ := hinf w
    refine ⟨fun x => if h : x • w = w then c ⟨x, h⟩ else 0, ?_⟩
    intro s t hs ht
    have hst : (s * t) • w = w := by rw [mul_smul, ht, hs]
    simp only [dif_pos ht, dif_pos hst, dif_pos hs]
    rw [transport_infiniteUnitsFamily w s hs]
    exact hc ⟨s, hs⟩ ⟨t, ht⟩)
  -- the places where the cocycle is a unit and the extension is unramified
  set Good₀ : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal ∧ ∀ s t : Gal(K/k), unitVal (f₂ s t v) = 0}
    with hGood₀def
  set Good : Set (HeightOneSpectrum (𝓞 K)) := {v | ∀ g : Gal(K/k), g • v ∈ Good₀} with hGooddef
  have hGood₀fin : Good₀ᶜ.Finite := by
    have h1 : {v : HeightOneSpectrum (𝓞 K) | ¬Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal}.Finite :=
      finite_setOf_not_isUnramifiedAt k
    have h2 : ∀ p : Gal(K/k) × Gal(K/k),
        {v : HeightOneSpectrum (𝓞 K) | unitVal (f₂ p.1 p.2 v) ≠ 0}.Finite := by
      intro p
      have hmem := (a p.1 p.2).2
      rw [mem_idele, Filter.eventually_cofinite] at hmem
      exact hmem
    refine Set.Finite.subset (h1.union (Set.Finite.biUnion
      (Set.finite_univ (α := Gal(K/k) × Gal(K/k))) (fun p _ => h2 p))) ?_
    intro v hv
    by_cases hu : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal
    · have hne : ¬∀ s t : Gal(K/k), unitVal (f₂ s t v) = 0 := fun h => hv ⟨hu, h⟩
      push_neg at hne
      obtain ⟨s, t, hst⟩ := hne
      exact Or.inr (Set.mem_biUnion (Set.mem_univ (s, t)) hst)
    · exact Or.inl hu
  have hGoodfin : Goodᶜ.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_univ (α := Gal(K/k)))
      (fun g _ => hGood₀fin.image (fun u => g⁻¹ • u))) ?_
    intro v hv
    simp only [hGooddef, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hv
    obtain ⟨g, hg⟩ := hv
    exact Set.mem_biUnion (Set.mem_univ g) ⟨g • v, hg, inv_smul_smul g v⟩
  -- the finite part
  obtain ⟨b₂, hb₂, hb₂N⟩ := FamilyAction.exists_coboundary_mem hf₂
    (fun v => (unitVal (A := v.adicCompletion K)).ker)
    (by
      intro g v x hx
      rw [AddMonoidHom.mem_ker] at hx ⊢
      rw [hF₂, unitVal_adicUnitsFamily_map]
      exact hx)
    Good
    (by
      intro g v hv h
      rw [← mul_smul]
      exact hv (h * g))
    (by
      intro s t v hv
      have h1 : v ∈ Good₀ := by simpa using hv 1
      exact AddMonoidHom.mem_ker.2 (h1.2 s t))
    (by
      intro v
      by_cases hv : v ∈ Good
      · have h1 : v ∈ Good₀ := by simpa using hv 1
        obtain ⟨hunr, hu⟩ := h1
        set g₀ : ↥(stabilizer Gal(K/k) v) → ↥(stabilizer Gal(K/k) v) →
            ↥(unitVal (A := v.adicCompletion K)).ker :=
          fun s t => ⟨f₂ s.1 t.1 v, AddMonoidHom.mem_ker.2 (hu s.1 t.1)⟩ with hg₀def
        have hg₀ : ∀ s t u : ↥(stabilizer Gal(K/k) v),
            kerUnitValAutHom (valued_smul_adicCompletion v) s (g₀ t u) + g₀ s (t * u)
              = g₀ (s * t) u + g₀ s t := by
          intro s t u
          refine Subtype.ext ?_
          have h := congrFun (hf₂ s.1 t.1 u.1) v
          rw [Pi.add_apply, Pi.add_apply,
            F₂.familyAut_apply_eq_transport (s.2 : s.1 • v = v) (f₂ t.1 u.1),
            hF₂, transport_adicUnitsFamily v s.1 s.2] at h
          exact h
        obtain ⟨c, hc⟩ := exists_sub_add_eq_adicUnits (k := k) v hunr hg₀
        refine ⟨fun x => if h : x • v = v then
          ((c ⟨x, h⟩ : ↥(unitVal (A := v.adicCompletion K)).ker) :
            Additive (v.adicCompletion K)ˣ) else 0, ?_, ?_⟩
        · intro s t hs ht
          have hst : (s * t) • v = v := by rw [mul_smul, ht, hs]
          simp only [dif_pos ht, dif_pos hst, dif_pos hs]
          rw [hF₂, transport_adicUnitsFamily v s hs]
          have h := congrArg
            (Subtype.val (p := fun x => x ∈ (unitVal (A := v.adicCompletion K)).ker))
            (hc ⟨s, hs⟩ ⟨t, ht⟩)
          simpa using h
        · intro _ x
          by_cases h : x • v = v
          · simp only [dif_pos h]
            exact (c ⟨x, h⟩).2
          · simp only [dif_neg h]
            exact AddSubgroup.zero_mem _
      · obtain ⟨c, hc⟩ := hfin v
        refine ⟨fun x => if h : x • v = v then c ⟨x, h⟩ else 0, ?_, fun h => absurd h hv⟩
        intro s t hs ht
        have hst : (s * t) • v = v := by rw [mul_smul, ht, hs]
        simp only [dif_pos ht, dif_pos hst, dif_pos hs]
        rw [hF₂, transport_adicUnitsFamily v s hs]
        exact hc ⟨s, hs⟩ ⟨t, ht⟩)
  -- the two halves assemble into an idele
  have hmem : ∀ g : Gal(K/k), ((b₁ g, b₂ g) : FullIdele K) ∈ idele K := by
    intro g
    rw [mem_idele, Filter.eventually_cofinite]
    refine hGoodfin.subset fun v hv hvg => hv ?_
    exact AddMonoidHom.mem_ker.1 (hb₂N g v hvg)
  refine ⟨fun g => ⟨(b₁ g, b₂ g), hmem g⟩, fun x y => ?_⟩
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact (hb₁ x y).symm
  · exact (hb₂ x y).symm

end IdeleCoboundary

end InverseGalois.CFT

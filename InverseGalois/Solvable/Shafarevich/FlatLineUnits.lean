/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.CyclicPairing
import InverseGalois.CFT.PoitouTate.GlobalClasses
import InverseGalois.Solvable.Shafarevich.KernelArith

/-!
# The families of units named on an equivariant line of local classes

The two-place construction prescribes the classes of a family of units at finitely many named
places, and it asks the classes prescribed at a place to lie on a line which is carried to the line
at the image of the place by every automorphism of the level.  Naming that line by a global unit
spreads it over an orbit only when the orbit is free: two automorphisms carrying the named place to
the same place would otherwise have to name the same line there.

A demand which names one place in each of finitely many distinct orbits, and says nothing about the
automorphisms fixing a named place, cannot afford that.  What it can afford is a line given at
every place at once and equivariant as a subgroup rather than as an element: no generator has to be
transported, so no orbit has to be free, and the prescription is read off whichever generator is at
hand.  Nothing is asked of the orbits beyond their being distinct, which is what keeps the classes
prescribed at one named place from being read at another.

What the construction still costs is the reciprocity residue: the product of the power residue
symbols of the naming against the units of the level which become exponent-th powers in the
auxiliary field, read over the named places, has to be trivial.  On a line that residue is a purely
local demand at each named place taken on its own, because the product runs over the named places
alone and, at an odd exponent, two powers of one class pair trivially: the classes at a named place
of the units which become exponent-th powers in the auxiliary field are asked to lie on the line
there, and nothing at all is asked anywhere else.

## Main results

* `InverseGalois.Shafarevich.exists_units_line_named` — **classes lying on an equivariant line can
  be prescribed at one place in each of finitely many distinct orbits**, the family being trivial at
  a prescribed finite set of places, at every conjugate of a named place which is not itself named,
  and ramified only over the named places or at places completely decomposed in the auxiliary field.
* `InverseGalois.Shafarevich.exists_units_line_diagonal` — **one unit per named place, ramified at
  its own place and trivial at the others**, which is the diagonal the orders of the confined units
  are read off.
* `InverseGalois.Shafarevich.isNamedOrthogonal_line` — **the reciprocity residue of a naming on a
  line is trivial** as soon as, at each named place, the units of the level which become
  exponent-th powers in the auxiliary field have their classes on that line.
* `InverseGalois.Shafarevich.exists_units_line_diagonal_of_scholz` — **the diagonal, in exchange for
  that local demand at the named places alone.**

## Tags

Shafarevich's theorem, embedding problem, Kummer theory, local class, line, reciprocity
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

section Line

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω]

/-- **Classes lying on an equivariant line can be prescribed at one place in each of finitely many
distinct orbits.**

The named places are read as a finite set and the classes prescribed at them as a family indexed by
that set, the transport along the naming being harmless because places in distinct orbits are
distinct.  The line is given at every place at once and only its subgroup is asked to be carried
along, so nothing has to be spread and the orbits of the named places are free of any further
demand; the finite level the leftover places are asked to be decomposed in serves as the auxiliary
field of the two-place construction.

A conjugate of a named place which is not the place itself is not named, the named places lying in
distinct orbits, so the family is trivial there; and the reciprocity residue is the orthogonality
of the naming read at the finite set of places the units are supported at, the prescription being
trivial away from the named places and the product of the symbols collapsing to them. -/
theorem exists_units_line_named {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hodd : 2 < ℓ)
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
    {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (E : IntermediateField k Ω)
    (hEfin : FiniteDimensional k ↥E) (hEgal : IsGalois k ↥E) (hKE : K ≤ E)
    {D : (v : HeightOneSpectrum (𝓞 ↥K)) → localClasses v ℓ}
    (hDgal : ∀ (σ : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)),
      Subgroup.zpowers (D (σ • v)) = Subgroup.zpowers (localClassesGalEquiv σ v ℓ (D v)))
    {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K))
    (hdist : ∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν)
    (Tz : Finset (HeightOneSpectrum (𝓞 ↥K))) (hTz : ∀ μ : ι, w μ ∉ Tz)
    (hℓw : ∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal)
    {d : ℕ} (c : (μ : ι) → Fin d → localClasses (w μ) ℓ)
    (hline : ∀ (μ : ι) (q : Fin d), c μ q ∈ Subgroup.zpowers (D (w μ)))
    (hnorth : IsNamedOrthogonal ℓ K hres hζ E w c) :
    ∃ z : Fin d → (↥K)ˣ,
      (∀ (q : Fin d) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → localClassHom v ℓ (z q) = 1) ∧
      (∀ (μ : ι) (q : Fin d), localClassHom (w μ) ℓ (z q) = c μ q) ∧
      (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ≠ w μ →
        ∀ q : Fin d, localClassHom (σ • w μ) ℓ (z q) = 1) ∧
      ∀ v : HeightOneSpectrum (𝓞 ↥K), (∃ q : Fin d, ¬ (ℓ : ℤ) ∣ placeValue v (z q)) →
        (∃ (μ : ι) (σ : Gal(↥K/k)), v = σ • w μ) ∨
          ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
            stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup := by
  classical
  haveI := hEfin
  haveI := hEgal
  -- the finite level the leftover places are asked to be decomposed in
  haveI : NumberField ↥E := NumberField.of_module_finite k ↥E
  letI : Algebra ↥K ↥E := inferInstanceAs (Algebra ↥K ↥(extendScalars hKE))
  haveI : IsScalarTower k ↥K ↥E := inferInstanceAs (IsScalarTower k ↥K ↥(extendScalars hKE))
  haveI : IsScalarTower ↥K ↥E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois ↥K ↥E := IsGalois.tower_top_of_isGalois k ↥K ↥E
  have hwinj : Function.Injective w := by
    intro μ ν h
    by_contra hne
    exact hdist μ ν hne 1 (by rw [one_smul]; exact h)
  -- the named places, read as a finite set
  obtain ⟨Tp, hTpdef⟩ : ∃ Tp : Finset (HeightOneSpectrum (𝓞 ↥K)),
      Tp = Finset.image w Finset.univ := ⟨_, rfl⟩
  have hmemTp : ∀ μ : ι, w μ ∈ Tp := by
    intro μ
    rw [hTpdef]
    exact Finset.mem_image.2 ⟨μ, Finset.mem_univ μ, rfl⟩
  have hmem : ∀ v ∈ Tp, ∃ μ : ι, w μ = v := by
    intro v hv
    rw [hTpdef] at hv
    obtain ⟨μ, -, hμ⟩ := Finset.mem_image.1 hv
    exact ⟨μ, hμ⟩
  have hex : ∀ x : ↥Tp, ∃ μ : ι, w μ = (x : HeightOneSpectrum (𝓞 ↥K)) := fun x => hmem _ x.2
  choose idx hidx using hex
  -- the prescribed classes, read at the finite set
  have htr : ∀ (ν μ : ι) (h : w ν = w μ) (q : Fin d),
      cast (congrArg (fun v => localClasses v ℓ) h) (c ν q) = c μ q := by
    intro ν μ h q
    obtain rfl : ν = μ := hwinj h
    rfl
  obtain ⟨cl, hcldef⟩ : ∃ cl : (x : ↥Tp) → ℕ → localClasses (x : HeightOneSpectrum (𝓞 ↥K)) ℓ,
      cl = fun x t => if h : t < d then
        cast (congrArg (fun v => localClasses v ℓ) (hidx x)) (c (idx x) ⟨t, h⟩) else 1 :=
    ⟨_, rfl⟩
  have hclval : ∀ (μ : ι) (hwm : w μ ∈ Tp) (q : Fin d),
      cl ⟨w μ, hwm⟩ (q : ℕ) = c μ q := by
    intro μ hwm q
    rw [hcldef]
    simp only [dif_pos q.isLt]
    exact htr (idx ⟨w μ, hwm⟩) μ (hidx ⟨w μ, hwm⟩) q
  have hcltop : ∀ (x : ↥Tp) (t : ℕ), ¬ t < d → cl x t = 1 := by
    intro x t ht
    rw [hcldef]
    simp only [dif_neg ht]
  -- the classes lie on the line
  have hDcl : ∀ (x : ↥Tp) (t : ℕ),
      cl x t ∈ Subgroup.zpowers (D (x : HeightOneSpectrum (𝓞 ↥K))) := by
    intro x t
    by_cases h : t < d
    · rw [hcldef]
      simp only [dif_pos h]
      have hgen : ∀ (v : HeightOneSpectrum (𝓞 ↥K)) (hv : w (idx x) = v),
          cast (congrArg (fun v => localClasses v ℓ) hv) (c (idx x) ⟨t, h⟩)
            ∈ Subgroup.zpowers (D v) := by
        intro v hv
        subst hv
        exact hline (idx x) ⟨t, h⟩
      exact hgen _ (hidx x)
    · rw [hcldef]
      simp only [dif_neg h]
      exact Subgroup.one_mem _
  have hcln : ∀ (x : ↥Tp) (t : ℕ),
      FinitePlace.mk (x : HeightOneSpectrum (𝓞 ↥K)) ((ℓ : ℕ) : ↥K) ≠ 1 → cl x t = 1 := by
    intro x t hne
    refine absurd ((finitePlace_natCast_eq_one_iff _ ℓ).2 ?_) hne
    rw [← hidx x]
    exact hℓw (idx x)
  have hdisj : ∀ v ∈ Tp, v ∉ Tz := by
    intro v hv
    rw [hTpdef] at hv
    obtain ⟨μ, -, rfl⟩ := Finset.mem_image.1 hv
    exact hTz μ
  obtain ⟨Tram, hTram⟩ := exists_finset_forall_ramIdx_eq_one ↥K ↥E
  -- the reciprocity residue, read off the orthogonality of the naming
  have horth : ∀ Tn : Finset (HeightOneSpectrum (𝓞 ↥K)), Tp ⊆ Tn → ∀ (t : ℕ)
      (u : ↥(sUnits ↥K (Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 ↥K))))),
      (∀ y : InfinitePlace ↥K, infClassHom y ℓ ((u : (↥K)ˣ)) = 1) →
      (∃ y : (↥E)ˣ, Units.map (algebraMap ↥K ↥E : ↥K →* ↥E) ((u : (↥K)ˣ)) = y ^ ℓ) →
      localSymbolPiPairing hres hζ (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 ↥K))
        (sUnitClassHom (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 ↥K)) ℓ u)
        (fun y => spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 ↥K))) = 1 := by
    intro Tn hsub t u hinf hpow
    by_cases ht : t < d
    · have hpowE : ∃ y : Ω, y ∈ E ∧ y ^ ℓ = algebraMap ↥K Ω (((u : (↥K)ˣ) : ↥K)) := by
        obtain ⟨y, hy⟩ := hpow
        refine ⟨((y : ↥E) : Ω), (y : ↥E).2, ?_⟩
        have hval : algebraMap ↥K ↥E ((u : (↥K)ˣ) : ↥K) = ((y : ↥E)) ^ ℓ := by
          simpa using congrArg Units.val hy
        have hcoe : ((algebraMap ↥K ↥E ((u : (↥K)ˣ) : ↥K) : ↥E) : Ω) = (((y : ↥E) : Ω)) ^ ℓ := by
          rw [hval]
          push_cast
          ring
        rw [← hcoe, IsScalarTower.algebraMap_apply ↥K ↥E Ω]
        rfl
      have hkey := hnorth Tn (fun μ => hsub (hmemTp μ)) ⟨t, ht⟩ u hinf hpowE
      have hfun : (fun μ : ι => spreadClasses Tp cl t (w μ))
          = fun μ : ι => c μ ⟨t, ht⟩ := by
        refine funext fun μ => ?_
        rw [spreadClasses_of_mem (hmemTp μ) t]
        exact hclval μ (hmemTp μ) ⟨t, ht⟩
      have hkey' : localSymbolPiPairing hres hζ w (fun μ => localClassHom (w μ) ℓ ((u : (↥K)ˣ)))
          (fun μ => spreadClasses Tp cl t (w μ)) = 1 := by
        rw [hfun]
        exact hkey
      have he : Function.Injective (fun μ : ι => (⟨w μ, hsub (hmemTp μ)⟩ : ↥Tn)) :=
        fun μ ν h => hwinj (congrArg Subtype.val h)
      have hb : ∀ y : ↥Tn, (∀ μ : ι, (⟨w μ, hsub (hmemTp μ)⟩ : ↥Tn) ≠ y) →
          spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 ↥K)) = 1 := by
        intro y hy
        refine spreadClasses_of_notMem (fun hc => ?_) t
        obtain ⟨μ, hμ⟩ := hmem _ hc
        exact hy μ (Subtype.ext hμ)
      exact Eq.trans (piPairing_eq_of_support _ he _ _ hb) hkey'
    · have hfun : (fun y : ↥Tn => spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 ↥K))) = 1 := by
        refine funext fun y => ?_
        show spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 ↥K)) = 1
        by_cases hy : (y : HeightOneSpectrum (𝓞 ↥K)) ∈ Tp
        · rw [spreadClasses_of_mem hy t, hcltop ⟨_, hy⟩ t ht]
        · exact spreadClasses_of_notMem hy t
      rw [hfun]
      exact _root_.map_one _
  obtain ⟨z, hz1, hz2, hz3, hz4⟩ := exists_units_named_prescribed (k := k) (A := Ω) (K := ↥K)
    (Ω := E) (p := ℓ) hℓ hodd hζ hres (Tp := Tp) (Tz := Tz) (Tram := Tram) hdisj hTram
    (cl := cl) hcln (D := D) hDgal hDcl horth d
  refine ⟨fun q => z (q : ℕ), fun q v hv => hz1 q q.isLt v hv, ?_, ?_, ?_⟩
  · intro μ q
    rw [hz2 q q.isLt ⟨w μ, hmemTp μ⟩]
    exact hclval μ (hmemTp μ) q
  · intro μ σ hσ q
    refine hz3 q q.isLt σ ⟨w μ, hmemTp μ⟩ fun hcon => ?_
    obtain ⟨ν, hν⟩ := hmem _ hcon
    rcases eq_or_ne ν μ with rfl | hne
    · exact hσ hν.symm
    · exact hdist μ ν (Ne.symm hne) σ hν.symm
  · intro v hv
    obtain ⟨q, hq⟩ := hv
    rcases hz4 v ⟨q, q.isLt, hq⟩ with ⟨σ, x, hvx⟩ | ⟨⟨W', hW'u, hW'st⟩, -, -⟩
    · exact Or.inl ⟨idx x, σ, by rw [hidx x]; exact hvx⟩
    · refine Or.inr ?_
      intro P hPp hPbot hPu
      haveI := hPp
      refine stabilizer_le_fixingSubgroup_of_stabilizer_eq_bot hW'st hPbot ?_
      have h1 : Ideal.under (𝓞 k) P = Ideal.under (𝓞 k) v.asIdeal := by
        rw [← hPu, Ideal.under_under]
      have h2 : Ideal.under (𝓞 k) W'.asIdeal = Ideal.under (𝓞 k) v.asIdeal := by
        rw [← Ideal.under_under (A := 𝓞 k) (B := 𝓞 ↥K) W'.asIdeal, ← primeUnder_asIdeal, hW'u]
      rw [h1, h2]

/-- **One unit per named place, ramified at its own place and trivial at the others.**

The classes prescribed are a diagonal on the line: in the coordinate belonging to a named place the
class there is the line and the class at every other named place is trivial.  The line at a named
place is asked to be ramified, so the unit of that coordinate is ramified at its own place; at any
other place of the orbit of a named place the class is trivial, the place either being the named
one — where the diagonal is trivial off its own coordinate — or not named at all. -/
theorem exists_units_line_diagonal {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hodd : 2 < ℓ)
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
    {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (E : IntermediateField k Ω)
    (hEfin : FiniteDimensional k ↥E) (hEgal : IsGalois k ↥E) (hKE : K ≤ E)
    {D : (v : HeightOneSpectrum (𝓞 ↥K)) → localClasses v ℓ}
    (hDgal : ∀ (σ : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)),
      Subgroup.zpowers (D (σ • v)) = Subgroup.zpowers (localClassesGalEquiv σ v ℓ (D v)))
    {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K))
    (hdist : ∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν)
    (Tz : Finset (HeightOneSpectrum (𝓞 ↥K))) (hTz : ∀ μ : ι, w μ ∉ Tz)
    (hℓw : ∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal)
    (hDram : ∀ (μ : ι) (a : (↥K)ˣ), localClassHom (w μ) ℓ a = D (w μ) →
      ¬ (ℓ : ℤ) ∣ placeValue (w μ) a)
    (e : ι ≃ Fin (Fintype.card ι))
    (hnorth : IsNamedOrthogonal ℓ K hres hζ E w
      (fun μ q => if e μ = q then D (w μ) else 1)) :
    ∃ Z : ι → (↥K)ˣ,
      (∀ μ : ι, ¬ (ℓ : ℤ) ∣ placeValue (w μ) (Z μ)) ∧
      (∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → localClassHom v ℓ (Z μ) = 1) ∧
      (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ≠ w μ → localClassHom (σ • w μ) ℓ (Z μ) = 1) ∧
      (∀ μ ν : ι, ν ≠ μ → ∀ σ : Gal(↥K/k), localClassHom (σ • w ν) ℓ (Z μ) = 1) ∧
      ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), ¬ (ℓ : ℤ) ∣ placeValue v (Z μ) →
        (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
          ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
            stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup := by
  classical
  have hline : ∀ (μ : ι) (q : Fin (Fintype.card ι)),
      (if e μ = q then D (w μ) else 1) ∈ Subgroup.zpowers (D (w μ)) := by
    intro μ q
    by_cases h : e μ = q
    · rw [if_pos h]
      exact Subgroup.mem_zpowers _
    · rw [if_neg h]
      exact Subgroup.one_mem _
  obtain ⟨z, hz1, hz2, hz3, hz4⟩ := exists_units_line_named hℓ hodd K hres hζ E hEfin
    hEgal hKE hDgal w hdist Tz hTz hℓw _ hline hnorth
  refine ⟨fun μ => z (e μ), fun μ => ?_, fun μ v hv => hz1 (e μ) v hv,
    fun μ σ hσ => hz3 μ σ hσ (e μ), fun μ ν hνμ σ => ?_, fun μ v hv => ?_⟩
  · refine hDram μ (z (e μ)) ?_
    rw [hz2 μ (e μ), if_pos rfl]
  · by_cases hσν : σ • w ν = w ν
    · rw [hσν, hz2 ν (e μ), if_neg fun hcon => hνμ (e.injective hcon)]
    · exact hz3 ν σ hσν (e μ)
  · exact hz4 v ⟨e μ, hv⟩

/-! ### The reciprocity residue of a naming on a line -/

omit [NumberField k] [IsGalois k Ω] [IsAlgClosed Ω] in
/-- **A naming on a line is orthogonal to the units of the level which become exponent-th powers in
the auxiliary field**, as soon as the classes of those units at the named places lie on that line
too.

The product of the symbols runs over the named places alone, and at each of them both arguments are
powers of one class; at an odd exponent a class pairs trivially with itself, so every factor of the
product is trivial.  What is asked of a named place is local and says nothing whatever about the
other named places, nor about any place the naming is not made at. -/
theorem isNamedOrthogonal_line {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hodd : 2 < ℓ)
    (K : IntermediateField k Ω) [NumberField ↥K]
    {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (E : IntermediateField k Ω)
    {D : (v : HeightOneSpectrum (𝓞 ↥K)) → localClasses v ℓ}
    {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K)) {d : ℕ}
    {c : (μ : ι) → Fin d → localClasses (w μ) ℓ}
    (hline : ∀ (μ : ι) (q : Fin d), c μ q ∈ Subgroup.zpowers (D (w μ)))
    (hscholz : ∀ (μ : ι) (u : (↥K)ˣ), (∃ y : Ω, y ∈ E ∧ y ^ ℓ = algebraMap ↥K Ω ((u : ↥K))) →
      localClassHom (w μ) ℓ u ∈ Subgroup.zpowers (D (w μ))) :
    IsNamedOrthogonal ℓ K hres hζ E w c := by
  have hoddℓ : Odd ℓ := hℓ.odd_of_ne_two (by omega)
  intro Tn _ q u _ hpow
  rw [localSymbolPiPairing_eq_piPairing, piPairing_apply]
  exact Finset.prod_eq_one fun μ _ =>
    localClassPairing_eq_one_of_mem_zpowers hres hζ (w μ) (isNegOnePow_of_odd hoddℓ)
      (hscholz μ ((u : (↥K)ˣ)) hpow) (hline μ q)

/-- **One unit per named place, ramified at its own place and trivial at the others, in exchange
for a local demand at the named places alone.**

The naming is the diagonal on the line, so the reciprocity residue is read off the line: at each
named place the classes of the units of the level which become exponent-th powers in the auxiliary
field are asked to lie on the line there, and nothing at all is asked anywhere else. -/
theorem exists_units_line_diagonal_of_scholz {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    (hodd : 2 < ℓ) (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K]
    [NumberField ↥K] {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (E : IntermediateField k Ω)
    (hEfin : FiniteDimensional k ↥E) (hEgal : IsGalois k ↥E) (hKE : K ≤ E)
    {D : (v : HeightOneSpectrum (𝓞 ↥K)) → localClasses v ℓ}
    (hDgal : ∀ (σ : Gal(↥K/k)) (v : HeightOneSpectrum (𝓞 ↥K)),
      Subgroup.zpowers (D (σ • v)) = Subgroup.zpowers (localClassesGalEquiv σ v ℓ (D v)))
    {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 ↥K))
    (hdist : ∀ μ ν : ι, μ ≠ ν → ∀ σ : Gal(↥K/k), σ • w μ ≠ w ν)
    (Tz : Finset (HeightOneSpectrum (𝓞 ↥K))) (hTz : ∀ μ : ι, w μ ∉ Tz)
    (hℓw : ∀ μ : ι, (ℓ : 𝓞 ↥K) ∉ (w μ).asIdeal)
    (hDram : ∀ (μ : ι) (a : (↥K)ˣ), localClassHom (w μ) ℓ a = D (w μ) →
      ¬ (ℓ : ℤ) ∣ placeValue (w μ) a)
    (hscholz : ∀ (μ : ι) (u : (↥K)ˣ), (∃ y : Ω, y ∈ E ∧ y ^ ℓ = algebraMap ↥K Ω ((u : ↥K))) →
      localClassHom (w μ) ℓ u ∈ Subgroup.zpowers (D (w μ))) :
    ∃ Z : ι → (↥K)ˣ,
      (∀ μ : ι, ¬ (ℓ : ℤ) ∣ placeValue (w μ) (Z μ)) ∧
      (∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), v ∈ Tz → localClassHom v ℓ (Z μ) = 1) ∧
      (∀ (μ : ι) (σ : Gal(↥K/k)), σ • w μ ≠ w μ → localClassHom (σ • w μ) ℓ (Z μ) = 1) ∧
      (∀ μ ν : ι, ν ≠ μ → ∀ σ : Gal(↥K/k), localClassHom (σ • w ν) ℓ (Z μ) = 1) ∧
      ∀ (μ : ι) (v : HeightOneSpectrum (𝓞 ↥K)), ¬ (ℓ : ℤ) ∣ placeValue v (Z μ) →
        (∃ (ν : ι) (σ : Gal(↥K/k)), v = σ • w ν) ∨
          ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
            stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup := by
  classical
  refine exists_units_line_diagonal hℓ hodd K hres hζ E hEfin hEgal hKE hDgal w hdist Tz hTz
    hℓw hDram (Fintype.equivFin ι)
    (isNamedOrthogonal_line hℓ hodd K hres hζ E w ?_ hscholz)
  intro μ q
  by_cases h : Fintype.equivFin ι μ = q
  · rw [if_pos h]
    exact Subgroup.mem_zpowers _
  · rw [if_neg h]
    exact Subgroup.one_mem _

end Line

end InverseGalois.Shafarevich

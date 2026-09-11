/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.NamedUnits
import InverseGalois.CFT.PoitouTate.OrbitLine
import InverseGalois.Solvable.Shafarevich.KernelPlaces

/-!
# The families of units the prescription is made of, bought from the arithmetic

The whole prescription over the field the base realization cuts out was reduced to a single
statement about that level: name finitely many places lying in distinct orbits, prescribe a class
at each of them in each coordinate, and ask for a family of units of the level carrying those
classes, dying at the proper conjugates of the named places and at a further prescribed finite set
of places, and confined everywhere else to places sitting over a named one or completely decomposed
in a given finite level.  That is exactly the shape the two-place construction over a number field
answers, and this file matches the two.

Setting the bookkeeping up is a matter of reading the named places as a finite set of places, the
prescribed classes as a family indexed by that finite set, and the lines the classes at one place
lie on as a family spread over the orbits of the named places, so that the line at the image of a
place is the image of the line there.  The finite level the leftover places are asked to be
decomposed in serves as the auxiliary field of the two-place construction, which is what its being
Galois over the base is for; the decomposition group of a prime of that level lands in the one of
the prime below it.  The places ramified in it are finitely many, because a place ramifies exactly
when the prime below it divides the different and a nonzero ideal has finitely many prime divisors.

What the construction asks for beyond the bookkeeping is the reciprocity residue, and that is
exactly the orthogonality the demand carries along with it.  The product of the power residue
symbols over all the places of a global unit against the spread prescription runs over a finite set
of places containing the named ones; away from the named places the spread prescription is trivial,
so the product collapses to the named places, which is the orthogonality of the naming.  In a
coordinate beyond the ones prescribed the spread prescription is trivial everywhere and the product
is empty of content.

## Main results

* `InverseGalois.Shafarevich.exists_finset_forall_ramIdx_eq_one` — **outside a finite set of places
  every place of a number field has an unramified prime above it in a finite extension.**
* `InverseGalois.Shafarevich.exists_prime_natCast_mem_asIdeal` — **every finite place lies above a
  rational prime**, its residue characteristic.
* `InverseGalois.Shafarevich.stabilizer_le_fixingSubgroup_of_stabilizer_eq_bot` — **a prime of the
  closure lying over a place with trivial decomposition group in a finite level has its whole
  decomposition group fixing that level.**
* `InverseGalois.Shafarevich.piPairing_eq_of_support` — **a pairing read against a family supported
  at the image of an injection is the pairing over the source of that injection.**
* `InverseGalois.Shafarevich.hasPrescribedUnits` — **every level carries the families of units the
  prescription is made of.**

## Tags

Shafarevich's theorem, embedding problem, power residue symbol, reciprocity, Kummer theory
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

/-! ### The places ramified in a finite extension -/

section Ramified

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/-- **Outside a finite set of places every place of a number field has an unramified prime above it
in a finite extension.**  A prime above a place is unramified exactly when it does not divide the
different, the different is nonzero, and a nonzero ideal has finitely many prime divisors. -/
theorem exists_finset_forall_ramIdx_eq_one (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ T,
      ∃ W : HeightOneSpectrum (𝓞 L), primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1 := by
  classical
  have hD : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))
  have hfin : {W : HeightOneSpectrum (𝓞 L) | W.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L)}.Finite :=
    Ideal.finite_factors hD
  refine ⟨hfin.toFinset.image (fun W => primeUnder (𝓞 K) W), ?_⟩
  intro v hv
  obtain ⟨W, hW⟩ := exists_primeUnder_eq (𝓞 K) (𝓞 L) v
  refine ⟨W, hW, ?_⟩
  have hnd : ¬ W.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    intro hdvd
    exact hv (Finset.mem_image.2 ⟨W, hfin.mem_toFinset.2 hdvd, hW⟩)
  haveI : W.asIdeal.IsPrime := W.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := not_dvd_differentIdeal_iff.1 hnd
  exact ramIdx_eq_one_of_isUnramifiedAt W

/-- **Every finite place lies above a rational prime**, the characteristic of its residue field.
The residue field is a finite field, so its characteristic is a prime, and a natural number is
zero in the residue field exactly when it lies in the place. -/
theorem exists_prime_natCast_mem_asIdeal (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  haveI := v.isPrime
  haveI : v.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal v.isPrime v.ne_bot
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := inferInstance
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  refine ⟨ringChar (𝓞 K ⧸ v.asIdeal), ?_, ?_⟩
  · haveI : CharP (𝓞 K ⧸ v.asIdeal) (ringChar (𝓞 K ⧸ v.asIdeal)) := ringChar.charP _
    exact CharP.char_is_prime (𝓞 K ⧸ v.asIdeal) (ringChar (𝓞 K ⧸ v.asIdeal))
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (ringChar.spec _ _).2 dvd_rfl

end Ramified

/-! ### The decomposition group of a prime over a decomposed place -/

section Decomposition

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

/-- **A prime of the closure lying over a place with trivial decomposition group in a finite level
has its whole decomposition group fixing that level.**  The place below the prime and the place
with trivial decomposition group lie over the same place of the base, so they are conjugate, and
conjugate places have conjugate decomposition groups. -/
theorem stabilizer_le_fixingSubgroup_of_stabilizer_eq_bot {W : IntermediateField k Ω}
    [NumberField ↥W] [FiniteDimensional k ↥W] [IsGalois k ↥W]
    {W' : HeightOneSpectrum (𝓞 ↥W)} (hW' : stabilizer Gal(↥W/k) W' = ⊥)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥)
    (hPu : Ideal.under (𝓞 k) P = Ideal.under (𝓞 k) W'.asIdeal) :
    stabilizer Gal(Ω/k) P ≤ W.fixingSubgroup := by
  classical
  have hunder : primeUnder (𝓞 k) W' = primeUnder (𝓞 k) (placeUnder W P hP) := by
    refine HeightOneSpectrum.ext ?_
    rw [primeUnder_asIdeal, primeUnder_asIdeal, placeUnder_asIdeal, Ideal.under_under, hPu]
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_primeUnder_eq (A := 𝓞 k) (G := Gal(↥W/k)) hunder
  have hst : stabilizer Gal(↥W/k) (placeUnder W P hP) = ⊥ := by
    rw [← hτ, MulAction.stabilizer_smul_eq_stabilizer_map_conj, hW']
    exact Subgroup.map_bot _
  rw [← IntermediateField.restrictNormalHom_ker W]
  exact stabilizer_le_ker_of_stabilizer_placeUnder_eq_bot
    (φ := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥W)
    (IntermediateField.restrictNormalHom_ker W).symm hP hst

end Decomposition

/-! ### A pairing read against a family named at finitely many places -/

section Support

/-- **A pairing on a product of groups, read against a family supported at the image of an
injection, is the pairing over the source of that injection.**  The factors outside the image
contribute nothing, the pairing being a homomorphism in its second variable. -/
theorem piPairing_eq_of_support {Y ι : Type*} [Fintype Y] [Fintype ι] {A : Y → Type*}
    [∀ y, CommGroup (A y)] {M : Type*} [CommGroup M] (φ : ∀ y, A y →* A y →* M) {e : ι → Y}
    (he : Function.Injective e) (a b : ∀ y, A y)
    (hb : ∀ y : Y, (∀ μ : ι, e μ ≠ y) → b y = 1) :
    piPairing φ a b = piPairing (fun μ => φ (e μ)) (fun μ => a (e μ)) (fun μ => b (e μ)) := by
  classical
  simp only [piPairing_apply]
  have h1 : ∀ y ∈ (Finset.univ : Finset Y), y ∉ Finset.image e Finset.univ →
      φ y (a y) (b y) = 1 := by
    intro y _ hy
    rw [hb y fun μ hμ => hy (Finset.mem_image.2 ⟨μ, Finset.mem_univ μ, hμ⟩), _root_.map_one]
  rw [← Finset.prod_subset (Finset.subset_univ _) h1,
    Finset.prod_image fun _ _ _ _ h => he h]

end Support

/-! ### The families of units -/

section Pairing

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω]

/-- **Every level carries the families of units the prescription is made of.**

The named places are read as a finite set of places and the classes prescribed at them as a family
indexed by that set, the transport along the naming being harmless because the naming is injective.
The lines the classes lie on are named by units of the level, which lets them be spread over the
orbits of the named places, and the finite level the leftover places are asked to be decomposed in
serves as the auxiliary field of the two-place construction, which is what its being Galois over the
base is for.  With that bookkeeping the two-place construction produces the family of units, and
each of the four clauses of the demand is one of its four conclusions read back through the naming.

The reciprocity residue the construction asks for is the orthogonality of the naming, read at the
finite set of places the units are supported at: away from the named places the spread prescription
is trivial, so the product of the symbols collapses to the named ones.  In a coordinate beyond the
ones prescribed the spread prescription is trivial everywhere and the product is empty. -/
theorem hasPrescribedUnits {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hodd : 2 < ℓ)
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
    {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) :
    HasPrescribedUnits ℓ K hres hζ := by
  classical
  intro E hEfin hEgal hKE ι _ w hwinj hwconj Tz hTz hℓw d c hline hnorth
  haveI := hEfin
  haveI := hEgal
  -- the finite level the leftover places are asked to be decomposed in
  haveI : NumberField ↥E := NumberField.of_module_finite k ↥E
  letI : Algebra ↥K ↥E := inferInstanceAs (Algebra ↥K ↥(extendScalars hKE))
  haveI : IsScalarTower k ↥K ↥E := inferInstanceAs (IsScalarTower k ↥K ↥(extendScalars hKE))
  haveI : IsScalarTower ↥K ↥E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois ↥K ↥E := IsGalois.tower_top_of_isGalois k ↥K ↥E
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
  -- the lines the classes at the named places lie on
  choose aU haU using hline
  obtain ⟨a, hadef⟩ : ∃ a : ↥Tp → (↥K)ˣ, a = fun x => aU (idx x) := ⟨_, rfl⟩
  have hfree : ∀ σ : Gal(↥K/k), σ ≠ 1 → ∀ x ∈ Tp, σ • x ∉ Tp := by
    intro σ hσ x hx hcon
    rw [hTpdef] at hx hcon
    obtain ⟨μ, -, hμ⟩ := Finset.mem_image.1 hx
    obtain ⟨ν, -, hν⟩ := Finset.mem_image.1 hcon
    exact hwconj μ ν σ hσ (by rw [hμ, hν])
  have hDcl : ∀ (x : ↥Tp) (t : ℕ),
      cl x t ∈ Subgroup.zpowers (orbitLine k Tp a ℓ (x : HeightOneSpectrum (𝓞 ↥K))) := by
    intro x t
    rw [orbitLine_mem hfree]
    by_cases h : t < d
    · rw [hcldef]
      simp only [dif_pos h]
      have hgen : ∀ (v : HeightOneSpectrum (𝓞 ↥K)) (hv : w (idx x) = v),
          cast (congrArg (fun v => localClasses v ℓ) hv) (c (idx x) ⟨t, h⟩)
            ∈ Subgroup.zpowers (localClassHom v ℓ (a x)) := by
        intro v hv
        subst hv
        rw [hadef]
        simpa using haU (idx x) ⟨t, h⟩
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
    (cl := cl) hfree hcln (D := orbitLine k Tp a ℓ) (orbitLine_zpowers_smul hfree a) hDcl horth d
  refine ⟨fun q => z (q : ℕ), fun q v hv => hz1 q q.isLt v hv, ?_, ?_, ?_⟩
  · intro μ q
    rw [hz2 q q.isLt ⟨w μ, hmemTp μ⟩]
    exact hclval μ (hmemTp μ) q
  · intro μ σ hσ q
    exact hz3 q q.isLt σ ⟨w μ, hmemTp μ⟩ hσ
  · intro v hv
    obtain ⟨q, hq⟩ := hv
    rcases hz4 v ⟨q, q.isLt, hq⟩ with ⟨σ, x, hvx⟩ | ⟨⟨W', hW'u, hW'st⟩, ⟨q₀, hq₀d, hq₀⟩, hconj⟩
    · exact Or.inl ⟨idx x, σ, by rw [hidx x]; exact hvx⟩
    · refine Or.inr ⟨?_, ⟨⟨q₀, hq₀d⟩, fun q hqne => hq₀ q q.isLt fun hcon => hqne (Fin.ext hcon)⟩,
        fun σ hσ q => hconj σ hσ q q.isLt⟩
      intro P hPp hPbot hPu
      haveI := hPp
      refine stabilizer_le_fixingSubgroup_of_stabilizer_eq_bot hW'st hPbot ?_
      have h1 : Ideal.under (𝓞 k) P = Ideal.under (𝓞 k) v.asIdeal := by
        rw [← hPu, Ideal.under_under]
      have h2 : Ideal.under (𝓞 k) W'.asIdeal = Ideal.under (𝓞 k) v.asIdeal := by
        rw [← Ideal.under_under (A := 𝓞 k) (B := 𝓞 ↥K) W'.asIdeal, ← primeUnder_asIdeal, hW'u]
      rw [h1, h2]

end Pairing

end InverseGalois.Shafarevich

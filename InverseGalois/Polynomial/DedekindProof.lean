/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Polynomial.FrobeniusLift

/-!
# Proof Infrastructure for Dedekind's Theorem

This file provides the building blocks for proving Dedekind's theorem, which
relates the mod-p factorization of a polynomial to cycle types in its Galois group.

## Structure

1. **Finite field infrastructure**: The Frobenius endomorphism x ↦ x^p on an
   algebraic closure of 𝔽_p maps roots to roots and induces a well-defined
   permutation on the root set.

2. **Frobenius cycle type**: The cycle type of the Frobenius permutation on roots
   of a squarefree polynomial over 𝔽_p equals its factorization type.

3. **Frobenius lifting** (the deep part): There exists a Galois automorphism
   over ℚ whose galActionHom image has the same cycle type as the Frobenius
   permutation on the mod-p roots. -/

open Polynomial UniqueFactorizationMonoid Classical NumberField

noncomputable section

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-!
## Section 1: Frobenius on roots over finite fields
-/

private lemma expChar_zmod : ExpChar (ZMod p) p := ExpChar.prime hp.out

private lemma expChar_algClosure : ExpChar (AlgebraicClosure (ZMod p)) p :=
  expChar_of_injective_ringHom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective p

private lemma perfectRing_algClosure : PerfectRing (AlgebraicClosure (ZMod p)) p := by
  haveI := expChar_algClosure (p := p)
  exact PerfectField.toPerfectRing p

/-- Over 𝔽_p, expanding a polynomial by p gives the polynomial raised to the p-th power. -/
lemma expand_eq_pow_zmod (f : Polynomial (ZMod p)) :
    (Polynomial.expand (ZMod p) p) f = f ^ p := by
  haveI := expChar_zmod (p := p)
  have h := Polynomial.expand_char (R := ZMod p) p f
  have frob_eq : frobenius (ZMod p) p = RingHom.id (ZMod p) := by ext x; simp
  rw [frob_eq, Polynomial.map_id] at h; exact h

/-- For f ∈ 𝔽_p[X] and α in the algebraic closure, f(α^p) = f(α)^p. -/
lemma eval₂_pow_char (f : Polynomial (ZMod p)) (α : AlgebraicClosure (ZMod p)) :
    Polynomial.eval₂ (algebraMap _ _) (α ^ p) f =
    (Polynomial.eval₂ (algebraMap _ _) α f) ^ p := by
  haveI := expChar_algClosure (p := p)
  rw [← Polynomial.eval_map, ← Polynomial.eval_map]
  set φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
  set g := f.map φ
  rw [← Polynomial.expand_eval p g α]
  suffices h : (Polynomial.expand _ p) g = g ^ p by rw [h]; simp [Polynomial.eval_pow]
  show (Polynomial.expand (AlgebraicClosure (ZMod p)) p) (f.map φ) = (f.map φ) ^ p
  rw [← Polynomial.map_expand (f := φ), expand_eq_pow_zmod, Polynomial.map_pow]

/-- The Frobenius x ↦ x^p maps roots of f ∈ 𝔽_p[X] to roots in the algebraic closure. -/
lemma frobenius_maps_roots (f : Polynomial (ZMod p)) (α : AlgebraicClosure (ZMod p))
    (hα : α ∈ f.rootSet (AlgebraicClosure (ZMod p))) :
    α ^ p ∈ f.rootSet (AlgebraicClosure (ZMod p)) := by
  rw [Polynomial.mem_rootSet] at hα ⊢
  refine ⟨hα.1, ?_⟩
  rw [Polynomial.aeval_def, eval₂_pow_char]
  have hα2 : Polynomial.eval₂ (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) α f = 0 := by
    rw [← Polynomial.aeval_def]; exact hα.2
  rw [hα2]; exact zero_pow (Nat.Prime.ne_zero hp.out)

/-- The Frobenius x ↦ x^p induces a permutation on the root set of any
nonzero polynomial f ∈ 𝔽_p[X] in the algebraic closure. -/
def frobeniusPermOnRoots (f : Polynomial (ZMod p)) (hf : f ≠ 0) :
    Equiv.Perm (f.rootSet (AlgebraicClosure (ZMod p))) := by
  haveI : Fintype (f.rootSet (AlgebraicClosure (ZMod p))) :=
    (Polynomial.rootSet_finite f _).fintype
  haveI := expChar_algClosure (p := p)
  exact Equiv.ofBijective
    (fun ⟨α, hα⟩ => ⟨α ^ p, frobenius_maps_roots f α hα⟩)
    ⟨fun ⟨x, _⟩ ⟨y, _⟩ h => by
        simp only [Subtype.mk.injEq] at h ⊢
        exact (frobenius (AlgebraicClosure (ZMod p)) p).injective
          (by rwa [frobenius_def, frobenius_def]),
     Finite.surjective_of_injective (fun ⟨x, _⟩ ⟨y, _⟩ h => by
        simp only [Subtype.mk.injEq] at h ⊢
        exact (frobenius (AlgebraicClosure (ZMod p)) p).injective
          (by rwa [frobenius_def, frobenius_def]))⟩

lemma frobeniusPermOnRoots_val (f : Polynomial (ZMod p)) (hf : f ≠ 0)
    (x : f.rootSet (AlgebraicClosure (ZMod p))) :
    (frobeniusPermOnRoots f hf x : AlgebraicClosure (ZMod p)) =
      (x : AlgebraicClosure (ZMod p)) ^ p := by
  simp [frobeniusPermOnRoots, Equiv.ofBijective]

/-- Monic polynomials over ℤ map to nonzero polynomials over ZMod p. -/
lemma monic_map_ne_zero (f : ℤ[X]) (hf : f.Monic) :
    f.map (Int.castRingHom (ZMod p)) ≠ 0 :=
  fun h => Polynomial.not_monic_zero (h ▸ hf.map (Int.castRingHom (ZMod p)))

/-!
## Section 2: Frobenius cycle type equals factorization type
-/

/-- The "factorization type" of a polynomial over a field: the multiset of
degrees of its monic irreducible factors, filtered to degrees ≥ 2. -/
def factorizationType {F : Type*} [Field F] [DecidableEq F] (f : F[X]) : Multiset ℕ :=
  ((normalizedFactors f).map natDegree).filter (· ≥ 2)

/-
For an irreducible polynomial g over 𝔽_p of degree d, the Frobenius x ↦ x^p
permutes the roots of g in a single cycle of length d.

This is because the splitting field of g is 𝔽_{p^d}, and the Galois group
Gal(𝔽_{p^d}/𝔽_p) is cyclic of order d generated by Frobenius. The roots of g
are α, α^p, ..., α^{p^{d-1}} (d distinct elements), and α^{p^d} = α.
-/
set_option maxHeartbeats 400000 in
lemma frobenius_on_irred_is_cycle
    (g : Polynomial (ZMod p)) (hg : g ≠ 0) (hirr : Irreducible g) :
    (frobeniusPermOnRoots g hg).IsCycle ∨ g.natDegree ≤ 1 := by
  by_cases h_deg : g.natDegree ≤ 1;
  · exact Or.inr h_deg;
  · -- Let α be a root of g in the algebraic closure.
    obtain ⟨α, hα⟩ : ∃ α : AlgebraicClosure (ZMod p), α ∈ g.rootSet (AlgebraicClosure (ZMod p)) := by
      obtain ⟨α, hα⟩ : ∃ α : AlgebraicClosure (ZMod p), g.eval₂ (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) α = 0 := by
        have := @IsAlgClosed.exists_root ( AlgebraicClosure ( ZMod p ) ) _;
        specialize this ( g.map ( algebraMap ( ZMod p ) ( AlgebraicClosure ( ZMod p ) ) ) ) ; simp_all [ Polynomial.degree_map ] ;
        exact this ( ne_of_gt ( Polynomial.natDegree_pos_iff_degree_pos.mp ( pos_of_gt h_deg ) ) ) |> fun ⟨ x, hx ⟩ => ⟨ x, by simpa [ Polynomial.eval₂_eq_eval_map ] using hx ⟩;
      exact ⟨ α, by rw [ Polynomial.mem_rootSet ] ; aesop ⟩;
    -- The orbit of α under Frobenius has size exactly d.
    have h_orbit_size : Finset.card (Finset.image (fun k : ℕ => α ^ (p ^ k)) (Finset.range g.natDegree)) = g.natDegree := by
      -- If α^(p^k) = α for some k < d, then α would be in the field with p^k elements, contradicting the fact that α is a root of an irreducible polynomial of degree d.
      have h_contra : ∀ k < g.natDegree, k ≠ 0 → α ^ (p ^ k) ≠ α := by
        intros k hk_lt hk_ne_zero hk_eq
        have h_in_field : α ∈ IntermediateField.adjoin (ZMod p) {α} := by
          exact IntermediateField.mem_adjoin_simple_self _ _
        have h_deg : Module.finrank (ZMod p) (IntermediateField.adjoin (ZMod p) {α}) = g.natDegree := by
          rw [ IntermediateField.adjoin.finrank ];
          · rw [ Polynomial.mem_rootSet ] at hα;
            rw [ show minpoly ( ZMod p ) α = Polynomial.C ( g.leadingCoeff ) ⁻¹ * g from _ ];
            · rw [ Polynomial.natDegree_C_mul ] ; aesop;
            · refine' Eq.symm ( minpoly.eq_of_irreducible_of_monic _ _ _ );
              · rw [ irreducible_mul_iff ] ; aesop;
              · aesop;
              · rw [ Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, inv_mul_cancel₀ ] ; aesop;
          · exact Algebra.IsIntegral.isIntegral α
        have h_contra : Module.finrank (ZMod p) (IntermediateField.adjoin (ZMod p) {α}) ≤ k := by
          have h_contra : ∀ x ∈ IntermediateField.adjoin (ZMod p) {α}, x ^ (p ^ k) = x := by
            intro x hx; induction hx using IntermediateField.adjoin_induction <;> simp_all [ pow_mul, pow_add ] ;
            · simp [ ← map_pow, ZMod.pow_card_pow ];
            · simp_all [ add_pow_char_pow ];
            · rw [ mul_pow, ‹ ( _ : AlgebraicClosure ( ZMod p ) ) ^ p ^ k = _ ›, ‹ ( _ : AlgebraicClosure ( ZMod p ) ) ^ p ^ k = _ › ];
          have h_contra : ∀ x ∈ IntermediateField.adjoin (ZMod p) {α}, x ∈ (Polynomial.X ^ (p ^ k) - Polynomial.X : Polynomial (ZMod p)).rootSet (AlgebraicClosure (ZMod p)) := by
            simp_all [ Polynomial.mem_rootSet ];
            exact fun x hx => ne_of_apply_ne Polynomial.natDegree <| by rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num [ hp.1.ne_zero, hp.1.one_lt, hk_ne_zero ] ;
          have h_contra : Set.ncard (IntermediateField.adjoin (ZMod p) {α} : Set (AlgebraicClosure (ZMod p))) ≤ p ^ k := by
            have h_contra : Set.ncard (IntermediateField.adjoin (ZMod p) {α} : Set (AlgebraicClosure (ZMod p))) ≤ Multiset.card (Polynomial.roots (Polynomial.X ^ (p ^ k) - Polynomial.X : Polynomial (AlgebraicClosure (ZMod p)))) := by
              have h_contra : (IntermediateField.adjoin (ZMod p) {α} : Set (AlgebraicClosure (ZMod p))) ⊆ Multiset.toFinset (Polynomial.roots (Polynomial.X ^ (p ^ k) - Polynomial.X : Polynomial (AlgebraicClosure (ZMod p)))) := by
                simp_all [ Set.subset_def, Polynomial.rootSet_def ];
                exact h_contra
              exact le_trans ( Set.ncard_le_ncard h_contra ) ( by rw [ Set.ncard_coe_finset ] ; exact Multiset.toFinset_card_le _ );
            exact h_contra.trans ( le_trans ( Polynomial.card_roots' _ ) ( by erw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num ; exact one_lt_pow₀ hp.1.one_lt hk_ne_zero ) );
          have h_contra : Set.ncard (IntermediateField.adjoin (ZMod p) {α} : Set (AlgebraicClosure (ZMod p))) = p ^ (Module.finrank (ZMod p) (IntermediateField.adjoin (ZMod p) {α})) := by
            have h_contra : ∀ (F : IntermediateField (ZMod p) (AlgebraicClosure (ZMod p))), FiniteDimensional (ZMod p) F → Set.ncard (F : Set (AlgebraicClosure (ZMod p))) = p ^ (Module.finrank (ZMod p) F) := by
              intros F hF_finiteDimensional
              have h_contra : Nonempty (F ≃ₗ[ZMod p] (Fin (Module.finrank (ZMod p) F) → ZMod p)) := by
                exact ⟨ ( Module.finBasis ( ZMod p ) F ).equivFun ⟩;
              obtain ⟨ e ⟩ := h_contra; rw [ Set.ncard_def ] ; simp [ Set.encard, e.cardinal_eq ] ;
              rw [ ENat.card_congr e.toEquiv ] ; simp [ ENat.card ] ;
            apply h_contra;
            exact FiniteDimensional.of_finrank_pos ( by linarith );
          exact le_of_not_gt fun h => by linarith [ pow_lt_pow_right₀ hp.1.one_lt h ] ;
        linarith [hk_lt];
      rw [ Finset.card_image_of_injOn, Finset.card_range ];
      intros k hk l hl hkl;
      by_contra hkl_ne;
      -- Without loss of generality, assume $k < l$.
      wlog hkl_lt : k < l generalizing k l;
      · exact this hl hk ( by simpa only [ eq_comm ] using hkl ) ( Ne.symm hkl_ne ) ( lt_of_le_of_ne ( le_of_not_gt hkl_lt ) ( Ne.symm hkl_ne ) );
      · -- Since $k < l$, we have $α^{p^l} = α^{p^k}$ implies $α^{p^{l-k}} = α$.
        have h_exp : α ^ (p ^ (l - k)) = α := by
          have h_exp : α ^ (p ^ l) = (α ^ (p ^ k)) ^ (p ^ (l - k)) := by
            rw [ ← pow_mul, ← pow_add, Nat.add_sub_of_le hkl_lt.le ];
          have h_exp : α ^ (p ^ (l - k)) = α := by
            have h_eq : (α ^ (p ^ k)) ^ (p ^ (l - k)) = α ^ (p ^ k) := by
              grind
            have h_eq : (α ^ (p ^ (l - k)) - α) ^ (p ^ k) = 0 := by
              simp_all [ sub_pow_char_pow ];
              rw [ ← pow_mul, mul_comm, pow_mul, h_eq, sub_self ];
            exact sub_eq_zero.mp ( eq_zero_of_pow_eq_zero h_eq );
          exact h_exp;
        exact h_contra ( l - k ) ( by rw [ Finset.mem_coe, Finset.mem_range ] at *; omega ) ( Nat.sub_ne_zero_of_lt hkl_lt ) h_exp;
    -- Since the orbit has size d = |rootSet|, the permutation is a single cycle on the entire set, hence IsCycle.
    have h_orbit_eq_rootSet : Finset.image (fun k : ℕ => α ^ (p ^ k)) (Finset.range g.natDegree) = Finset.image (fun x : g.rootSet (AlgebraicClosure (ZMod p)) => x.val) (Finset.univ : Finset (g.rootSet (AlgebraicClosure (ZMod p)))) := by
      refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _;
      · intro k hk; induction' k with k ih <;> simp_all [ pow_succ, pow_mul ] ;
        convert frobenius_maps_roots g _ ( ih ( Nat.lt_of_succ_lt hk ) ) using 1;
      · rw [ h_orbit_size, Finset.card_image_of_injective ];
        · simp [ Polynomial.rootSet_def ];
          exact le_trans ( Multiset.toFinset_card_le _ ) ( Polynomial.card_roots' _ ) |> le_trans <| by simp [ Polynomial.natDegree_map ] ;
        · exact Subtype.coe_injective;
    refine Or.inl ⟨ ⟨ α, hα ⟩, ?_, ?_ ⟩;
    · intro h; have := congr_arg Subtype.val h; simp_all [ frobeniusPermOnRoots_val ] ;
      replace h_orbit_eq_rootSet := Finset.card_image_iff.mp ( by aesop : Finset.card ( Finset.image ( fun k => α ^ p ^ k ) ( Finset.range g.natDegree ) ) = _ ) ; simp_all [ Finset.card_image_of_injective, Function.Injective ] ;
      have := @h_orbit_eq_rootSet 0 ( by norm_num; linarith ) 1 ( by norm_num; linarith ) ; simp_all [ pow_succ, pow_mul ] ;
      exact this ( by simpa [ frobeniusPermOnRoots_val ] using congr_arg Subtype.val h.symm );
    · intro y hy; replace h_orbit_eq_rootSet := Finset.ext_iff.mp h_orbit_eq_rootSet y; simp_all [ Finset.mem_image ] ;
      obtain ⟨ k, hk₁, hk₂ ⟩ := h_orbit_eq_rootSet; use k; simp_all [ frobeniusPermOnRoots_val ] ;
      refine' Subtype.ext _;
      convert hk₂ using 1;
      refine' Nat.recOn k _ _ <;> simp_all [ pow_succ, pow_mul, frobeniusPermOnRoots_val ];
      intro n hn; erw [ show ( frobeniusPermOnRoots g hg ^ n ) ( frobeniusPermOnRoots g hg ⟨ α, hα ⟩ ) = frobeniusPermOnRoots g hg ( ( frobeniusPermOnRoots g hg ^ n ) ⟨ α, hα ⟩ ) from ?_ ] ; simp_all [ pow_succ, pow_mul, frobeniusPermOnRoots_val ] ;
      exact Nat.recOn n rfl fun n ihn => by simp [ *, pow_succ', mul_assoc ] ;

/-
For an irreducible polynomial g over 𝔽_p of degree d, the Frobenius permutation
on its roots has support of size d (i.e., the cycle length is d).
-/
lemma frobenius_on_irred_support_card
    (g : Polynomial (ZMod p)) (hg : g ≠ 0) (hirr : Irreducible g)
    (hd : g.natDegree ≥ 2) :
    (frobeniusPermOnRoots g hg).support.card = g.natDegree := by
  -- Since $g$ is irreducible and has degree $d \geq 2$, the Frobenius permutation on its roots is a single cycle of length $d$. Therefore, the support of the Frobenius permutation is exactly the set of roots of $g$.
  have h_support : (frobeniusPermOnRoots g hg).support = Finset.univ := by
    apply Finset.eq_univ_of_forall; intro x; simp [frobeniusPermOnRoots];
    -- Since $x$ is a root of $g$, we have $g(x) = 0$. If $x^p = x$, then $x$ would be a root of $x^p - x$, which contradicts the irreducibility of $g$.
    have h_contradiction : ¬(x.val ^ p = x.val) := by
      intro h_contra
      have h_root : x.val ∈ Set.range (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
        have h_root : x.val ∈ Set.range (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
          have h_poly : (Polynomial.X ^ p - Polynomial.X : Polynomial (AlgebraicClosure (ZMod p))) = ∏ a ∈ Finset.univ, (Polynomial.X - Polynomial.C (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) a)) := by
            refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
            exact Finset.image ( fun a : ZMod p => algebraMap ( ZMod p ) ( AlgebraicClosure ( ZMod p ) ) a ) Finset.univ;
            · convert Polynomial.degree_sub_lt _ _ ?_ <;> norm_num [ Polynomial.degree_prod, Polynomial.degree_X_pow_sub_C ];
              · rw [ Finset.card_image_of_injective _ fun a b h => by simpa using h, Finset.card_univ ] ; norm_num [ Polynomial.degree_sub_eq_left_of_degree_lt, hp.1.one_lt ];
              · rw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> norm_num [ hp.1.one_lt ];
              · exact ne_of_apply_ne ( Polynomial.derivative ) ( by simp [ Polynomial.derivative_pow, hp.1.ne_zero ] );
              · rw [ Polynomial.leadingCoeff_prod ];
                rw [ Polynomial.leadingCoeff_sub_of_degree_lt ] <;> norm_num [ hp.1.one_lt ];
            · simp [ Polynomial.eval_prod ];
              intro a; rw [ Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_univ a ] ; simp [ sub_eq_iff_eq_add ] ;
              exact_mod_cast ZMod.pow_card a
          replace h_poly := congr_arg ( Polynomial.eval ( x : AlgebraicClosure ( ZMod p ) ) ) h_poly ; simp_all [ Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_iff_eq_add ] ;
          exact Exists.elim ( Finset.prod_eq_zero_iff.mp h_poly.symm ) fun y hy => ⟨ y, by linear_combination -hy.2 ⟩;
        exact h_root;
      obtain ⟨ y, hy ⟩ := h_root; simp_all [ Polynomial.mem_rootSet ] ;
      have := Polynomial.degree_eq_one_of_irreducible_of_root hirr ( show g.eval y = 0 from ?_ ) ; rw [ Polynomial.degree_eq_natDegree hirr.ne_zero ] at this ; norm_cast at this ; linarith;
      have := x.2; rw [ Polynomial.mem_rootSet ] at this; aesop;
    exact fun h => h_contradiction <| Subtype.ext_iff.mp h;
  rw [h_support, Finset.card_univ]
  exact Polynomial.card_rootSet_eq_natDegree
    (PerfectField.separable_of_irreducible hirr) (IsAlgClosed.splits _)

/-
For an irreducible polynomial g over 𝔽_p, the Frobenius cycle type equals the
factorization type. Since g is irreducible, factorizationType(g) = {deg(g)} if
deg(g) ≥ 2, and ∅ if deg(g) ≤ 1.
-/
lemma frobenius_cycleType_irred
    (g : Polynomial (ZMod p)) (hg : g ≠ 0) (hirr : Irreducible g) :
    (frobeniusPermOnRoots g hg).cycleType = factorizationType g := by
  -- For an irreducible polynomial g over a field, the normalized factors are {normalize g}.
  have h_normalized_factors : normalizedFactors g = {normalize g} := by
    convert UniqueFactorizationMonoid.normalizedFactors_irreducible hirr;
  by_cases hd : g.natDegree ≥ 2;
  · -- Since g is irreducible, the Frobenius permutation on its roots is a single cycle of length g.natDegree.
    have h_frobenius_cycle : (frobeniusPermOnRoots g hg).IsCycle ∧ (frobeniusPermOnRoots g hg).support.card = g.natDegree := by
      exact ⟨ frobenius_on_irred_is_cycle g hg hirr |> Or.resolve_right <| by linarith, frobenius_on_irred_support_card g hg hirr hd ⟩;
    convert h_frobenius_cycle.1.cycleType using 1;
    unfold factorizationType;
    simp_all [ normalize_apply ];
    rw [ Polynomial.natDegree_mul' ] <;> aesop;
  · -- Since the degree of g is less than 2, the permutation is the identity.
    have h_identity : frobeniusPermOnRoots g hg = 1 := by
      have h_root_set_card : (g.rootSet (AlgebraicClosure (ZMod p))).toFinset.card ≤ 1 := by
        exact le_trans ( Finset.card_le_card <| show ( g.rootSet ( AlgebraicClosure ( ZMod p ) ) ).toFinset ⊆ ( g.map ( algebraMap ( ZMod p ) ( AlgebraicClosure ( ZMod p ) ) ) |> Polynomial.roots |> Multiset.toFinset ) from fun x hx => by simp_all [ Polynomial.mem_rootSet ] ) ( le_trans ( Multiset.toFinset_card_le _ ) <| by exact le_trans ( Polynomial.card_roots' _ ) <| by erw [ Polynomial.natDegree_map ] ; interval_cases g.natDegree <;> simp_all );
      interval_cases _ : Finset.card _ <;> simp_all [ Equiv.Perm.ext_iff ];
      · simp_all [ Fintype.card_eq_zero_iff ];
      · rw [ Fintype.card_eq_one_iff ] at * ; aesop;
    simp_all [ factorizationType ];
    interval_cases _ : g.natDegree <;> simp_all [ normalize ]; all_goals rw [ Polynomial.natDegree_mul' ] <;> aesop

/-!
### Helper lemmas for the squarefree case
-/

private lemma factorizationType_mul'
    (g h : (ZMod p)[X]) (hg : g ≠ 0) (hh : h ≠ 0) :
    factorizationType (g * h) = factorizationType g + factorizationType h := by
  unfold factorizationType
  rw [normalizedFactors_mul hg hh, Multiset.map_add, Multiset.filter_add]

private lemma rootSet_unit_mul'
    (u : (ZMod p)[X]ˣ) (g : (ZMod p)[X]) :
    ((u : (ZMod p)[X]) * g).rootSet (AlgebraicClosure (ZMod p)) =
      g.rootSet (AlgebraicClosure (ZMod p)) := by
  rcases Polynomial.isUnit_iff.mp u.isUnit with ⟨ k, hk ⟩;
  simp [ ← hk.2, Polynomial.rootSet_def ];
  ext; simp [hk.left.ne_zero]

private lemma factorizationType_unit_mul'
    (u : (ZMod p)[X]ˣ) (g : (ZMod p)[X]) :
    factorizationType ((u : (ZMod p)[X]) * g) = factorizationType g := by
  by_cases hg : g = 0
  · simp [hg]
  · unfold factorizationType
    congr 1; congr 1
    rw [normalizedFactors_mul (Units.ne_zero u) hg,
        show normalizedFactors (u : (ZMod p)[X]) = 0
          from normalizedFactors_of_isUnit u.isUnit,
        Multiset.zero_add]

private lemma frobeniusPermOnRoots_unit_mul'
    (u : (ZMod p)[X]ˣ) (g : Polynomial (ZMod p))
    (hg : g ≠ 0) :
    (frobeniusPermOnRoots ((u : (ZMod p)[X]) * g)
      (mul_ne_zero (Units.ne_zero u) hg)).cycleType =
    (frobeniusPermOnRoots g hg).cycleType := by
  convert Equiv.Perm.cycleType_extendDomain _;
  rotate_left;
  exact Set.Finite.fintype ( Polynomial.rootSet_finite _ _ );
  infer_instance;
  exact fun x => x.val ∈ g.rootSet ( AlgebraicClosure ( ZMod p ) );
  exact fun x => inferInstance;
  exact ⟨ fun x => ⟨ ⟨ x, by
    grind only [rootSet_unit_mul'] ⟩, by
    exact x.2 ⟩, fun x => ⟨ x.val, by
    exact x.2 ⟩, fun x => by
    aesop, fun x => by
    aesop ⟩
  generalize_proofs at *;
  ext; simp [Equiv.Perm.extendDomain];
  grind only [Equiv.Perm.subtypeCongr.apply, Equiv.permCongr_def, frobeniusPermOnRoots_val, rootSet_unit_mul', Equiv.permCongr_apply, = Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]

/-
General permutation decomposition: if σ preserves two complementary disjoint
predicates, then its cycle type is the sum of the restricted cycle types.
-/
private lemma perm_cycleType_decompose {α : Type*} [Fintype α] [DecidableEq α]
    {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (σ : Equiv.Perm α) (hP : ∀ x, P (σ x) ↔ P x) (hQ : ∀ x, Q (σ x) ↔ Q x)
    (hdisj : ∀ x, ¬(P x ∧ Q x)) (hcover : ∀ x, P x ∨ Q x) :
    σ.cycleType = (σ.subtypePerm hP).cycleType + (σ.subtypePerm hQ).cycleType := by
  by_contra h_contra;
  -- Let's denote the set of elements where P holds by A and the set where Q holds by B.
  set A := {x : α | P x}
  set B := {x : α | Q x};
  -- Since A and B are complementary sets, we can split the permutation σ into two permutations, one acting on A and the other on B.
  have h_split : σ = (Equiv.Perm.subtypePerm σ hP).extendDomain (Equiv.setCongr (by
  rfl : A = A)) * (Equiv.Perm.subtypePerm σ hQ).extendDomain (Equiv.setCongr (by
  rfl : B = B)) := by
    ext x; cases hcover x <;> simp_all [ Equiv.Perm.subtypePerm, Equiv.Perm.extendDomain ] ;
    · grind only [Equiv.Perm.subtypeCongr.apply, Equiv.Perm.subtypeCongr.left_apply, Equiv.permCongr_def, usr Set.mem_setOf_eq, = Equiv.refl_apply, Equiv.permCongr_apply, = Equiv.trans_apply, Equiv.setCongr_apply, Equiv.setCongr_symm_apply, Equiv.coe_fn_mk, #75d5, #6def];
    · simp [ Equiv.Perm.subtypeCongr, Equiv.setCongr ];
      simp [ Equiv.sumCompl, Equiv.subtypeEquivProp ];
      grind
  generalize_proofs at *;
  refine' h_contra _;
  convert congr_arg Equiv.Perm.cycleType h_split using 1;
  rw [ Equiv.Perm.Disjoint.cycleType_mul ];
  · rw [ Equiv.Perm.cycleType_extendDomain, Equiv.Perm.cycleType_extendDomain ];
  · intro x; by_cases hx : P x <;> by_cases hx' : Q x <;> simp [ hx, hx' ] at hdisj ⊢;
    · exact False.elim ( hdisj x hx hx' );
    · simp [ Equiv.Perm.extendDomain, hx, hx' ];
      simp [ Equiv.Perm.subtypeCongr, hx, hx' ];
      simp [ Equiv.sumCompl, hx, hx' ];
      grind;
    · grind only [Equiv.Perm.extendDomain_apply_not_subtype, usr Set.mem_setOf_eq];
    · exact False.elim ( hx' ( Or.resolve_left ( hcover x ) hx ) )

/-
If two permutations on subtypes are "the same" (both act as x ↦ x^p on the
underlying values), they have the same cycle type.
-/
private lemma subtypePerm_cycleType_eq_of_equiv {α : Type*} [Fintype α] [DecidableEq α]
    {P : α → Prop} [DecidablePred P]
    {β : Type*} [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm {x : α // P x}) (τ : Equiv.Perm β)
    (e : β ≃ {x : α // P x})
    (h : ∀ x, σ (e x) = e (τ x)) :
    σ.cycleType = τ.cycleType := by
  -- Since σ and e.permCongr τ are equal, their cycle types are equal.
  have h_cycleType_eq : σ.cycleType = (Equiv.permCongr e τ).cycleType := by
    congr;
    exact Equiv.ext fun x => by simpa using h ( e.symm x ) ;
  convert h_cycleType_eq using 1;
  apply Eq.symm; exact (by
    have : (e.permCongr τ).cycleType = τ.cycleType := by
      have : (e.permCongr τ).cycleType = (τ.extendDomain e).cycleType := by
        have h_cycleType_eq : (Equiv.Perm.ofSubtype (Equiv.permCongr e τ)) = τ.extendDomain e := by
          ext x; simp [Equiv.Perm.ofSubtype, Equiv.Perm.extendDomain];
        rw [ ← h_cycleType_eq, Equiv.Perm.cycleType_ofSubtype ]
      rw [ this, Equiv.Perm.cycleType_extendDomain ]
    exact this)

/-
For coprime g, h with g*h squarefree, the Frobenius cycle type on rootSet(g*h)
equals the sum of Frobenius cycle types on rootSet(g) and rootSet(h).
-/
set_option maxHeartbeats 800000 in
private lemma frobenius_cycleType_coprime_mul'
    (g h : Polynomial (ZMod p)) (hg : g ≠ 0) (hh : h ≠ 0)
    (hgh : g * h ≠ 0) (hc : IsCoprime g h)
    (hsf : Squarefree (g * h)) :
    (frobeniusPermOnRoots (g * h) hgh).cycleType =
      (frobeniusPermOnRoots g hg).cycleType + (frobeniusPermOnRoots h hh).cycleType := by
  -- Define P := fun x => x.val ∈ g.rootSet K and Q := fun x => x.val ∈ h.rootSet K on rootSet(g*h).
  set P : (g * h).rootSet (AlgebraicClosure (ZMod p)) → Prop := fun x => x.val ∈ g.rootSet (AlgebraicClosure (ZMod p))
  set Q : (g * h).rootSet (AlgebraicClosure (ZMod p)) → Prop := fun x => x.val ∈ h.rootSet (AlgebraicClosure (ZMod p));
  -- Show P and Q are preserved by σ := frobeniusPermOnRoots (g*h) hgh.
  have hP : ∀ x, P (frobeniusPermOnRoots (g * h) hgh x) ↔ P x := by
    simp +zetaDelta at *;
    intro a ha; have := frobeniusPermOnRoots_val ( g * h ) hgh ⟨ a, ha ⟩ ; simp_all [ Polynomial.mem_rootSet ] ;
    have := eval₂_pow_char g a; simp_all [ Polynomial.aeval_def ] ;
    exact fun _ => hp.1.ne_zero
  have hQ : ∀ x, Q (frobeniusPermOnRoots (g * h) hgh x) ↔ Q x := by
    simp +zetaDelta at *;
    simp_all [ Polynomial.mem_rootSet ];
    simp_all [ frobeniusPermOnRoots_val ];
    simp_all [ aeval_def, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one ];
    intro a ha; specialize hP a ha; simp_all [ eval₂_pow_char ] ;
    exact fun _ => hp.1.ne_zero;
  -- Show P and Q are disjoint and cover.
  have h_disjoint : ∀ x, ¬(P x ∧ Q x) := by
    simp +zetaDelta at *;
    intro a ha₁ ha₂ ha₃; simp_all [ Polynomial.mem_rootSet ] ;
    obtain ⟨ u, v, h ⟩ := hc; replace h := congr_arg ( Polynomial.aeval a ) h; simp_all ;
  have h_cover : ∀ x, P x ∨ Q x := by
    simp +zetaDelta at *;
    simp [ Polynomial.mem_rootSet, hg, hh ];
  rw [ perm_cycleType_decompose _ hP hQ h_disjoint h_cover ];
  refine' congrArg₂ ( · + · ) _ _;
  · refine' subtypePerm_cycleType_eq_of_equiv _ _ _ _;
    refine' Equiv.ofBijective _ ⟨ _, _ ⟩;
    use fun x => ⟨ ⟨ x.val, by
      simp_all [ Polynomial.mem_rootSet ];
      exact Or.inl <| Polynomial.mem_rootSet.mp x.2 |>.2 ⟩, by
      exact x.2 ⟩;
    all_goals simp [ Function.Injective, Function.Surjective ];
    · exact fun a ha ha' => ha';
    · intro a ha; ext; simp [ frobeniusPermOnRoots_val ] ;
  · refine' subtypePerm_cycleType_eq_of_equiv _ _ _ _;
    refine' Equiv.ofBijective _ ⟨ _, _ ⟩;
    use fun x => ⟨ ⟨ x.val, by
      simp_all [ Polynomial.mem_rootSet ];
      exact Or.inr ( by simpa [ Polynomial.eval₂_eq_eval_map ] using Polynomial.mem_rootSet.mp x.2 |>.2 ) ⟩, by
      exact x.2 ⟩;
    all_goals norm_num [ Function.Injective, Function.Surjective ];
    · exact fun a ha ha' => ha';
    · intro a ha; ext; simp [ frobeniusPermOnRoots_val ] ;

/-
The cycle type of the Frobenius permutation on the roots of a squarefree polynomial
f ∈ 𝔽_p[X] equals the factorization type of f.

For each irreducible factor g of f of degree d, the roots of g in the algebraic
closure form a single orbit of size d under x ↦ x^p.
-/
theorem frobenius_cycleType_eq_factorizationType
    (f : Polynomial (ZMod p)) (hf : f ≠ 0) (hsf : Squarefree f) :
    (frobeniusPermOnRoots f hf).cycleType = factorizationType f := by
  revert f hf hsf;
  intro f hf hsf
  have h_segment : ∀ (g : Polynomial (ZMod p)) (hg : g ≠ 0) (hirr : Irreducible g), (frobeniusPermOnRoots g hg).cycleType = factorizationType g := by
    grind only [frobenius_cycleType_irred];
  have h_segment_mul : ∀ (g h : Polynomial (ZMod p)) (hg : g ≠ 0) (hh : h ≠ 0) (hgh : g * h ≠ 0) (hc : IsCoprime g h) (hsf : Squarefree (g * h)), (frobeniusPermOnRoots (g * h) hgh).cycleType = (frobeniusPermOnRoots g hg).cycleType + (frobeniusPermOnRoots h hh).cycleType := by
    exact fun g h hg hh hgh hc hsf => frobenius_cycleType_coprime_mul' g h hg hh hgh hc hsf;
  have h_segment_mul : ∀ (g : Polynomial (ZMod p)) (hg : g ≠ 0) (hsf : Squarefree g), (frobeniusPermOnRoots g hg).cycleType = factorizationType g := by
    intro g hg hsf
    induction' g using WfDvdMonoid.induction_on_irreducible with g hg ih;
    · contradiction;
    · rw [ Polynomial.isUnit_iff ] at *;
      obtain ⟨ r, hr, rfl ⟩ := ‹∃ r, IsUnit r ∧ C r = g›; simp_all [ factorizationType ] ;
      rw [ Multiset.filter_eq_nil.mpr ] <;> norm_num;
      · ext ⟨ x, hx ⟩ ; simp [ hr, Polynomial.mem_rootSet ] at hx ⊢;
      · intro a ha; have := Polynomial.natDegree_le_of_dvd ( dvd_of_mem_normalizedFactors ha ) ; aesop;
    · rename_i g hg₁ hg₂ hg₃;
      rw [ h_segment_mul g ih hg₂.ne_zero hg₁ hg ];
      · rw [ h_segment g hg₂.ne_zero hg₂, hg₃ hg₁ ];
        · rw [ factorizationType_mul' g ih hg₂.ne_zero hg₁ ];
        · exact hsf.of_mul_right;
      · refine' hg₂.coprime_iff_not_dvd.mpr _;
        intro h; have := hsf g; simp_all [ dvd_mul_of_dvd_left, dvd_mul_of_dvd_right ] ;
        exact absurd ( this ( mul_dvd_mul_left _ h ) ) ( by exact hg₂.not_isUnit );
      · exact hsf;
  exact h_segment_mul f hf hsf

/-!
## Section 3: Frobenius lifting -/

/-
Over a perfect field, squarefree polynomials are separable.
-/
private lemma squarefree_separable_of_perfectField {F : Type*} [Field F] [PerfectField F]
    (g : Polynomial F) (hg : Squarefree g) : g.Separable := by
  exact PerfectField.separable_iff_squarefree.mpr hg

/-
The natDegree of f.map ℚ equals the natDegree of f.map (ZMod p) for monic f.
-/
private lemma natDegree_map_eq_of_monic (f : ℤ[X]) (hf : f.Monic) :
    (f.map (Int.castRingHom ℚ)).natDegree = (f.map (Int.castRingHom (ZMod p))).natDegree := by
  rw [ Polynomial.natDegree_map_of_leadingCoeff_ne_zero, Polynomial.natDegree_map_of_leadingCoeff_ne_zero ] <;> norm_num [ hf ]

/-
The reduction map on roots is injective: if f mod p is squarefree,
then distinct roots of f in L reduce to distinct elements modulo Q.
-/
private lemma reduction_injective_on_roots_aux (f : ℤ[X]) (hf_monic : f.Monic)
    (hf_irr : Irreducible (f.map (Int.castRingHom ℚ)))
    (h_sep : Squarefree (f.map (Int.castRingHom (ZMod p))))
    {L : Type*} [Field L] [Algebra ℚ L] [NumberField L] [IsGalois ℚ L]
    [Polynomial.IsSplittingField ℚ L (f.map (Int.castRingHom ℚ))]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ Q)
    (α β : 𝓞 L)
    (hα : Polynomial.aeval (α : L) (f.map (Int.castRingHom ℚ)) = 0)
    (hβ : Polynomial.aeval (β : L) (f.map (Int.castRingHom ℚ)) = 0)
    (h_eq : Ideal.Quotient.mk Q α = Ideal.Quotient.mk Q β) :
    (α : L) = (β : L) := by
  -- By contradiction, assume α ≠ β.
  by_contra h_neq;
  have h_common_root : (f.map (Int.castRingHom (𝓞 L ⧸ Q))).IsRoot (Ideal.Quotient.mk Q α) ∧ (Polynomial.derivative (f.map (Int.castRingHom (𝓞 L ⧸ Q)))).IsRoot (Ideal.Quotient.mk Q α) := by
    have h_common_root : (Polynomial.map (Int.castRingHom (𝓞 L)) f).eval₂ (algebraMap (𝓞 L) L) (α : L) = 0 ∧ (Polynomial.map (Int.castRingHom (𝓞 L)) f).eval₂ (algebraMap (𝓞 L) L) (β : L) = 0 := by
      simp_all [ Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range ];
    obtain ⟨g, hg⟩ : ∃ g : Polynomial (𝓞 L), Polynomial.map (Int.castRingHom (𝓞 L)) f = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β) * g := by
      obtain ⟨ g, hg ⟩ := Polynomial.dvd_iff_isRoot.mpr ( show Polynomial.eval₂ ( algebraMap ( 𝓞 L ) ( 𝓞 L ) ) α ( Polynomial.map ( Int.castRingHom ( 𝓞 L ) ) f ) = 0 from by simpa [ Polynomial.eval₂_eq_eval_map ] using h_common_root.1 );
      simp_all [ Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C ];
      exact mul_dvd_mul_left _ ( Polynomial.dvd_iff_isRoot.mpr ( h_common_root.resolve_left ( sub_ne_zero_of_ne <| by simpa [ sub_eq_zero ] using Ne.symm <| by simpa [ sub_eq_zero ] using h_neq ) ) );
    replace hg := congr_arg ( Polynomial.map ( Ideal.Quotient.mk Q ) ) hg ; simp_all [ Polynomial.eval₂_eq_eval_map ] ;
    replace hg := congr_arg ( Polynomial.derivative ) hg ; simp_all [ Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C ] ;
    replace hg := congr_arg ( Polynomial.eval ( Ideal.Quotient.mk Q β ) ) hg ; simp_all [ Polynomial.eval_map ] ;
    convert reduction_of_root_is_root f Q α hα using 1;
    simp [ Polynomial.aeval_def, Polynomial.eval₂_map, h_eq ];
  -- Since $f$ is squarefree over $\mathbb{Z}/p\mathbb{Z}$, it is separable over $\mathbb{Z}/p\mathbb{Z}$.
  have h_separable : Polynomial.Separable (f.map (Int.castRingHom (ZMod p))) := by
    convert squarefree_separable_of_perfectField _ h_sep;
  -- Since $f$ is separable over $\mathbb{Z}/p\mathbb{Z}$, it is also separable over $\mathcal{O}_L/Q$.
  have h_separable_Q : Polynomial.Separable (f.map (Int.castRingHom (𝓞 L ⧸ Q))) := by
    obtain ⟨ a, b, h ⟩ := h_separable;
    -- Since $Q$ is a maximal ideal above $p$, the quotient $\mathcal{O}_L/Q$ is a field extension of $\mathbb{Z}/p\mathbb{Z}$.
    have h_field_extension : ∃ (φ : ZMod p →+* 𝓞 L ⧸ Q), Function.Injective φ := by
      have h_field_extension : ∃ (φ : ZMod p →+* 𝓞 L ⧸ Q), Function.Injective φ := by
        have h_char : CharP (𝓞 L ⧸ Q) p := by
          exact residue_field_charP Q hQ
        exact ⟨ ZMod.castHom ( by aesop ) _, ZMod.castHom_injective _ ⟩;
      exact h_field_extension;
    obtain ⟨ φ, hφ ⟩ := h_field_extension;
    refine' ⟨ Polynomial.map φ a, Polynomial.map φ b, _ ⟩;
    convert congr_arg ( Polynomial.map φ ) h using 1 <;> simp [ Polynomial.map_map ];
    congr! 2;
    · ext; simp [ Polynomial.coeff_map ] ;
    · ext; simp [ Polynomial.coeff_derivative ] ;
  obtain ⟨ a, b, h ⟩ := h_separable_Q; replace h := congr_arg ( Polynomial.eval ( Ideal.Quotient.mk Q α ) ) h; simp_all ;

/-- A ring hom from the residue field to the algebraic closure of 𝔽_p. -/
private noncomputable def residueFieldEmbedding
    {L : Type*} [Field L] [Algebra ℚ L] [NumberField L]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ Q) :
    𝓞 L ⧸ Q →+* AlgebraicClosure (ZMod p) := by
  haveI : CharP (𝓞 L ⧸ Q) p := residue_field_charP Q hQ
  haveI : Finite (𝓞 L ⧸ Q) := residue_field_finite Q
  haveI : Fintype (𝓞 L ⧸ Q) := Fintype.ofFinite _
  haveI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  letI := ZMod.algebra (𝓞 L ⧸ Q) p
  haveI : Algebra.IsAlgebraic (ZMod p) (𝓞 L ⧸ Q) := Algebra.IsAlgebraic.of_finite _ _
  exact (IsAlgClosed.lift (R := ZMod p) (S := 𝓞 L ⧸ Q)
    (M := AlgebraicClosure (ZMod p))).toRingHom

private lemma residueFieldEmbedding_injective
    {L : Type*} [Field L] [Algebra ℚ L] [NumberField L]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ Q) :
    Function.Injective (residueFieldEmbedding Q hQ) := by
  haveI : CharP (𝓞 L ⧸ Q) p := residue_field_charP Q hQ
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  haveI : IsSimpleRing (𝓞 L ⧸ Q) := inferInstance
  exact (residueFieldEmbedding Q hQ).injective

/-- The reduction-embedding map sends roots of f over ℚ to roots of f mod p. -/
private lemma reduction_embedding_maps_root
    {L : Type*} [Field L] [Algebra ℚ L] [NumberField L]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ Q)
    (f : ℤ[X]) (hf_monic : f.Monic) (α : 𝓞 L)
    (hα : Polynomial.aeval (α : L) (f.map (Int.castRingHom ℚ)) = 0) :
    (residueFieldEmbedding Q hQ) (Ideal.Quotient.mk Q α) ∈
    (f.map (Int.castRingHom (ZMod p))).rootSet (AlgebraicClosure (ZMod p)) := by
  have h_red := reduction_of_root_is_root f Q α hα
  rw [Polynomial.mem_rootSet]
  constructor
  · exact monic_map_ne_zero f hf_monic
  · set ι := residueFieldEmbedding Q hQ
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp (Int.castRingHom (ZMod p)) =
        ι.comp (Int.castRingHom (𝓞 L ⧸ Q)) from RingHom.ext_int _ _,
      ← Polynomial.hom_eval₂ f (Int.castRingHom (𝓞 L ⧸ Q)) ι (Ideal.Quotient.mk Q α)]
    have : Polynomial.eval₂ (Int.castRingHom (𝓞 L ⧸ Q)) (Ideal.Quotient.mk Q α) f = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map] at h_red
      rwa [show (algebraMap (𝓞 L ⧸ Q) (𝓞 L ⧸ Q)).comp (Int.castRingHom (𝓞 L ⧸ Q)) =
        Int.castRingHom (𝓞 L ⧸ Q) from RingHom.ext_int _ _] at h_red
    simp [this]

/-
Injectivity of the reduction-embedding map on roots.
-/
private lemma rootReduction_injective
    (f : ℤ[X]) (hf_monic : f.Monic)
    (hf_irr : Irreducible (f.map (Int.castRingHom ℚ)))
    (h_sep : Squarefree (f.map (Int.castRingHom (ZMod p)))
    )
    {L : Type*} [Field L] [Algebra ℚ L] [NumberField L] [IsGalois ℚ L]
    [Polynomial.IsSplittingField ℚ L (f.map (Int.castRingHom ℚ))]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ Q)
    (α1 α2 : (f.map (Int.castRingHom ℚ)).rootSet L)
    (h_eq : (residueFieldEmbedding Q hQ)
      (Ideal.Quotient.mk Q (root_mem_ringOfIntegers f hf_monic (α1 : L) α1.2).choose) =
    (residueFieldEmbedding Q hQ)
      (Ideal.Quotient.mk Q (root_mem_ringOfIntegers f hf_monic (α2 : L) α2.2).choose)) :
    α1 = α2 := by
  have h_inj : (root_mem_ringOfIntegers f hf_monic α1.val α1.2).choose = (root_mem_ringOfIntegers f hf_monic α2.val α2.2).choose := by
    apply residueFieldEmbedding_injective Q hQ at h_eq;
    convert reduction_injective_on_roots_aux f hf_monic hf_irr h_sep Q hQ _ _ _ _ h_eq using 1;
    · simp [ Subtype.ext_iff ];
    · exact ( root_mem_ringOfIntegers f hf_monic α1.val α1.2 ).choose_spec ▸ Polynomial.mem_rootSet.mp α1.2 |>.2;
    · exact ( root_mem_ringOfIntegers f hf_monic α2.val α2.2 ).choose_spec.symm ▸ Polynomial.mem_rootSet.mp α2.2 |>.2;
  grind

/-
Both root sets have the same cardinality = natDegree f.
-/
private lemma rootSet_card_eq
    (f : ℤ[X]) (hf_monic : f.Monic)
    (hf_irr : Irreducible (f.map (Int.castRingHom ℚ)))
    (h_sep : Squarefree (f.map (Int.castRingHom (ZMod p))))
    {L : Type*} [Field L] [Algebra ℚ L]
    [Polynomial.IsSplittingField ℚ L (f.map (Int.castRingHom ℚ))] :
    Fintype.card ((f.map (Int.castRingHom ℚ)).rootSet L) =
    Fintype.card ((f.map (Int.castRingHom (ZMod p))).rootSet (AlgebraicClosure (ZMod p))) := by
  convert Polynomial.card_rootSet_eq_natDegree _ _;
  · convert Polynomial.card_rootSet_eq_natDegree _ _;
    · exact natDegree_map_eq_of_monic f hf_monic;
    · exact squarefree_separable_of_perfectField (map (Int.castRingHom (ZMod p)) f) h_sep;
    · exact IsAlgClosed.splits_codomain _;
  · convert Irreducible.separable hf_irr using 1;
  · convert Polynomial.IsSplittingField.splits L ( map ( Int.castRingHom ℚ ) f ) using 1

set_option maxHeartbeats 1600000 in
/-- **Frobenius lifting lemma**: For a monic f ∈ ℤ[X] with f irreducible over ℚ
and p prime with f mod p squarefree, there exists σ in the Galois group whose
action on roots has the same cycle type as the Frobenius on mod-p roots. -/
theorem frobenius_lift (f : ℤ[X]) (hf_monic : f.Monic)
    (hf_irr : Irreducible (f.map (Int.castRingHom ℚ)))
    (h_sep : Squarefree (f.map (Int.castRingHom (ZMod p)))) :
    ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
      (@Polynomial.Gal.galActionHom _ _ (f.map (Int.castRingHom ℚ)) ℂ _ _
        ⟨IsAlgClosed.splits _⟩ σ).cycleType =
      (frobeniusPermOnRoots (f.map (Int.castRingHom (ZMod p)))
        (monic_map_ne_zero f hf_monic)).cycleType := by
  -- Abbreviations
  set fQ := f.map (Int.castRingHom ℚ) with hfQ_def
  set fp := f.map (Int.castRingHom (ZMod p)) with hfp_def
  set L := fQ.SplittingField
  -- L is Galois over ℚ and a number field
  haveI : IsGalois ℚ L := IsGalois.of_separable_splitting_field hf_irr.separable
  haveI : NumberField L := ⟨⟩
  -- Get maximal ideal Q above p and Frobenius element σ
  obtain ⟨Q, hQmax, hQp⟩ := @exists_maximal_ideal_above p hp L _ _ _
  haveI := hQmax
  obtain ⟨σ, hσ⟩ := @exists_frobenius_element_over_Q p hp L _ _ _ _ Q hQmax hQp
  -- σ is our candidate
  refine ⟨σ, ?_⟩
  -- Transfer cycle type from ℂ to L (splitting field)
  rw [galActionHom_cycleType_eq]
  -- Now need: galActionHom(fQ, L, σ).cycleType = frobeniusPermOnRoots(fp).cycleType
  -- Construct the equivariant bijection
  -- Step 1: The embedding from residue field to algebraic closure
  set ι := residueFieldEmbedding (p := p) Q hQp
  -- Step 2: Define the map on roots: α ↦ ι(π(lift(α)))
  -- For α ∈ rootSet(fQ, L), lift to 𝓞 L, reduce mod Q, embed
  -- Define the map on roots
  have h_map : ∀ (α : fQ.rootSet L),
      ι (Ideal.Quotient.mk Q (root_mem_ringOfIntegers f hf_monic (α : L) α.2).choose) ∈
      fp.rootSet (AlgebraicClosure (ZMod p)) := by
    intro ⟨α, hα⟩
    apply reduction_embedding_maps_root Q hQp f hf_monic
    have hα' := (root_mem_ringOfIntegers f hf_monic α hα).choose_spec
    rw [show (((root_mem_ringOfIntegers f hf_monic α hα).choose : 𝓞 L) : L) = α from hα']
    exact (Polynomial.mem_rootSet.mp hα).2
  -- Define the function rootSet(fQ, L) → rootSet(fp, AlgClosure)
  let φ : fQ.rootSet L → fp.rootSet (AlgebraicClosure (ZMod p)) :=
    fun α => ⟨ι (Ideal.Quotient.mk Q (root_mem_ringOfIntegers f hf_monic (α : L) α.2).choose), h_map α⟩
  -- Show φ is injective
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    exact rootReduction_injective f hf_monic hf_irr h_sep Q hQp a b
      (by simpa [φ] using congr_arg Subtype.val hab)
  -- Both rootSets have the same cardinality
  have h_card : Fintype.card (fQ.rootSet L) = Fintype.card (fp.rootSet (AlgebraicClosure (ZMod p))) := by
    exact rootSet_card_eq f hf_monic hf_irr h_sep
  -- Therefore φ is a bijection → construct Equiv
  have hφ_bij : Function.Bijective φ := by
    refine ⟨hφ_inj, fun b => ?_⟩
    have h_range : Finset.image φ Finset.univ = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injective _ hφ_inj, Finset.card_univ, h_card]
    have : b ∈ Finset.image φ Finset.univ := h_range ▸ Finset.mem_univ _
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp this; exact ⟨a, ha⟩
  -- Construct the Equiv
  let e : fQ.rootSet L ≃ fp.rootSet (AlgebraicClosure (ZMod p)) := Equiv.ofBijective φ hφ_bij
  -- The galActionHom needs the Fact that fQ splits in L = SplittingField
  haveI : Fact (fQ.map (algebraMap ℚ L)).Splits := ⟨Polynomial.SplittingField.splits fQ⟩
  -- Use galActionHom = permCongr(rootsEquivRoots)(galActionAux_perm)
  -- So galActionHom.cycleType = galActionAux_perm.cycleType
  rw [galActionHom_eq_permCongr, permCongr_cycleType]
  -- Now need: galActionAux_perm(fQ, σ).cycleType = frobeniusPermOnRoots(fp).cycleType
  -- Show equivariance for galActionAux_perm (which maps ⟨x, hx⟩ to ⟨σ(x), _⟩)
  have h_equiv : ∀ x, e (galActionAux_perm fQ σ x) =
      frobeniusPermOnRoots fp (monic_map_ne_zero f hf_monic) (e x) := by
    intro x
    -- Reduce to showing underlying values are equal
    apply Subtype.ext
    -- LHS value: ι(π(lift(σ(x))))
    -- RHS value: (ι(π(lift(x))))^p  (by frobeniusPermOnRoots_val)
    have h_lift_eq : (root_mem_ringOfIntegers f hf_monic ((galActionAux_perm fQ σ) x).val ((galActionAux_perm fQ σ) x).2).choose = (galRestrict ℤ ℚ L (𝓞 L) σ (root_mem_ringOfIntegers f hf_monic x.val x.2).choose) := by
      have h_lift_eq : (root_mem_ringOfIntegers f hf_monic (galActionAux_perm fQ σ x).val (galActionAux_perm fQ σ x).2).choose.val = (galRestrict ℤ ℚ L (𝓞 L) σ (root_mem_ringOfIntegers f hf_monic x.val x.2).choose).val := by
        have := root_mem_ringOfIntegers f hf_monic (galActionAux_perm fQ σ x).val (galActionAux_perm fQ σ x).2
        have := this.choose_spec; simp_all [ galActionAux_perm_val ] ;
        have := root_mem_ringOfIntegers f hf_monic x.val x.2; have := this.choose_spec; simp_all [ galRestrict ] ;
        exact DFunLike.congr rfl (id (Eq.symm this));
      exact Subtype.ext h_lift_eq;
    aesop
  -- Conclude: cycle types are equal
  exact cycleType_eq_of_conjugate e _ _ h_equiv

/-!
## Section 4: Assembly — Dedekind's theorem from the pieces
-/

/-- **Dedekind's theorem**, proved from the Frobenius cycle type computation
and the Frobenius lifting lemma. -/
theorem dedekind_theorem' (f : ℤ[X]) (hf_monic : f.Monic)
    (hf_irr : Irreducible (f.map (Int.castRingHom ℚ)))
    (h_sep : Squarefree (f.map (Int.castRingHom (ZMod p)))) :
    ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
      (@Polynomial.Gal.galActionHom _ _ (f.map (Int.castRingHom ℚ)) ℂ _ _
        ⟨IsAlgClosed.splits _⟩ σ).cycleType =
      factorizationType (f.map (Int.castRingHom (ZMod p))) := by
  obtain ⟨σ, hσ⟩ := frobenius_lift f hf_monic hf_irr h_sep
  exact ⟨σ, hσ.trans (frobenius_cycleType_eq_factorizationType _ _ h_sep)⟩

end

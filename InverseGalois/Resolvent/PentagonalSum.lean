/-
# Pentagonal Sum and F₂₀ infrastructure for resolvent theory

This file provides:
1. The pentagonal sum function Ψ(v) = v₀v₁ + v₁v₂ + v₂v₃ + v₃v₄ + v₄v₀
2. F₂₀ = AGL(1, F₅) as a subgroup of S₅
3. Group-theoretic facts about F₂₀ (order, A₅ transitivity on S₅/F₂₀)
4. Galois compatibility of pentagonal sums
5. The algebraic identity connecting R₆ to pentagonal sums
-/

import Mathlib
import InverseGalois.Resolvent.PentagonalSumIdentities

open Polynomial Finset

noncomputable section

/-!
## § 1. Pentagonal Sum
-/

/-- The pentagonal sum of 5 elements: v₀v₁ + v₁v₂ + v₂v₃ + v₃v₄ + v₄v₀.
    This is the key expression whose orbit under S₅ determines the resolvent. -/
def pentagonalSum {L : Type*} [Ring L] (v : Fin 5 → L) : L :=
  v 0 * v 1 + v 1 * v 2 + v 2 * v 3 + v 3 * v 4 + v 4 * v 0

/-- The second elementary symmetric polynomial of 5 elements. -/
def elemSymm2 {L : Type*} [Ring L] (v : Fin 5 → L) : L :=
  v 0 * v 1 + v 0 * v 2 + v 0 * v 3 + v 0 * v 4 +
  v 1 * v 2 + v 1 * v 3 + v 1 * v 4 +
  v 2 * v 3 + v 2 * v 4 + v 3 * v 4

/-- Pentagonal sum is compatible with ring homomorphisms. -/
@[simp] lemma map_pentagonalSum {L M : Type*} [Ring L] [Ring M] (φ : L →+* M) (v : Fin 5 → L) :
    φ (pentagonalSum v) = pentagonalSum (φ ∘ v) := by
  simp [pentagonalSum, map_add, map_mul]

/-- An algebra map preserves pentagonal sums. -/
@[simp] lemma algebraMap_pentagonalSum {K L : Type*} [CommRing K] [Ring L] [Algebra K L]
    (v : Fin 5 → K) :
    algebraMap K L (pentagonalSum v) = pentagonalSum (algebraMap K L ∘ v) := by
  simp [pentagonalSum, map_add, map_mul]

/-- Galois compatibility: if σ is a ring automorphism that maps v(i) to v(π(i)),
    then σ(pentagonalSum(v)) = pentagonalSum(v ∘ π). -/
lemma galPerm_pentagonalSum {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : Fin 5 → L) (π : Equiv.Perm (Fin 5))
    (hπ : ∀ i, σ (v i) = v (π i)) :
    σ (pentagonalSum v) = pentagonalSum (v ∘ π) := by
  simp only [pentagonalSum, map_add, map_mul, hπ, Function.comp]

/-- Galois compatibility for pentagonal sum squared. -/
lemma galPerm_pentagonalSum_sq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : Fin 5 → L) (π : Equiv.Perm (Fin 5))
    (hπ : ∀ i, σ (v i) = v (π i)) :
    σ (pentagonalSum v ^ 2) = pentagonalSum (v ∘ π) ^ 2 := by
  rw [map_pow, galPerm_pentagonalSum σ v π hπ]

/-!
## § 2. F₂₀ = AGL(1, F₅)

The Frobenius group F₂₀ consists of affine linear maps x ↦ ax + b on Z/5Z,
where a ∈ {1,2,3,4} and b ∈ {0,1,2,3,4}. This gives |F₂₀| = 4 × 5 = 20.
-/

/-- A permutation of Fin 5 is affine linear if σ(x) = ax + b mod 5
    for some a ∈ (Z/5Z)* and b ∈ Z/5Z. -/
def IsAffineLinearMod5 (σ : Equiv.Perm (Fin 5)) : Prop :=
  ∃ a b : Fin 5, a ≠ 0 ∧ ∀ x : Fin 5, σ x = ⟨(a.val * x.val + b.val) % 5, by omega⟩

instance : DecidablePred IsAffineLinearMod5 := fun σ => by
  unfold IsAffineLinearMod5; infer_instance

/-- F₂₀ as a finset of Perm(Fin 5) (for computational purposes). -/
def F20_finset : Finset (Equiv.Perm (Fin 5)) :=
  Finset.univ.filter IsAffineLinearMod5

/-- F₂₀ has exactly 20 elements. -/
lemma F20_finset_card : F20_finset.card = 20 := by native_decide

/-- A₅ as a finset (even permutations). -/
def A5_finset : Finset (Equiv.Perm (Fin 5)) :=
  Finset.univ.filter (fun σ => Equiv.Perm.sign σ = 1)

/-- A₅ has 60 elements. -/
lemma A5_finset_card : A5_finset.card = 60 := by native_decide

/-- The product set A₅ · F₂₀ equals all of S₅.
    This implies A₅ acts transitively on S₅/F₂₀. -/
lemma A5_mul_F20_eq_univ :
    (A5_finset.biUnion (fun a => F20_finset.image (fun f => a * f))) = Finset.univ := by
  native_decide

set_option linter.constructorNameAsVariable false in
/-- Every element of S₅ can be written as a product of an element of A₅ and
    an element of F₂₀. This is the key group-theoretic fact for the resolvent theory. -/
lemma exists_A5_F20_factorization (σ : Equiv.Perm (Fin 5)) :
    ∃ α : Equiv.Perm (Fin 5), ∃ g : Equiv.Perm (Fin 5),
      Equiv.Perm.sign α = 1 ∧ IsAffineLinearMod5 g ∧ σ = α * g := by
  have h := A5_mul_F20_eq_univ
  have hσ : σ ∈ (A5_finset.biUnion (fun a => F20_finset.image (fun g => a * g))) := by
    rw [h]; exact Finset.mem_univ _
  simp only [A5_finset, F20_finset, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and] at hσ
  obtain ⟨a, ha_sign, g, hg_aff, hprod⟩ := hσ
  exact ⟨a, g, ha_sign, hg_aff, hprod.symm⟩

/-!
## § 2.5. F₂₀ stabilizes pentagonal sum squared

The key ring-theoretic facts:
- For σ ∈ F₂₀ with a ∈ {1,4}: Ψ(v∘σ) = Ψ(v) (free polynomial identity)
- For σ ∈ F₂₀ with a ∈ {2,3}: Ψ(v∘σ) + Ψ(v) = e₂(v) (free polynomial identity)
- When e₂(v) = 0: Ψ(v∘σ)² = Ψ(v)² for all σ ∈ F₂₀
-/

set_option maxHeartbeats 400000 in
/-- For any σ ∈ F₂₀, Ψ(v∘σ)² = Ψ(v)² when e₂(v) = 0. -/
lemma pentagonalSum_sq_F20_inv {L : Type*} [CommRing L] (v : Fin 5 → L)
    (he2 : elemSymm2 v = 0) (σ : Equiv.Perm (Fin 5)) (hσ : IsAffineLinearMod5 σ) :
    pentagonalSum (v ∘ σ) ^ 2 = pentagonalSum v ^ 2 := by
  obtain ⟨ a, b, ha, hb ⟩ := hσ;
  fin_cases a <;> simp +decide at ha hb ⊢;
  · fin_cases b <;> simp +decide [ hb, pentagonalSum ] <;> ring!;
  · fin_cases b <;> simp +decide [ hb, pentagonalSum ] at he2 ⊢;
    · unfold elemSymm2 at he2;
      grind +ring;
    · unfold elemSymm2 at he2;
      grobner;
    · unfold elemSymm2 at he2;
      grind +ring;
    · unfold elemSymm2 at he2; simp_all +decide [ Fin.forall_fin_succ ] ;
      grind +ring;
    · unfold elemSymm2 at he2;
      grind;
  · -- For σ ∈ F₂₀ with a ∈ {2,3}: Ψ(v∘σ) + Ψ(v) = e₂(v) (free polynomial identity)
    have h_case3 : pentagonalSum (v ∘ σ) + pentagonalSum v = elemSymm2 v := by
      fin_cases b <;> simp +decide [ hb, pentagonalSum, elemSymm2 ] <;> ring!;
    grind;
  · fin_cases b <;> simp +decide [ hb, pentagonalSum ] at he2 ⊢;
    · ring;
    · ring;
    · grind +qlia;
    · unfold elemSymm2 at he2; simp_all +decide [ Fin.forall_fin_succ ] ; ring;
    · grind

/-- The second elementary symmetric function is invariant under permutations. -/
lemma elemSymm2_perm {L : Type*} [CommRing L] (v : Fin 5 → L)
    (σ : Equiv.Perm (Fin 5)) : elemSymm2 (v ∘ σ) = elemSymm2 v := by
  unfold elemSymm2;
  induction' σ using Equiv.Perm.swap_induction_on' with τ hτ ih;
  · rfl;
  · simp_all +decide [ Equiv.swap_apply_def ];
    grind

/-- The multiset esymm 2 of the roots of the mapped polynomial equals 0
    for f = X⁵+pX+q. This is the Vieta relation for the coefficient of X³. -/
lemma roots_esymm2_zero {K : Type*} [Field K]
    (p q : K) (f : K[X])
    (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q) :
    (Polynomial.map (algebraMap K f.SplittingField) f).roots.esymm 2 = 0 := by
  have hf_monic : f.Monic := by
    rw [hf, show (Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q : K[X]) =
      Polynomial.X ^ 5 + (Polynomial.C p * Polynomial.X + Polynomial.C q) from by ring]
    apply Polynomial.Monic.add_of_left (Polynomial.monic_X_pow 5)
    calc Polynomial.degree (Polynomial.C p * Polynomial.X + Polynomial.C q : K[X])
        ≤ max (Polynomial.degree (Polynomial.C p * Polynomial.X))
              (Polynomial.degree (Polynomial.C q)) := Polynomial.degree_add_le _ _
      _ ≤ max 1 0 := max_le_max (Polynomial.degree_C_mul_X_le p) Polynomial.degree_C_le
      _ < (5 : ℕ) := by norm_num
      _ = Polynomial.degree ((Polynomial.X : K[X]) ^ 5) := by simp
  have hf_splits := Polynomial.IsSplittingField.splits f.SplittingField f
  have hnd : (Polynomial.map (algebraMap K f.SplittingField) f).natDegree = 5 := by
    rw [Polynomial.natDegree_map, hf,
        show (Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q : K[X]) =
          (Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X) + Polynomial.C q from by ring,
        Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · have : (Polynomial.C p * Polynomial.X : K[X]) = Polynomial.C p * Polynomial.X ^ 1 := by ring
      rw [this]
      calc Polynomial.natDegree (Polynomial.C p * Polynomial.X ^ 1 : K[X])
          ≤ 1 := Polynomial.natDegree_C_mul_X_pow_le p 1
        _ < _ := by simp
  have h_vieta := Polynomial.coeff_eq_esymm_roots_of_splits hf_splits (k := 3) (by omega : 3 ≤ _)
  rw [hnd] at h_vieta
  simp only [Polynomial.leadingCoeff_map, hf_monic.leadingCoeff, map_one, one_mul,
             show 5 - 3 = 2 from rfl, neg_one_sq] at h_vieta
  rw [← h_vieta, Polynomial.coeff_map, hf]
  simp [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_X,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Finset.antidiagonal]

set_option maxHeartbeats 2000000 in
/-- The coefficient of X³ in a product of 5 linear factors is the second
    elementary symmetric polynomial of the roots. -/
lemma coeff3_prod5 {R : Type*} [CommRing R] (a : Fin 5 → R) :
    ((Polynomial.X - Polynomial.C (a 0)) * (Polynomial.X - Polynomial.C (a 1)) *
     (Polynomial.X - Polynomial.C (a 2)) * (Polynomial.X - Polynomial.C (a 3)) *
     (Polynomial.X - Polynomial.C (a 4))).coeff 3 =
    elemSymm2 a := by
  simp [elemSymm2, Polynomial.coeff_mul, Polynomial.coeff_sub,
        Polynomial.coeff_X, Polynomial.coeff_C, Finset.antidiagonal]
  ring

/-
In the splitting field, map f equals the product of linear factors (X - C (v i)).
-/
lemma map_eq_prod_linear {K : Type*} [Field K]
    (p q : K) (f : K[X])
    (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (v : Fin 5 ≃ f.rootSet f.SplittingField) :
    Polynomial.map (algebraMap K f.SplittingField) f =
    (Polynomial.X - Polynomial.C (v 0 : f.SplittingField)) *
    (Polynomial.X - Polynomial.C (v 1 : f.SplittingField)) *
    (Polynomial.X - Polynomial.C (v 2 : f.SplittingField)) *
    (Polynomial.X - Polynomial.C (v 3 : f.SplittingField)) *
    (Polynomial.X - Polynomial.C (v 4 : f.SplittingField)) := by
  -- Let $g = \text{map}(\text{algebraMap}(K, L)) f$ where $L = f.\text{SplittingField}$.
  set g : Polynomial (f.SplittingField) := Polynomial.map (algebraMap K f.SplittingField) f;
  -- Since $g$ is monic and has degree 5, and $(X - C (v i))$ are distinct linear factors, their product divides $g$.
  have h_div : (∏ i : Fin 5, (Polynomial.X - Polynomial.C (v i : f.SplittingField))) ∣ g := by
    refine' Finset.prod_dvd_of_coprime _ _;
    · intros i hi j hj hij; have := Polynomial.irreducible_X_sub_C ( v i : f.SplittingField ) ; have := Polynomial.irreducible_X_sub_C ( v j : f.SplittingField ) ; simp_all +decide [Polynomial.irreducible_X_sub_C] ;
      refine' ( Polynomial.pairwise_coprime_X_sub_C _ ) hij;
      exact Subtype.coe_injective.comp v.injective;
    · intro i _; erw [ Polynomial.dvd_iff_isRoot ] ; simp +decide ;
      have := v i |>.2; simp_all +decide [ Polynomial.mem_rootSet ] ;
      aesop;
  obtain ⟨ q, hq ⟩ := h_div;
  -- Since $g$ is monic and has degree 5, and $(X - C (v i))$ are distinct linear factors, their product must equal $g$.
  have h_deg : g.degree = 5 := by
    rw [ Polynomial.degree_map, hf, Polynomial.degree_add_C ] <;> erw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> by_cases h : p = 0 <;> simp +decide [ h ]
  have h_deg_prod : (∏ i : Fin 5, (Polynomial.X - Polynomial.C (v i : f.SplittingField))).degree = 5 := by
    simp +decide [ Polynomial.degree_prod ]
  have h_deg_q : q.degree = 0 := by
    rw [ hq, Polynomial.degree_mul, h_deg_prod ] at h_deg ; rw [ Polynomial.degree_eq_natDegree ] at * <;> norm_cast at * <;> aesop_cat;
  have h_q_const : ∃ c : f.SplittingField, q = Polynomial.C c := by
    exact ⟨ q.coeff 0, Polynomial.eq_C_of_degree_eq_zero h_deg_q ⟩
  obtain ⟨ c, hc ⟩ := h_q_const
  have h_c_one : c = 1 := by
    replace hq := congr_arg Polynomial.leadingCoeff hq ; simp_all +decide [ Polynomial.leadingCoeff_prod ] ;
    rw [ ← hq, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero ] <;> norm_num [ hf ];
    · rw [ Polynomial.leadingCoeff, Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases hp : p = 0 <;> simp +decide [ hp ];
    · exact ne_of_apply_ne ( fun f => f.coeff 5 ) ( by norm_num [ Polynomial.coeff_eq_zero_of_natDegree_lt ] )
  simp_all +decide [ Fin.prod_univ_five ]

set_option maxHeartbeats 2000000 in
/-- For roots of X⁵+pX+q, the second elementary symmetric polynomial vanishes. -/
lemma roots_e2_zero {K : Type*} [Field K]
    (p q : K) (f : K[X])
    (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (v : Fin 5 ≃ f.rootSet f.SplittingField) :
    elemSymm2 (fun i => (v i : f.SplittingField)) = 0 := by
  have h1 := map_eq_prod_linear p q f hf v
  have h2 := coeff3_prod5 (fun i => (v i : f.SplittingField))
  rw [← h2, ← h1, Polynomial.coeff_map, hf]
  simp [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_X,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Finset.antidiagonal]

/-!
## § 3. Resolvent-Pentagonal Sum Connection
-/

variable {K : Type*} [Field K] [CharZero K]

/-- The sextic resolvent polynomial. -/
def sexticResolventLocal (p q : K) : K[X] :=
  Polynomial.X ^ 6 - Polynomial.C (10 * p) * Polynomial.X ^ 5
    + Polynomial.C (55 * p ^ 2) * Polynomial.X ^ 4
    - Polynomial.C (140 * p ^ 3) * Polynomial.X ^ 3
    + Polynomial.C (175 * p ^ 4) * Polynomial.X ^ 2
    - Polynomial.C (106 * p ^ 5 + 3125 * q ^ 4) * Polynomial.X
    + Polynomial.C (25 * p ^ 6)

/-!
### Helper infrastructure for the resolvent–pentagonal-sum factorisation -/

/-- Coefficient `4` of a product of five monic linear factors is `-(Σ aᵢ)`. -/
lemma coeff4_prod5 {R : Type*} [CommRing R] (a : Fin 5 → R) :
    ((Polynomial.X - Polynomial.C (a 0)) * (Polynomial.X - Polynomial.C (a 1)) *
     (Polynomial.X - Polynomial.C (a 2)) * (Polynomial.X - Polynomial.C (a 3)) *
     (Polynomial.X - Polynomial.C (a 4))).coeff 4 =
    -(a 0 + a 1 + a 2 + a 3 + a 4) := by
  simp [Polynomial.coeff_mul, Polynomial.coeff_sub,
        Polynomial.coeff_X, Polynomial.coeff_C, Finset.antidiagonal]
  ring

/-- Coefficient `2` of a product of five monic linear factors is `-(e₃)`. -/
lemma coeff2_prod5 {R : Type*} [CommRing R] (a : Fin 5 → R) :
    ((Polynomial.X - Polynomial.C (a 0)) * (Polynomial.X - Polynomial.C (a 1)) *
     (Polynomial.X - Polynomial.C (a 2)) * (Polynomial.X - Polynomial.C (a 3)) *
     (Polynomial.X - Polynomial.C (a 4))).coeff 2 =
    -(a 0*a 1*a 2 + a 0*a 1*a 3 + a 0*a 1*a 4 + a 0*a 2*a 3 + a 0*a 2*a 4 + a 0*a 3*a 4
      + a 1*a 2*a 3 + a 1*a 2*a 4 + a 1*a 3*a 4 + a 2*a 3*a 4) := by
  simp [Polynomial.coeff_mul, Polynomial.coeff_sub,
        Polynomial.coeff_X, Polynomial.coeff_C, Finset.antidiagonal]
  ring

/-- Coefficient `1` of a product of five monic linear factors is `e₄`. -/
lemma coeff1_prod5 {R : Type*} [CommRing R] (a : Fin 5 → R) :
    ((Polynomial.X - Polynomial.C (a 0)) * (Polynomial.X - Polynomial.C (a 1)) *
     (Polynomial.X - Polynomial.C (a 2)) * (Polynomial.X - Polynomial.C (a 3)) *
     (Polynomial.X - Polynomial.C (a 4))).coeff 1 =
    (a 0*a 1*a 2*a 3 + a 0*a 1*a 2*a 4 + a 0*a 1*a 3*a 4 + a 0*a 2*a 3*a 4 + a 1*a 2*a 3*a 4) := by
  simp [Polynomial.coeff_mul, Polynomial.coeff_sub,
        Polynomial.coeff_X, Polynomial.coeff_C, Finset.antidiagonal]
  ring

/-- Coefficient `0` of a product of five monic linear factors is `-(∏ aᵢ)`. -/
lemma coeff0_prod5 {R : Type*} [CommRing R] (a : Fin 5 → R) :
    ((Polynomial.X - Polynomial.C (a 0)) * (Polynomial.X - Polynomial.C (a 1)) *
     (Polynomial.X - Polynomial.C (a 2)) * (Polynomial.X - Polynomial.C (a 3)) *
     (Polynomial.X - Polynomial.C (a 4))).coeff 0 =
    -(a 0*a 1*a 2*a 3*a 4) := by
  simp [Polynomial.coeff_mul, Polynomial.coeff_sub,
        Polynomial.coeff_X, Polynomial.coeff_C, Finset.antidiagonal]

omit [CharZero K] in
/-- Evaluation of the sextic resolvent at a point `y` of a `K`-algebra `L`. -/
lemma eval₂_sexticResolventLocal_eq {L : Type*} [CommRing L] [Algebra K L] (p q : K) (y : L) :
    Polynomial.eval₂ (algebraMap K L) y (sexticResolventLocal p q) =
      y ^ 6 - 10 * (algebraMap K L p) * y ^ 5 + 55 * (algebraMap K L p) ^ 2 * y ^ 4
        - 140 * (algebraMap K L p) ^ 3 * y ^ 3 + 175 * (algebraMap K L p) ^ 4 * y ^ 2
        - (106 * (algebraMap K L p) ^ 5 + 3125 * (algebraMap K L q) ^ 4) * y
        + 25 * (algebraMap K L p) ^ 6 := by
  simp only [sexticResolventLocal, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    map_add, map_mul, map_pow, map_ofNat, Polynomial.eval₂_ofNat]

omit [CharZero K] in
/-- The Vieta relations for the roots `w i = v i` of `f = X⁵ + pX + q`:
    `e₁ = e₂ = e₃ = 0`, `e₄ = p`, `e₅ = -q`. -/
lemma vieta_pentagon (p q : K)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (v : Fin 5 ≃ f.rootSet f.SplittingField) :
    ((v 0 : f.SplittingField) + v 1 + v 2 + v 3 + v 4 = 0) ∧
    ((v 0 : f.SplittingField)*v 1+v 0*v 2+v 0*v 3+v 0*v 4+v 1*v 2+v 1*v 3+v 1*v 4+v 2*v 3+v 2*v 4+v 3*v 4 = 0) ∧
    ((v 0 : f.SplittingField)*v 1*v 2+v 0*v 1*v 3+v 0*v 1*v 4+v 0*v 2*v 3+v 0*v 2*v 4+v 0*v 3*v 4+v 1*v 2*v 3+v 1*v 2*v 4+v 1*v 3*v 4+v 2*v 3*v 4 = 0) ∧
    ((v 0 : f.SplittingField)*v 1*v 2*v 3+v 0*v 1*v 2*v 4+v 0*v 1*v 3*v 4+v 0*v 2*v 3*v 4+v 1*v 2*v 3*v 4 = algebraMap K f.SplittingField p) ∧
    ((v 0 : f.SplittingField)*v 1*v 2*v 3*v 4 = - algebraMap K f.SplittingField q) := by
  have hmap := map_eq_prod_linear p q f hf v
  have hc4 : (Polynomial.map (algebraMap K f.SplittingField) f).coeff 4 = 0 := by
    rw [hf]; simp [Polynomial.coeff_add, Polynomial.coeff_X_pow]
  have hc2 : (Polynomial.map (algebraMap K f.SplittingField) f).coeff 2 = 0 := by
    rw [hf]; simp [Polynomial.coeff_add, Polynomial.coeff_X_pow]
  have hc1 : (Polynomial.map (algebraMap K f.SplittingField) f).coeff 1
      = algebraMap K f.SplittingField p := by
    rw [hf]; simp [Polynomial.coeff_add, Polynomial.coeff_X_pow]
  have hc0 : (Polynomial.map (algebraMap K f.SplittingField) f).coeff 0
      = algebraMap K f.SplittingField q := by
    rw [hf]; simp [Polynomial.coeff_add, Polynomial.coeff_X_pow]
  rw [hmap, coeff4_prod5 (fun i => (v i : f.SplittingField))] at hc4
  rw [hmap, coeff2_prod5 (fun i => (v i : f.SplittingField))] at hc2
  rw [hmap, coeff1_prod5 (fun i => (v i : f.SplittingField))] at hc1
  rw [hmap, coeff0_prod5 (fun i => (v i : f.SplittingField))] at hc0
  refine ⟨neg_eq_zero.mp hc4, ?_, neg_eq_zero.mp hc2, hc1, by linear_combination -hc0⟩
  have h2 := roots_e2_zero p q f hf v
  simpa [elemSymm2] using h2

/-- The six coset representatives of `F₂₀` in `S₅`: the permutations fixing `0,1`
    (i.e. the permutations of `{2,3,4}`). -/
def pentRep : Fin 6 → Equiv.Perm (Fin 5) :=
  ![1, Equiv.swap 3 4, Equiv.swap 2 3,
    Equiv.swap 2 4 * Equiv.swap 2 3, Equiv.swap 2 3 * Equiv.swap 2 4, Equiv.swap 2 4]

/-- The six pentagonal-sum-squares as a function of the roots `w`. -/
def pentSqVal {L : Type*} [CommRing L] (w : Fin 5 → L) : Fin 6 → L :=
  ![ (w 0*w 1+w 1*w 2+w 2*w 3+w 3*w 4+w 4*w 0)^2,
     (w 0*w 1+w 1*w 2+w 2*w 4+w 4*w 3+w 3*w 0)^2,
     (w 0*w 1+w 1*w 3+w 3*w 2+w 2*w 4+w 4*w 0)^2,
     (w 0*w 1+w 1*w 3+w 3*w 4+w 4*w 2+w 2*w 0)^2,
     (w 0*w 1+w 1*w 4+w 4*w 2+w 2*w 3+w 3*w 0)^2,
     (w 0*w 1+w 1*w 4+w 4*w 3+w 3*w 2+w 2*w 0)^2 ]

/-- The pentagonal sum of `w ∘ pentRep j`, squared, equals the `j`-th pentagonal-sum-square. -/
lemma pentRep_sq_eq {L : Type*} [CommRing L] (w : Fin 5 → L) (j : Fin 6) :
    pentagonalSum (fun i => w (pentRep j i)) ^ 2 = pentSqVal w j := by
  fin_cases j <;>
    simp [pentRep, pentSqVal, pentagonalSum, Equiv.swap_apply_def, Equiv.Perm.mul_apply]

/-- Every permutation of `Fin 5` lies in some `F₂₀`-coset `pentRep j · F₂₀`. -/
lemma pentRep_cover (σ : Equiv.Perm (Fin 5)) :
    ∃ j : Fin 6, IsAffineLinearMod5 ((pentRep j)⁻¹ * σ) := by
  revert σ; native_decide

/-- The sextic-resolvent value factors as `∏_j (y − a_j)`, given the six
    elementary-symmetric identities of the `a_j`. -/
lemma resolvent_eq_prod {L : Type*} [CommRing L]
    (a0 a1 a2 a3 a4 a5 p q : L)
    (e1 : a0 + a1 + a2 + a3 + a4 + a5 = 10 * p)
    (e2 : a0*a1 + a0*a2 + a0*a3 + a0*a4 + a0*a5 + a1*a2 + a1*a3 + a1*a4 + a1*a5
        + a2*a3 + a2*a4 + a2*a5 + a3*a4 + a3*a5 + a4*a5 = 55 * p ^ 2)
    (e3 : a0*a1*a2 + a0*a1*a3 + a0*a1*a4 + a0*a1*a5 + a0*a2*a3 + a0*a2*a4 + a0*a2*a5
        + a0*a3*a4 + a0*a3*a5 + a0*a4*a5 + a1*a2*a3 + a1*a2*a4 + a1*a2*a5 + a1*a3*a4
        + a1*a3*a5 + a1*a4*a5 + a2*a3*a4 + a2*a3*a5 + a2*a4*a5 + a3*a4*a5 = 140 * p ^ 3)
    (e4 : a0*a1*a2*a3 + a0*a1*a2*a4 + a0*a1*a2*a5 + a0*a1*a3*a4 + a0*a1*a3*a5 + a0*a1*a4*a5
        + a0*a2*a3*a4 + a0*a2*a3*a5 + a0*a2*a4*a5 + a0*a3*a4*a5 + a1*a2*a3*a4 + a1*a2*a3*a5
        + a1*a2*a4*a5 + a1*a3*a4*a5 + a2*a3*a4*a5 = 175 * p ^ 4)
    (e5 : a0*a1*a2*a3*a4 + a0*a1*a2*a3*a5 + a0*a1*a2*a4*a5 + a0*a1*a3*a4*a5
        + a0*a2*a3*a4*a5 + a1*a2*a3*a4*a5 = 106 * p ^ 5 + 3125 * q ^ 4)
    (e6 : a0*a1*a2*a3*a4*a5 = 25 * p ^ 6)
    (y : L) :
    y ^ 6 - 10 * p * y ^ 5 + 55 * p ^ 2 * y ^ 4 - 140 * p ^ 3 * y ^ 3
      + 175 * p ^ 4 * y ^ 2 - (106 * p ^ 5 + 3125 * q ^ 4) * y + 25 * p ^ 6
      = (y - a0) * (y - a1) * (y - a2) * (y - a3) * (y - a4) * (y - a5) := by
  linear_combination y^5*e1 - y^4*e2 + y^3*e3 - y^2*e4 + y*e5 - e6

/-- The six elementary-symmetric identities for `a_j := pentSqVal w j`, where `w` are the
    roots of `f = X⁵ + pX + q`, with the constants expressed via the Vieta values
    `algebraMap p`, `algebraMap q`. -/
lemma pentSqVal_esymm_pure {L : Type*} [CommRing L] (w : Fin 5 → L) (P Q : L)
    (he1 : w 0 + w 1 + w 2 + w 3 + w 4 = 0)
    (he2 : w 0*w 1+w 0*w 2+w 0*w 3+w 0*w 4+w 1*w 2+w 1*w 3+w 1*w 4+w 2*w 3+w 2*w 4+w 3*w 4 = 0)
    (he3 : w 0*w 1*w 2+w 0*w 1*w 3+w 0*w 1*w 4+w 0*w 2*w 3+w 0*w 2*w 4+w 0*w 3*w 4+w 1*w 2*w 3+w 1*w 2*w 4+w 1*w 3*w 4+w 2*w 3*w 4 = 0)
    (he4 : w 0*w 1*w 2*w 3+w 0*w 1*w 2*w 4+w 0*w 1*w 3*w 4+w 0*w 2*w 3*w 4+w 1*w 2*w 3*w 4 = P)
    (he5 : w 0*w 1*w 2*w 3*w 4 = -Q) :
    (pentSqVal w 0 + pentSqVal w 1 + pentSqVal w 2 + pentSqVal w 3 + pentSqVal w 4 + pentSqVal w 5 = 10 * P) ∧
    (pentSqVal w 0*pentSqVal w 1 + pentSqVal w 0*pentSqVal w 2 + pentSqVal w 0*pentSqVal w 3 + pentSqVal w 0*pentSqVal w 4 + pentSqVal w 0*pentSqVal w 5 + pentSqVal w 1*pentSqVal w 2 + pentSqVal w 1*pentSqVal w 3 + pentSqVal w 1*pentSqVal w 4 + pentSqVal w 1*pentSqVal w 5 + pentSqVal w 2*pentSqVal w 3 + pentSqVal w 2*pentSqVal w 4 + pentSqVal w 2*pentSqVal w 5 + pentSqVal w 3*pentSqVal w 4 + pentSqVal w 3*pentSqVal w 5 + pentSqVal w 4*pentSqVal w 5 = 55 * P ^ 2) ∧
    (pentSqVal w 0*pentSqVal w 1*pentSqVal w 2 + pentSqVal w 0*pentSqVal w 1*pentSqVal w 3 + pentSqVal w 0*pentSqVal w 1*pentSqVal w 4 + pentSqVal w 0*pentSqVal w 1*pentSqVal w 5 + pentSqVal w 0*pentSqVal w 2*pentSqVal w 3 + pentSqVal w 0*pentSqVal w 2*pentSqVal w 4 + pentSqVal w 0*pentSqVal w 2*pentSqVal w 5 + pentSqVal w 0*pentSqVal w 3*pentSqVal w 4 + pentSqVal w 0*pentSqVal w 3*pentSqVal w 5 + pentSqVal w 0*pentSqVal w 4*pentSqVal w 5 + pentSqVal w 1*pentSqVal w 2*pentSqVal w 3 + pentSqVal w 1*pentSqVal w 2*pentSqVal w 4 + pentSqVal w 1*pentSqVal w 2*pentSqVal w 5 + pentSqVal w 1*pentSqVal w 3*pentSqVal w 4 + pentSqVal w 1*pentSqVal w 3*pentSqVal w 5 + pentSqVal w 1*pentSqVal w 4*pentSqVal w 5 + pentSqVal w 2*pentSqVal w 3*pentSqVal w 4 + pentSqVal w 2*pentSqVal w 3*pentSqVal w 5 + pentSqVal w 2*pentSqVal w 4*pentSqVal w 5 + pentSqVal w 3*pentSqVal w 4*pentSqVal w 5 = 140 * P ^ 3) ∧
    (pentSqVal w 0*pentSqVal w 1*pentSqVal w 2*pentSqVal w 3 + pentSqVal w 0*pentSqVal w 1*pentSqVal w 2*pentSqVal w 4 + pentSqVal w 0*pentSqVal w 1*pentSqVal w 2*pentSqVal w 5 + pentSqVal w 0*pentSqVal w 1*pentSqVal w 3*pentSqVal w 4 + pentSqVal w 0*pentSqVal w 1*pentSqVal w 3*pentSqVal w 5 + pentSqVal w 0*pentSqVal w 1*pentSqVal w 4*pentSqVal w 5 + pentSqVal w 0*pentSqVal w 2*pentSqVal w 3*pentSqVal w 4 + pentSqVal w 0*pentSqVal w 2*pentSqVal w 3*pentSqVal w 5 + pentSqVal w 0*pentSqVal w 2*pentSqVal w 4*pentSqVal w 5 + pentSqVal w 0*pentSqVal w 3*pentSqVal w 4*pentSqVal w 5 + pentSqVal w 1*pentSqVal w 2*pentSqVal w 3*pentSqVal w 4 + pentSqVal w 1*pentSqVal w 2*pentSqVal w 3*pentSqVal w 5 + pentSqVal w 1*pentSqVal w 2*pentSqVal w 4*pentSqVal w 5 + pentSqVal w 1*pentSqVal w 3*pentSqVal w 4*pentSqVal w 5 + pentSqVal w 2*pentSqVal w 3*pentSqVal w 4*pentSqVal w 5 = 175 * P ^ 4) ∧
    (pentSqVal w 0*pentSqVal w 1*pentSqVal w 2*pentSqVal w 3*pentSqVal w 4 + pentSqVal w 0*pentSqVal w 1*pentSqVal w 2*pentSqVal w 3*pentSqVal w 5 + pentSqVal w 0*pentSqVal w 1*pentSqVal w 2*pentSqVal w 4*pentSqVal w 5 + pentSqVal w 0*pentSqVal w 1*pentSqVal w 3*pentSqVal w 4*pentSqVal w 5 + pentSqVal w 0*pentSqVal w 2*pentSqVal w 3*pentSqVal w 4*pentSqVal w 5 + pentSqVal w 1*pentSqVal w 2*pentSqVal w 3*pentSqVal w 4*pentSqVal w 5 = 106 * P ^ 5 + 3125 * Q ^ 4) ∧
    (pentSqVal w 0*pentSqVal w 1*pentSqVal w 2*pentSqVal w 3*pentSqVal w 4*pentSqVal w 5 = 25 * P ^ 6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [pentSqVal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  · rw [PentagonalSumIdentities.psSq_esymm1 (w 0) (w 1) (w 2) (w 3) (w 4) he1 he2 he3, he4]
  · rw [PentagonalSumIdentities.psSq_esymm2 (w 0) (w 1) (w 2) (w 3) (w 4) he1 he2 he3, he4]
  · rw [PentagonalSumIdentities.psSq_esymm3 (w 0) (w 1) (w 2) (w 3) (w 4) he1 he2 he3, he4]
  · rw [PentagonalSumIdentities.psSq_esymm4 (w 0) (w 1) (w 2) (w 3) (w 4) he1 he2 he3, he4]
  · rw [PentagonalSumIdentities.psSq_esymm5 (w 0) (w 1) (w 2) (w 3) (w 4) he1 he2 he3, he4, he5]; ring
  · rw [PentagonalSumIdentities.psSq_esymm6 (w 0) (w 1) (w 2) (w 3) (w 4) he1 he2 he3, he4]

omit [CharZero K] in
/-- Backward direction: F₂₀ coset implies equal pentagonal sums squared. -/
lemma pentagonalSum_sq_eq_of_F20_coset
    {L : Type*} [CommRing L] (v : Fin 5 → L) (he2 : elemSymm2 v = 0)
    (σ₁ σ₂ : Equiv.Perm (Fin 5))
    (hF20 : IsAffineLinearMod5 (σ₁⁻¹ * σ₂)) :
    pentagonalSum (fun i => v (σ₁ i)) ^ 2 =
    pentagonalSum (fun i => v (σ₂ i)) ^ 2 := by
  -- Rewrite v∘σ₂ as (v∘σ₁)∘(σ₁⁻¹*σ₂)
  have hconv : (fun i => v (σ₂ i)) =
    (fun i => v (σ₁ ((σ₁⁻¹ * σ₂) i))) := by
    ext i; congr 1; simp [Equiv.Perm.mul_apply]
  rw [hconv]
  -- Now apply pentagonalSum_sq_F20_inv
  exact (pentagonalSum_sq_F20_inv
    (fun i => v (σ₁ i))
    (by rw [← Function.comp_def, elemSymm2_perm, he2])
    (σ₁⁻¹ * σ₂) hF20).symm

omit [CharZero K] in
/-- For roots `v` of `f = X⁵+pX+q`, the sextic resolvent `R₆` evaluated at
    `pentagonalSum(v ∘ σ)²` is zero for any `σ ∈ S₅`.

    The identity was also numerically verified over GF(101) with p=8, q=34, where X⁵+8X+34
    splits with roots [66,76,82,84,96], confirming R₆(Ψ²) = 0 for all six values. -/
lemma sexticResolvent_pentagonalSum_root
    (p q : K)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (v : Fin 5 ≃ f.rootSet f.SplittingField)
    (σ : Equiv.Perm (Fin 5)) :
    Polynomial.eval₂ (algebraMap K f.SplittingField)
      (pentagonalSum (fun i => (v (σ i) : f.SplittingField)) ^ 2)
      (sexticResolventLocal p q) = 0 := by
  rw [eval₂_sexticResolventLocal_eq]
  set y := pentagonalSum (fun i => (v (σ i) : f.SplittingField)) ^ 2 with hydef
  obtain ⟨he1, he2, he3, he4, he5⟩ :=
    vieta_pentagon p q f hf v
  obtain ⟨E1, E2, E3, E4, E5, E6⟩ :=
    pentSqVal_esymm_pure (fun i => (v i : f.SplittingField))
      (algebraMap K f.SplittingField p) (algebraMap K f.SplittingField q) he1 he2 he3 he4 he5
  rw [resolvent_eq_prod _ _ _ _ _ _ _ _ E1 E2 E3 E4 E5 E6]
  obtain ⟨j, hj⟩ := pentRep_cover σ
  have hy : y = pentSqVal (fun i => (v i : f.SplittingField)) j := by
    rw [hydef, ← pentRep_sq_eq (fun i => (v i : f.SplittingField)) j]
    exact (pentagonalSum_sq_eq_of_F20_coset (fun i => (v i : f.SplittingField))
      (roots_e2_zero p q f hf v) (pentRep j) σ hj).symm
  rw [show (y - pentSqVal (fun i => (v i : f.SplittingField)) 0) * (y - pentSqVal (fun i => (v i : f.SplittingField)) 1) * (y - pentSqVal (fun i => (v i : f.SplittingField)) 2) * (y - pentSqVal (fun i => (v i : f.SplittingField)) 3) * (y - pentSqVal (fun i => (v i : f.SplittingField)) 4) * (y - pentSqVal (fun i => (v i : f.SplittingField)) 5)
        = ∏ k : Fin 6, (y - pentSqVal (fun i => (v i : f.SplittingField)) k)
      from (Fin.prod_univ_six (fun k => y - pentSqVal (fun i => (v i : f.SplittingField)) k)).symm]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_eq_zero.mpr hy)

omit [CharZero K] in
/-- The 6 pentagonal sums squared are the only roots of `R₆` in the splitting field.
    This factorization needs neither `p ≠ 0` nor irreducibility: it holds for all `p, q`. -/
lemma sexticResolvent_roots_are_pentagonalSums
    (p q : K)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (v : Fin 5 ≃ f.rootSet f.SplittingField)
    (y : f.SplittingField)
    (hy : Polynomial.eval₂ (algebraMap K f.SplittingField) y (sexticResolventLocal p q) = 0) :
    ∃ σ : Equiv.Perm (Fin 5),
      y = pentagonalSum (fun i => (v (σ i) : f.SplittingField)) ^ 2 := by
  rw [eval₂_sexticResolventLocal_eq] at hy
  obtain ⟨he1, he2, he3, he4, he5⟩ :=
    vieta_pentagon p q f hf v
  obtain ⟨E1, E2, E3, E4, E5, E6⟩ :=
    pentSqVal_esymm_pure (fun i => (v i : f.SplittingField))
      (algebraMap K f.SplittingField p) (algebraMap K f.SplittingField q) he1 he2 he3 he4 he5
  rw [resolvent_eq_prod _ _ _ _ _ _ _ _ E1 E2 E3 E4 E5 E6] at hy
  simp only [mul_eq_zero, sub_eq_zero] at hy
  rcases hy with ((((h|h)|h)|h)|h)|h
  · exact ⟨pentRep 0, by rw [h]; exact (pentRep_sq_eq (fun i => (v i : f.SplittingField)) 0).symm⟩
  · exact ⟨pentRep 1, by rw [h]; exact (pentRep_sq_eq (fun i => (v i : f.SplittingField)) 1).symm⟩
  · exact ⟨pentRep 2, by rw [h]; exact (pentRep_sq_eq (fun i => (v i : f.SplittingField)) 2).symm⟩
  · exact ⟨pentRep 3, by rw [h]; exact (pentRep_sq_eq (fun i => (v i : f.SplittingField)) 3).symm⟩
  · exact ⟨pentRep 4, by rw [h]; exact (pentRep_sq_eq (fun i => (v i : f.SplittingField)) 4).symm⟩
  · exact ⟨pentRep 5, by rw [h]; exact (pentRep_sq_eq (fun i => (v i : f.SplittingField)) 5).symm⟩


omit [CharZero K] in
/-- `F₂₀` (the affine-linear permutations) is closed under inverses. -/
lemma IsAffineLinearMod5.inv {g : Equiv.Perm (Fin 5)} (hg : IsAffineLinearMod5 g) :
    IsAffineLinearMod5 g⁻¹ := by
  revert hg; revert g; native_decide

omit [CharZero K] in
/-- `F₂₀` (the affine-linear permutations) is closed under multiplication. -/
lemma IsAffineLinearMod5.mul {g h : Equiv.Perm (Fin 5)}
    (hg : IsAffineLinearMod5 g) (hh : IsAffineLinearMod5 h) :
    IsAffineLinearMod5 (g * h) := by
  revert hg hh; revert g h; native_decide

/-!
### Separability of the sextic resolvent via an explicit Bézout certificate -/

omit [CharZero K] in
/-- The derivative of the sextic resolvent (explicit form). -/
lemma sexticResolventLocal_derivative (p q : K) :
    Polynomial.derivative (sexticResolventLocal p q) =
      Polynomial.C (6:K) * Polynomial.X ^ 5 - Polynomial.C (50 * p) * Polynomial.X ^ 4
        + Polynomial.C (220 * p ^ 2) * Polynomial.X ^ 3
        - Polynomial.C (420 * p ^ 3) * Polynomial.X ^ 2
        + Polynomial.C (350 * p ^ 4) * Polynomial.X
        - Polynomial.C (106 * p ^ 5 + 3125 * q ^ 4) := by
  rw [sexticResolventLocal]
  simp only [derivative_sub, derivative_add, derivative_X_pow, derivative_mul, derivative_C,
    derivative_X, zero_mul, add_zero, zero_add, Nat.cast_ofNat, mul_one]
  simp only [map_ofNat, map_mul, map_add, map_pow]
  ring

set_option maxHeartbeats 1000000 in
omit [CharZero K] in
/-- **Bézout certificate** for `R₆` and its derivative:
    `A·R₆ + B·R₆' = 5⁶ q⁴ (256 p⁵ + 3125 q⁴)`.  Verified by `ring` after expanding
    the `C`-coefficients. -/
lemma sexticResolventLocal_bezout (p q : K) :
    (Polynomial.C (-36:K) * Polynomial.X ^ 4 + Polynomial.C (312 * p) * Polynomial.X ^ 3
        - Polynomial.C (1456 * p ^ 2) * Polynomial.X ^ 2
        + Polynomial.C (3080 * p ^ 3) * Polynomial.X - Polynomial.C (3180 * p ^ 4))
        * sexticResolventLocal p q
      + (Polynomial.C (6:K) * Polynomial.X ^ 5 - Polynomial.C (62 * p) * Polynomial.X ^ 4
        + Polynomial.C (356 * p ^ 2) * Polynomial.X ^ 3 - Polynomial.C (980 * p ^ 3) * Polynomial.X ^ 2
        + Polynomial.C (1430 * p ^ 4) * Polynomial.X - Polynomial.C (750 * p ^ 5 + 15625 * q ^ 4))
        * Polynomial.derivative (sexticResolventLocal p q)
      = Polynomial.C (5 ^ 6 * q ^ 4 * (256 * p ^ 5 + 3125 * q ^ 4)) := by
  rw [sexticResolventLocal]
  simp only [derivative_sub, derivative_add, derivative_X_pow, derivative_mul, derivative_C,
    derivative_X, zero_mul, add_zero, zero_add, Nat.cast_ofNat, mul_one]
  simp only [map_ofNat, map_mul, map_add, map_pow, map_neg]
  ring

/-- The sextic resolvent is separable provided `q ≠ 0` and the quintic discriminant
    `256 p⁵ + 3125 q⁴` is nonzero. -/
lemma sexticResolventLocal_separable (p q : K) (hq : q ≠ 0)
    (hdisc : (256:K) * p ^ 5 + 3125 * q ^ 4 ≠ 0) :
    (sexticResolventLocal p q).Separable := by
  have hc : (5:K) ^ 6 * q ^ 4 * (256 * p ^ 5 + 3125 * q ^ 4) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hq)) hdisc
  refine ⟨Polynomial.C (((5:K) ^ 6 * q ^ 4 * (256 * p ^ 5 + 3125 * q ^ 4))⁻¹) *
      (Polynomial.C (-36:K) * Polynomial.X ^ 4 + Polynomial.C (312 * p) * Polynomial.X ^ 3
        - Polynomial.C (1456 * p ^ 2) * Polynomial.X ^ 2
        + Polynomial.C (3080 * p ^ 3) * Polynomial.X - Polynomial.C (3180 * p ^ 4)),
      Polynomial.C (((5:K) ^ 6 * q ^ 4 * (256 * p ^ 5 + 3125 * q ^ 4))⁻¹) *
      (Polynomial.C (6:K) * Polynomial.X ^ 5 - Polynomial.C (62 * p) * Polynomial.X ^ 4
        + Polynomial.C (356 * p ^ 2) * Polynomial.X ^ 3 - Polynomial.C (980 * p ^ 3) * Polynomial.X ^ 2
        + Polynomial.C (1430 * p ^ 4) * Polynomial.X - Polynomial.C (750 * p ^ 5 + 15625 * q ^ 4)), ?_⟩
  have hb := sexticResolventLocal_bezout p q
  have h1 : Polynomial.C (((5:K) ^ 6 * q ^ 4 * (256 * p ^ 5 + 3125 * q ^ 4))⁻¹)
      * Polynomial.C ((5:K) ^ 6 * q ^ 4 * (256 * p ^ 5 + 3125 * q ^ 4)) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  rw [show (1:K[X]) = Polynomial.C (((5:K) ^ 6 * q ^ 4 * (256 * p ^ 5 + 3125 * q ^ 4))⁻¹)
      * Polynomial.C ((5:K) ^ 6 * q ^ 4 * (256 * p ^ 5 + 3125 * q ^ 4)) from h1.symm]
  linear_combination Polynomial.C (((5:K) ^ 6 * q ^ 4 * (256 * p ^ 5 + 3125 * q ^ 4))⁻¹) * hb

/-- An irreducible quintic `X⁵ + pX + q` has nonzero constant term `q`
    (otherwise `X ∣ f`). -/
lemma quintic_const_ne_zero (p q : K)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (hf_irr : Irreducible f) : q ≠ 0 := by
  intro hq0
  subst hq0
  rw [map_zero, add_zero] at hf
  have hfac : f = Polynomial.X * (Polynomial.X ^ 4 + Polynomial.C p) := by rw [hf]; ring
  rcases hf_irr.isUnit_or_isUnit hfac with h | h
  · exact Polynomial.not_isUnit_X h
  · have hdeg : (Polynomial.X ^ 4 + Polynomial.C p).natDegree = 4 := by compute_degree!
    have hz := Polynomial.natDegree_eq_zero_of_isUnit h
    rw [hdeg] at hz; norm_num at hz

/-- The discriminant `256 p⁵ + 3125 q⁴` of an irreducible quintic `X⁵ + pX + q`
    is nonzero (irreducible ⇒ separable in characteristic zero). -/
lemma quintic_disc_ne_zero (p q : K)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (hf_irr : Irreducible f) :
    (256:K) * p ^ 5 + 3125 * q ^ 4 ≠ 0 := by
  have hq : q ≠ 0 := quintic_const_ne_zero p q f hf hf_irr
  intro hdisc0
  have hsep := hf_irr.separable
  rw [hf] at hsep
  by_cases hp : p = 0
  · subst hp
    have h3125 : (3125:K) * q ^ 4 = 0 := by linear_combination hdisc0
    have hq4 : q ^ 4 = 0 := (mul_eq_zero.mp h3125).resolve_left (by norm_num)
    exact hq (pow_eq_zero_iff (by norm_num) |>.mp hq4)
  · have hfr : (Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q).eval
        (-5 * q / (4 * p)) = 0 := by
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
      field_simp
      linear_combination (-q) * hdisc0
    have hfr' : (Polynomial.derivative
        (Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)).eval
        (-5 * q / (4 * p)) = 0 := by
      have h4 : ((4:K) * p) ^ 4 ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) hp)
      have key : ((4:K) * p) ^ 4 * (Polynomial.derivative
          (Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)).eval
          (-5 * q / (4 * p)) = 256 * p ^ 5 + 3125 * q ^ 4 := by
        simp only [derivative_add, derivative_mul, derivative_X_pow, derivative_X, derivative_C,
          eval_add, eval_mul, eval_pow, eval_X, eval_C, mul_one, Nat.cast_ofNat, zero_mul,
          add_zero, zero_add]
        field_simp
        have hpc : p ^ 4 * (p⁻¹) ^ 4 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hp, one_pow]
        linear_combination 3125 * q ^ 4 * hpc
      rw [hdisc0] at key
      exact (mul_eq_zero.mp key).resolve_left h4
    obtain ⟨a, b, hab⟩ := hsep
    have heval := congrArg (eval (-5 * q / (4 * p))) hab
    simp only [eval_add, eval_mul, eval_one, hfr, hfr', mul_zero, add_zero] at heval
    exact one_ne_zero heval.symm

/-- The map of the sextic resolvent to the splitting field factors as the product
    `∏_j (X - pentSqVal w j)` over the six `F₂₀`-cosets. -/
lemma sexticResolventLocal_map_eq_prod
    (p q : K)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (v : Fin 5 ≃ f.rootSet f.SplittingField) :
    (sexticResolventLocal p q).map (algebraMap K f.SplittingField)
      = ∏ j : Fin 6, (Polynomial.X
          - Polynomial.C (pentSqVal (fun i => (v i : f.SplittingField)) j)) := by
  apply Polynomial.funext
  intro r
  rw [eval_prod, ← eval₂_eq_eval_map, eval₂_sexticResolventLocal_eq]
  obtain ⟨he1, he2, he3, he4, he5⟩ :=
    vieta_pentagon p q f hf v
  obtain ⟨E1, E2, E3, E4, E5, E6⟩ :=
    pentSqVal_esymm_pure (fun i => (v i : f.SplittingField))
      (algebraMap K f.SplittingField p) (algebraMap K f.SplittingField q) he1 he2 he3 he4 he5
  rw [resolvent_eq_prod _ _ _ _ _ _ _ _ E1 E2 E3 E4 E5 E6, Fin.prod_univ_six]
  simp only [eval_sub, eval_X, eval_C]

/-- **Distinctness of the six pentagonal-sum-squares.**
    For an irreducible quintic `f = X⁵ + pX + q`, the six values `pentSqVal w j`
    (`w` the roots, `j` ranging over the six `F₂₀`-cosets) are pairwise distinct.

    Mathematically this is the separability of the sextic resolvent `R₆`: its
    discriminant equals `5²⁰ · q¹² · (disc f)³`, which is nonzero because for an
    irreducible quintic `q ≠ 0` (else `X ∣ f`) and `disc f ≠ 0` (irreducible ⇒
    separable in characteristic zero).

    The proof is by an explicit Bézout certificate for `R₆` and its derivative
    (`sexticResolventLocal_separable`), so no heavy discriminant computation is needed.
    The hypothesis `p ≠ 0` turns out to be unnecessary. -/
lemma pentSqVal_injective
    (p q : K)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (hf_irr : Irreducible f)
    (v : Fin 5 ≃ f.rootSet f.SplittingField) (j k : Fin 6)
    (h : pentSqVal (fun i => (v i : f.SplittingField)) j
        = pentSqVal (fun i => (v i : f.SplittingField)) k) :
    j = k := by
  set w : Fin 5 → f.SplittingField := fun i => (v i : f.SplittingField) with hw
  have hq : q ≠ 0 := quintic_const_ne_zero p q f hf hf_irr
  have hdisc : (256:K) * p ^ 5 + 3125 * q ^ 4 ≠ 0 := quintic_disc_ne_zero p q f hf hf_irr
  have hsep : (sexticResolventLocal p q).Separable := sexticResolventLocal_separable p q hq hdisc
  have hsepL : ((sexticResolventLocal p q).map (algebraMap K f.SplittingField)).Separable :=
    hsep.map
  rw [sexticResolventLocal_map_eq_prod p q f hf v] at hsepL
  have hsf : Squarefree (∏ i : Fin 6, (Polynomial.X - Polynomial.C (pentSqVal w i))) :=
    hsepL.squarefree
  by_contra hjk
  have hdvd : (Polynomial.X - Polynomial.C (pentSqVal w j))
        * (Polynomial.X - Polynomial.C (pentSqVal w j))
      ∣ ∏ i : Fin 6, (Polynomial.X - Polynomial.C (pentSqVal w i)) := by
    have hsub : ({j, k} : Finset (Fin 6)) ⊆ Finset.univ := Finset.subset_univ _
    have hp := Finset.prod_dvd_prod_of_subset ({j, k} : Finset (Fin 6)) Finset.univ
      (fun i => Polynomial.X - Polynomial.C (pentSqVal w i)) hsub
    rwa [Finset.prod_pair hjk, ← h] at hp
  have hunit := hsf _ hdvd
  exact (Polynomial.not_isUnit_X_sub_C (pentSqVal w j)) hunit

/-- Two pentagonal sums squared coincide iff the permutations differ by an
    element of F₂₀ (for an irreducible quintic). -/
lemma pentagonalSum_sq_eq_iff_F20_coset
    (p q : K)
    (f : K[X]) (hf : f = Polynomial.X ^ 5 + Polynomial.C p * Polynomial.X + Polynomial.C q)
    (hf_irr : Irreducible f)
    (v : Fin 5 ≃ f.rootSet f.SplittingField)
    (σ₁ σ₂ : Equiv.Perm (Fin 5)) :
    pentagonalSum (fun i => (v (σ₁ i) : f.SplittingField)) ^ 2 =
    pentagonalSum (fun i => (v (σ₂ i) : f.SplittingField)) ^ 2 ↔
    IsAffineLinearMod5 (σ₁⁻¹ * σ₂) := by
  constructor
  · intro h
    obtain ⟨j1, hj1⟩ := pentRep_cover σ₁
    obtain ⟨j2, hj2⟩ := pentRep_cover σ₂
    have e1 : pentagonalSum (fun i => (v (σ₁ i) : f.SplittingField)) ^ 2
        = pentSqVal (fun i => (v i : f.SplittingField)) j1 := by
      rw [← pentRep_sq_eq (fun i => (v i : f.SplittingField)) j1]
      exact (pentagonalSum_sq_eq_of_F20_coset (fun i => (v i : f.SplittingField))
        (roots_e2_zero p q f hf v) (pentRep j1) σ₁ hj1).symm
    have e2 : pentagonalSum (fun i => (v (σ₂ i) : f.SplittingField)) ^ 2
        = pentSqVal (fun i => (v i : f.SplittingField)) j2 := by
      rw [← pentRep_sq_eq (fun i => (v i : f.SplittingField)) j2]
      exact (pentagonalSum_sq_eq_of_F20_coset (fun i => (v i : f.SplittingField))
        (roots_e2_zero p q f hf v) (pentRep j2) σ₂ hj2).symm
    have hjj : j1 = j2 :=
      pentSqVal_injective p q f hf hf_irr v j1 j2 (by rw [← e1, ← e2]; exact h)
    subst hjj
    have hrw : σ₁⁻¹ * σ₂ = ((pentRep j1)⁻¹ * σ₁)⁻¹ * ((pentRep j1)⁻¹ * σ₂) := by group
    rw [hrw]
    exact (hj1.inv).mul hj2
  · exact fun h => pentagonalSum_sq_eq_of_F20_coset (fun i => (v i : f.SplittingField))
      (roots_e2_zero p q f hf v) σ₁ σ₂ h

end

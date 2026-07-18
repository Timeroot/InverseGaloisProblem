/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Polynomial.DedekindFacts
import InverseGalois.Polynomial.QuinticDiscriminant
import InverseGalois.Resolvent.QuinticGroupTheory

/-!
# Helper lemmas for the A₅ inverse Galois proof
-/

open Polynomial UniqueFactorizationMonoid

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 1000

/-!
## Mod-7 factorization infrastructure
-/

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- A nonzero polynomial of degree ≤ n over a domain with > n elements has at most n roots. -/
private lemma poly_zero_of_too_many_roots {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    {f : R[X]} (hf : f ≠ 0) (n : ℕ) (hn : f.natDegree ≤ n)
    (S : Finset R) (hS : n < S.card)
    (hroots : ∀ x ∈ S, f.IsRoot x) : False := by
  have h1 : S.card ≤ f.roots.toFinset.card :=
    Finset.card_le_card fun x hx =>
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf).mpr (hroots x hx))
  have h2 : f.roots.toFinset.card ≤ f.roots.card := f.roots.toFinset_card_le
  have h3 : f.roots.card ≤ f.natDegree := Polynomial.card_roots' f
  omega

/-- The cubic X³ + 2X² + 5X + 5 has no roots in ZMod 7. -/
theorem cubic_mod7_no_roots :
    ∀ x : ZMod 7,
      (x ^ 3 + 2 * x ^ 2 + 5 * x + 5 : ZMod 7) ≠ 0 := by decide

/-
The cubic X³ + 2X² + 5X + 5 is irreducible over ZMod 7.
-/
theorem cubic_mod7_irreducible :
    Irreducible (X ^ 3 + C 2 * X ^ 2 + C 5 * X + C 5 : (ZMod 7)[X]) := by
      -- Since the polynomial has no roots in ZMod 7, it is irreducible over ZMod 7.
      have h_irred : ∀ p q : Polynomial (ZMod 7), p.degree > 0 → q.degree > 0 → (p * q = Polynomial.X ^ 3 + Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 5 * Polynomial.X + Polynomial.C 5) → False := by
        intros p q hp hq h_eq
        have h_deg : p.degree + q.degree = 3 := by
          haveI := Fact.mk ( by decide : Nat.Prime 7 ) ; rw [ ← Polynomial.degree_mul, h_eq, Polynomial.degree_add_C ] <;> erw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> erw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> simp +decide ;
        -- Since the degrees of $p$ and $q$ add up to 3 and both are positive, one of them must have degree 1.
        have h_deg_one : p.degree = 1 ∨ q.degree = 1 := by
          erw [ Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hp ), Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hq ) ] at * ; norm_cast at * ; omega;
        obtain h | h := h_deg_one <;> obtain ⟨ x, hx ⟩ := Polynomial.exists_root_of_degree_eq_one h <;> replace h_eq := congr_arg ( Polynomial.eval x ) h_eq <;> simp_all +decide; all_goals fin_cases x <;> contradiction;
      constructor;
      · haveI := Fact.mk ( by decide : Nat.Prime 7 ) ; exact fun h => absurd ( Polynomial.degree_eq_zero_of_isUnit h ) ( by erw [ Polynomial.degree_add_C ] <;> repeat ( first | erw [ Polynomial.degree_add_eq_left_of_degree_lt ] | simp +decide ) ) ;
      · contrapose! h_irred;
        obtain ⟨ a, b, h₁, h₂, h₃ ⟩ := h_irred; use a, b; simp_all +decide [ Polynomial.isUnit_iff_degree_eq_zero ] ;
        exact ⟨ lt_of_le_of_ne ( le_of_not_gt fun h => by apply_fun Polynomial.eval 0 at h₁; simp_all +decide ) ( Ne.symm h₂ ), lt_of_le_of_ne ( le_of_not_gt fun h => by apply_fun Polynomial.eval 0 at h₁; simp_all +decide ) ( Ne.symm h₃ ) ⟩

/-
The mod-7 reduction of X⁵+20X+16 is squarefree.
-/
theorem f_a5_mod7_squarefree :
    Squarefree (Polynomial.map (Int.castRingHom (ZMod 7))
      (X ^ 5 + C 20 * X + C 16 : ℤ[X])) := by
        have h_gcd : IsCoprime (Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16 : Polynomial (ZMod 7)) (Polynomial.derivative (Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16 : Polynomial (ZMod 7))) := by
          norm_num [ Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow ];
          -- We can use the fact that if the polynomial $X^5 + 6X + 2$ has no common roots with its derivative $5X^4 + 6$, then it is coprime with its derivative.
          have h_coprime : ∀ x : AlgebraicClosure (ZMod 7), Polynomial.eval x (Polynomial.map (algebraMap (ZMod 7) (AlgebraicClosure (ZMod 7))) (Polynomial.X ^ 5 + Polynomial.C 6 * Polynomial.X + Polynomial.C 2)) ≠ 0 ∨ Polynomial.eval x (Polynomial.map (algebraMap (ZMod 7) (AlgebraicClosure (ZMod 7))) (Polynomial.C 5 * Polynomial.X ^ 4 + Polynomial.C 6)) ≠ 0 := by
            intro x
            by_contra h_contra
            push_neg at h_contra
            have h_root : x^5 + 6 * x + 2 = 0 ∧ 5 * x^4 + 6 = 0 := by
              aesop;
            grind;
          apply isCoprime_of_dvd;
          · exact not_and_of_not_left _ <| by exact ne_of_apply_ne ( Polynomial.eval 0 ) <| by simp +decide ;
          · intro z hz hz' hz'' hz'''; contrapose! h_coprime; simp_all +decide;
            obtain ⟨ x, hx ⟩ := ( @IsAlgClosed.exists_root ( AlgebraicClosure ( ZMod 7 ) ) _ _ ( Polynomial.map ( algebraMap ( ZMod 7 ) ( AlgebraicClosure ( ZMod 7 ) ) ) z ) ( by
              rw [ Polynomial.degree_map ] ; intro H; simp_all +decide [ Polynomial.isUnit_iff_degree_eq_zero ] ; ) );
            obtain ⟨ y, hy ⟩ := hz''; obtain ⟨ z, hz ⟩ := hz'''; replace hy := congr_arg ( Polynomial.map ( algebraMap ( ZMod 7 ) ( AlgebraicClosure ( ZMod 7 ) ) ) ) hy; replace hz := congr_arg ( Polynomial.map ( algebraMap ( ZMod 7 ) ( AlgebraicClosure ( ZMod 7 ) ) ) ) hz; replace hy := congr_arg ( Polynomial.eval x ) hy; replace hz := congr_arg ( Polynomial.eval x ) hz; aesop;
        obtain ⟨ a, b, h ⟩ := h_gcd;
        refine' fun x hx => _;
        -- Since $x^2$ divides the polynomial, it follows that $x$ divides the polynomial and its derivative.
        have h_div : x ∣ (Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16 : Polynomial (ZMod 7)) ∧ x ∣ Polynomial.derivative (Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16 : Polynomial (ZMod 7)) := by
          have h_div : x ^ 2 ∣ (Polynomial.X ^ 5 + Polynomial.C 20 * Polynomial.X + Polynomial.C 16 : Polynomial (ZMod 7)) := by
            convert hx using 1 ; ring;
            norm_num [ Polynomial.ext_iff ];
            intro n; erw [ Polynomial.coeff_C ] ;
          obtain ⟨ y, hy ⟩ := h_div; simp_all +decide [ sq, mul_assoc ] ;
          exact ⟨ derivative x * y + derivative x * y + x * derivative y, by ring ⟩;
        exact isUnit_of_dvd_one ( h ▸ dvd_add ( dvd_mul_of_dvd_right h_div.1 _ ) ( dvd_mul_of_dvd_right h_div.2 _ ) )

/-
The factorizationType of the mod-7 reduction contains 3.
-/
theorem f_a5_mod7_factorizationType :
    3 ∈ factorizationType (Polynomial.map (Int.castRingHom (ZMod 7))
      (X ^ 5 + C 20 * X + C 16 : ℤ[X])) := by
        unfold factorizationType;
        erw [ show ( Polynomial.map ( Int.castRingHom ( ZMod 7 ) ) ( X ^ 5 + C 20 * X + C 16 ) : ( ZMod 7 )[X] ) = ( X + 3 ) * ( X + 2 ) * ( X ^ 3 + 2 * X ^ 2 + 5 * X + 5 ) by
                ext; norm_num; ring_nf
                rename_i n; rcases n with ( _ | _ | _ | _ | _ | _ | n ) <;> simp +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ; ];
        erw [ normalizedFactors_mul, normalizedFactors_mul ];
        · erw [ normalizedFactors_irreducible, normalizedFactors_irreducible, normalizedFactors_irreducible ] <;> norm_num;
          · erw [ Polynomial.natDegree_mul' ] <;> norm_num [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ];
            · erw [ Polynomial.natDegree_mul' ] <;> norm_num [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ];
              · erw [ Polynomial.natDegree_mul' ] <;> norm_num [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ];
                · erw [ Polynomial.natDegree_add_C ] ; erw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> erw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num;
                  · erw [ Polynomial.natDegree_C_mul_X_pow ] <;> norm_num;
                    decide +revert;
                  · erw [ Polynomial.natDegree_C_mul_X ] <;> norm_num;
                    decide +revert;
                  · erw [ Polynomial.natDegree_C_mul_X_pow ] <;> norm_num;
                    decide +revert;
                · exact ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide );
              · exact Polynomial.X_add_C_ne_zero _;
            · exact Polynomial.X_add_C_ne_zero _;
          · convert cubic_mod7_irreducible using 1;
          · exact Polynomial.irreducible_of_degree_eq_one ( by erw [ Polynomial.degree_add_C ] <;> norm_num );
          · haveI := Fact.mk ( by decide : Nat.Prime 7 ) ; exact Polynomial.irreducible_of_degree_eq_one ( Polynomial.degree_X_add_C _ ) ;
        · exact Polynomial.X_add_C_ne_zero _;
        · exact Polynomial.X_add_C_ne_zero _;
        · exact ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide );
        · exact ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide )

/-!
## Galois group of X⁵+20X+16 has order dividing 60

This section proves that |Gal| divides 60 by showing:
1. |Gal| divides 120 (embedding into S₅)
2. 5 | |Gal| (from irreducibility)
3. S₅ has no subgroup of order 40
4. |Gal| ≠ 120 (from discriminant being a perfect square)
-/

/-- The Galois group of X⁵+20X+16 does not have order 120
(i.e., Gal ≠ S₅). This follows from the discriminant being a
perfect square: disc = 32000². -/
theorem card_gal_a5_ne_120 :
    Nat.card (X ^ 5 + C 20 * X + C 16 : ℚ[X]).Gal ≠ 120 :=
  card_gal_f_poly_ne_120

end

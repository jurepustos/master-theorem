import Mathlib

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv


lemma bounded_above_of_asymp_le {f g : ℕ → ℕ}
    (h : AsympLE f g) (N : ℕ) (hg : ∀ n > N, g n > 0) : 
    ∃ C > 0, ∀ n > N, f n ≤ C * g n := by
  rcases h with ⟨N', hbound⟩
  rcases func_le_mul_func_of_lt N' with ⟨C, C_pos, hle⟩
  use C
  apply And.intro C_pos
  intro n n_gt
  if hn : N' ≤ n then {
    apply le_trans (hbound n hn)
    specialize hg n n_gt
    apply le_mul_of_one_le_left <;> linarith
  }
  else {
    simp at hn
    exact hle n n_gt hn
  }
where
  func_le_mul_func_of_lt (N' : ℕ) : ∃ C > 0, ∀ n > N, n < N' → f n ≤ C * g n := by
    induction' N' with m hm
    . use 1
      apply And.intro one_pos
      intro n n_pos n_lt
      contrapose n_lt
      exact Nat.not_lt_zero n
    . rcases hm with ⟨C, C_pos, f_le⟩
      use C + f m
      apply And.intro (add_pos_of_pos_of_nonneg C_pos (Nat.zero_le (f m)))
      intro n n_gt n_lt_succ
      rw [add_mul]
      if hn_m : n < m then {
        apply le_add_of_le_of_nonneg (f_le n n_gt hn_m)
        apply mul_nonneg <;> apply Nat.zero_le
      }
      else {
        simp at hn_m
        have n_eq_m : n = m := eq_of_le_of_le (Nat.le_of_lt_add_one n_lt_succ) hn_m
        apply le_add_of_nonneg_of_le (mul_nonneg (le_of_lt C_pos) (zero_le (g n)))
        rw [← mul_one (f n), ← n_eq_m]
        exact Nat.mul_le_mul_left (f n) (hg n n_gt)
      }


/- We formalize the proof at https://www.cs.dartmouth.edu/~deepc/Courses/S20/lecs/lec3supp.pdf -/

/- Divide and conquer recurrence -/
structure MasterRecurrence (T : ℕ → ℕ) (a b n₀ : ℕ) (f : ℕ → ℕ) where
  /- n₀ has to be strictly positive -/
  one_lt_n₀ : 1 < n₀
  /-a is positive -/
  a_pos : a > 0
  /- a is positive -/
  one_lt_b : 1 < b
  /- T is monotone -/
  T_monotone : Monotone T
  /- The recurrence formula -/
  T_rec : ∀ n ≥ n₀, T n ≤ a * T (n ⌈/⌉ b) + f n


namespace MasterRecurrence


private lemma formula_subst_once {T : ℕ → ℕ} {a b k : ℕ} {d C : ℝ} (n : ℕ) 
    (ha : a > 0) (hrec : T (n / b^k) ≤ a * T (n / b^(k+1)) + 
      C * (n / Nat.cast (R := ℝ) b^k)^d)
    (hformula : T n ≤ a^k * T (n / b^k) + C * GeometricSum (K := ℝ)
      (a / (b^d)) (k-1) * Nat.cast (R := ℝ) n^d) :
    T n ≤ a^(k+1) * T (n / b^(k+1)) + C * GeometricSum (K := ℝ) 
      (a / (b^d)) k * Nat.cast (R := ℝ) n^d := by
  if hk : k = 0 then {
    rw [hk, GeometricSum.def_zero]
    simp
    rw [hk] at hrec
    simp at hrec
    exact hrec
  }
  else {
    rw [pow_succ, mul_assoc, ← Nat.sub_one_add_one hk, ← GeometricSum.def_succ,
        Nat.sub_one_add_one hk, mul_add, add_mul, ← add_assoc]

    apply le_add_of_le_add_right hformula
    have pow_k_eq : (Nat.cast (R := ℝ) a / ↑b ^ d) ^ k = 
        (Nat.cast (R := ℝ) a ^ k / (b^k)^d) := by {
      rw [div_pow, ← Real.rpow_natCast (Nat.cast (R := ℝ) b^d), ← Real.rpow_mul,
          mul_comm d, Real.rpow_mul, Real.rpow_natCast]
      all_goals apply Nat.cast_nonneg
    }
    rw [pow_k_eq, mul_assoc, div_mul_comm, ← mul_assoc C, mul_right_comm C, 
        mul_comm C, mul_assoc _ C, ← mul_add, ← Real.div_rpow, mul_le_mul_left]
    exact hrec

    all_goals norm_cast
    . apply pow_pos
      exact ha
    . apply zero_le
    . apply pow_nonneg
      apply zero_le
  }

private theorem formula_subst {T : ℕ → ℕ} {a b n₀ : ℕ} {d C : ℝ} (k n : ℕ) (ha : a > 0)
    (hb : b > 1) (hn : n ≥ n₀ * b^k) (hC : C > 0) (hd : d ≥ 1)
    (hrec : ∀ m : ℕ, m ≥ n₀ → T m ≤ a * T (m / b) + C * (Nat.cast (R := ℝ) m)^d) :
    T n ≤ a^k * T (n / b^k) + C * GeometricSum (K := ℝ) (a / b^d) (k-1) * Nat.cast (R := ℝ) n^d := by
  induction' k with x hx
  . rw [pow_zero, Nat.zero_sub, pow_zero, Nat.div_one, 
        GeometricSum.def_zero, one_mul]
    rw [pow_zero, mul_one] at hn
    apply le_add_of_le_of_nonneg (le_refl _)
    rw [mul_one]
    apply mul_nonneg
    . linarith
    . apply Real.rpow_nonneg
      apply Nat.cast_nonneg
  . have n₀_mul_b_pow_x_le_n : n₀ * b^x ≤ n := by {
      rw [pow_succ, ← mul_assoc] at hn
      exact le_of_mul_le_of_one_le_left hn (le_of_lt hb)
    }
    have n₀_le_x_div_b_pow_x : n₀ ≤ n / b^x := by {
      apply (Nat.le_div_iff_mul_le (pow_pos (le_of_lt hb) x)).2 
      exact n₀_mul_b_pow_x_le_n
    }

    rw [Nat.add_one_sub_one]
    specialize hx n₀_mul_b_pow_x_le_n
    apply flip (formula_subst_once n ha) hx
    specialize hrec (n / b^x) n₀_le_x_div_b_pow_x
    rw [Nat.div_div_eq_div_mul, ← pow_succ] at hrec
    apply le_trans hrec
    have bound_cast_le : C * ↑(n / b ^ x) ^ d ≤ 
        C * (Nat.cast (R := ℝ) n / ↑b ^ x) ^ d := by {
      rw [mul_le_mul_left hC, ← Nat.cast_pow]
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le
      exact le_trans (le_of_lt one_pos) hd
    }
    exact le_add_of_le_add_left (le_refl _) bound_cast_le


variable {T f : ℕ → ℕ} {a b n₀ : ℕ} {d : ℝ}

lemma n₀_pos (self: MasterRecurrence T a b n₀ f) : n₀ > 0 := lt_trans one_pos self.one_lt_n₀ 

lemma b_pos (self: MasterRecurrence T a b n₀ f) : b > 0 := lt_trans one_pos self.one_lt_b 

private lemma add_poly (hd : d ≥ 1) (hb : b > 1) {n : ℕ} (hn : n > 1) : 
    Nat.cast (R := NNReal) (n + b)^d ≤ (2 : NNReal)^(d-1) * b^d * n^d := by
  have one_lt_n_add_b : 1 < (Nat.cast (R := ℝ) n + ↑b) := by {
    rw [← Nat.cast_add, ← Nat.cast_one, Nat.cast_lt]
    exact Nat.lt_add_right b hn
  }

  rw [Nat.cast_add]
  apply le_trans (NNReal.rpow_add_le_mul_rpow_add_rpow n b hd)

  have n_pos : n > 0 := lt_trans one_pos hn
  have one_le_cast {k : ℕ} (hk_pos : k > 0) : 1 ≤ Nat.cast (R := NNReal) k := by {
    rw [← Nat.cast_one, Nat.cast_le]
    exact hk_pos
  }
  rw [add_comm, mul_assoc, mul_le_mul_left (NNReal.rpow_pos two_pos)]
  apply add_le_mul
  . apply le_trans' (NNReal.rpow_le_rpow_of_exponent_le _ hd)
    . rw [NNReal.rpow_one, ← Nat.cast_two, Nat.cast_le]
      exact hb
    . rw [← Nat.cast_one, Nat.cast_le]
      exact le_of_lt hb
  . apply le_trans' (NNReal.rpow_le_rpow_of_exponent_le _ hd)
    . rw [NNReal.rpow_one, ← Nat.cast_two, Nat.cast_le]
      exact hn
    . rw [← Nat.cast_one, Nat.cast_le]
      exact le_of_lt hn

private lemma f_of_add_b_poly {C : ℕ} (hd : d ≥ 1) (hC : C > 0) (hb : b > 1)
    (hf_poly : ∀ n > 0, f n ≤ C * Nat.cast (R := ℝ) n^d) {n : ℕ} (hn : n > 1) : 
    f (n + b) ≤ C * (2 : ℝ)^(d-1) * b^d * Nat.cast (R := ℝ) n^d := by
  specialize hf_poly (n + b) (le_add_of_le_of_nonneg (le_of_lt hn) (zero_le b))
  apply le_trans hf_poly
  have poly_le : Nat.cast (R := ℝ) (n + b) ^ d ≤ (2 : ℝ)^(d - 1) * 
      ↑b ^ d * Nat.cast (R := ℝ) n^d := by {
    apply add_poly hd hb hn
  }
  apply le_trans ((mul_le_mul_left (Nat.cast_pos.2 hC)).2 poly_le)
  rw [← mul_assoc, ← mul_assoc, mul_le_mul_right]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.2 (lt_trans one_pos hn)) d


lemma self_subst (self : MasterRecurrence T a b n₀ f) (hd : d ≥ 1) 
    (hf_poly : f ∈ O ℕ fun n ↦ ⌈(Nat.cast (R := ℝ) n)^d⌉₊) : 
    ∃ C > 0, ∀ k > 0, MasterRecurrence 
      (fun n ↦ T (n + b)) (a^k) (b^k) (n₀ * b^k) 
      (fun n ↦ C * ⌈GeometricSum (K := ℝ) (a/b^d) (k - 1)⌉₊ * 
        ⌈Nat.cast (R := ℝ) n^d⌉₊) := by
  rw [O_iff_asymp_bounded_above, 
      ← exists_pos_smul_asymp_le_iff_asymp_bounded_above] at hf_poly
  rcases hf_poly with ⟨C₀, C₀_pos, f_poly'⟩
  have ceil_poly_pos : ∀ n > 0, 0 < C₀ * ⌈Nat.cast (R := ℝ) n ^ d⌉₊ := by {
    intro n n_pos
    apply mul_pos C₀_pos
    rw [Nat.ceil_pos]
    apply Real.rpow_pos_of_pos
    norm_cast
  }
  apply bounded_above_of_asymp_le at f_poly'
  specialize f_poly' 0 ceil_poly_pos
  rcases f_poly' with ⟨C₁, C₁_pos, f_poly⟩

  have const_pos : 0 < ↑C₁ * (2 : ℝ) * C₀ * 2^(d-1) * ↑b^d := by {
    apply mul_pos
    . apply mul_pos <;> norm_cast
      . apply mul_pos
        apply mul_pos
        all_goals linarith
      . apply Real.rpow_pos_of_pos
        linarith
    . apply Real.rpow_pos_of_pos
      norm_cast
      exact self.b_pos
  }

  have const_ceil_pos : 0 < ⌈↑C₁ * (2 : ℝ) * C₀ * 2^(d-1) * ↑b^d⌉₊ := by {
    rw [Nat.ceil_pos]
    exact const_pos
  }
  use ⌈↑C₁ * (2 : ℝ) * C₀ * 2^(d-1) * ↑b^d⌉₊
  apply And.intro const_ceil_pos

  intro k hk
  exact {
    one_lt_n₀ := one_lt_mul_of_lt_of_le self.one_lt_n₀ (pow_pos self.b_pos k),
    a_pos := pow_pos self.a_pos k,
    one_lt_b := one_lt_pow₀ self.one_lt_b (zero_lt_iff.1 hk),
    T_monotone := by {
      intro x y x_le_y
      exact self.T_monotone (add_le_add x_le_y (le_refl b))
    }
    T_rec := by {
      intro n hn

      suffices add_b : T (n + b) ≤ a ^ k * T (n / b ^ k + b) + 
          ((C₁ * 2 * C₀ * 2^(d-1) * b^d) * GeometricSum (K := ℝ) (↑a/↑b^d) 
          (k-1)) * Nat.cast (R := ℝ) n^d by {
        rw [← Nat.cast_le (α := ℝ)]
        push_cast
        apply le_trans add_b (add_le_add _ _)
        . rw [mul_le_mul_left, Nat.cast_le, ← Nat.floorDiv_eq_div]
          apply self.T_monotone
          apply add_le_add_right floorDiv_le_ceilDiv
          norm_cast
          exact pow_pos self.a_pos k
        . apply mul_le_mul
          . apply mul_le_mul
            . apply Nat.le_ceil
            . apply Nat.le_ceil
            . apply le_of_lt
              apply GeometricSum.pos_of_pos
              apply div_pos
              . norm_cast
                exact self.a_pos
              . apply Real.rpow_pos_of_pos
                norm_cast
                exact self.b_pos
            . apply Nat.cast_nonneg
          . apply Nat.le_ceil
          . apply Real.rpow_nonneg
            norm_cast
            linarith
          . apply mul_nonneg 
            all_goals apply Nat.cast_nonneg
      }

      generalize S_def : (fun n ↦ T (n + b)) = S
      have S_apply : ∀ (n : ℕ), T (n + b) = S n := by {
        intro n
        rw [← S_def]
      }
      have n_pos : n > 0 := le_trans (mul_pos self.n₀_pos (pow_pos self.b_pos k)) hn

      have rec_apply : ∀ m ≥ n₀, S m ≤ a * S (m / b) + 
          C₁ * 2 * C₀ * (2 : ℝ)^(d-1) * b^d * Nat.cast (R := ℝ) m^d := by {
        intro m n₀_le_m 
        have m_gt_one : m > 1 := lt_of_lt_of_le self.one_lt_n₀ n₀_le_m
        have ceilDiv_apply := self.T_rec (m + b) (le_add_right n₀_le_m) 
        have ceilDiv_le : a * T ((m + b) ⌈/⌉ b) ≤ a * T ((m + b) / b + 1) := by {
          apply Nat.mul_le_mul_left
          apply self.T_monotone
          exact Nat.ceilDiv_le_div_succ self.b_pos
        }

        apply flip le_add_of_le_add_right ceilDiv_le at ceilDiv_apply
        rw [Nat.add_div self.b_pos, Nat.div_self self.b_pos] at ceilDiv_apply
        split_ifs at ceilDiv_apply with hrec_mod <;> simp at hrec_mod
        . contrapose hrec_mod
          intro hmod
          have hcontra := Nat.mod_lt m self.b_pos
          exact not_le_of_lt hcontra hmod 
        . simp at ceilDiv_apply
          rw [add_assoc, one_add_one_eq_two] at ceilDiv_apply
          have rec_T_le_m_add_b : a * T (m / b + 2) ≤ a * T (m / b + b) := by {
            apply Nat.mul_le_mul_left
            apply self.T_monotone
            apply add_le_add_left self.one_lt_b
          }
          apply flip le_add_of_le_add_right rec_T_le_m_add_b at  ceilDiv_apply
          rw [S_apply, S_apply, ← Nat.cast_le (α := ℝ), Nat.cast_add,
              Nat.cast_mul] at ceilDiv_apply

          have f_poly : ∀ n' > 0, f n' ≤ ↑C₁ * 2 * C₀ * Nat.cast (R := ℝ) n'^d := by {
            intro n' n'_pos
            have one_le_n'_pow : 1 ≤ Nat.cast (R := ℝ) n' ^ d := by {
              apply Real.one_le_rpow <;> norm_cast; linarith
            }
            specialize f_poly n' n'_pos
            rw [← Nat.cast_le (α := ℝ), Nat.cast_mul] at f_poly
            rw [mul_assoc (Nat.cast (R := ℝ) C₁), mul_assoc]
            apply le_trans' ((mul_le_mul_left (by norm_cast)).2 _) f_poly
            simp
            rw [mul_comm 2, mul_assoc, mul_le_mul_left] <;> norm_cast
            apply Nat.ceil_le_two_mul
            linarith
          }
          
          have C_mul_two_pos : C₁ * 2 * C₀ > 0 := by {
            apply mul_pos <;> linarith
          }
          rw [← Nat.cast_two, ← Nat.cast_mul, ← Nat.cast_mul] at f_poly
          have f_le := f_of_add_b_poly hd C_mul_two_pos self.one_lt_b f_poly m_gt_one
          push_cast at f_le
          exact le_add_of_le_add_left ceilDiv_apply f_le
      }
      
      rw [S_apply, S_apply]
      exact formula_subst k n self.a_pos self.one_lt_b hn const_pos hd rec_apply
    }
  }


end MasterRecurrence


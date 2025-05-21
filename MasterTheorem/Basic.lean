import Mathlib
import Init.Data.Int.Order

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv
import MasterTheorem.MasterRecurrence

namespace MasterRecurrence


variable {T f : ℕ → ℕ} {a b n₀ : ℕ} {d : ℝ}

private lemma exists_le_of_O_poly {C : ℕ} (self : MasterRecurrence T a b n₀ f)
    (hC : C > 0) (hd : d ≥ 1) (hf_poly : ∀ m > 0, f m ≤ C * ⌈Nat.cast (R := ℝ) m^d⌉₊) : 
    ∃ k > 0, ∀ n ≥ n₀, b ≤ n / n₀ → T n ≤ T ((n₀ + 1) * b + 1) * 
    ⌈Nat.cast (R := ℝ) n ^ (Real.logb b a)⌉₊ + ⌈GeometricSum (K := ℝ) k (↑a / ↑b^d) 
    (⌈Real.logb b n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ := by
  use C * 2 * 2^(d-1) * ↑b^d
  apply And.intro (by {
    apply mul_pos
    . apply mul_pos
      . apply mul_pos <;> norm_cast
      . apply Real.rpow_pos_of_pos two_pos
    . apply Real.rpow_pos_of_pos
      norm_cast
      exact self.b_pos
  })

  intro n hn hb
  have n_pos : n > 0 := le_trans self.n₀_pos hn
  have one_le_cast_n_div_n₀ : 1 ≤ Nat.cast (R := ℝ) n / ↑n₀ := by {
    rw [one_le_div] <;> norm_cast
    linarith [self.one_lt_n₀]
  }

  generalize k_def : ⌊Real.logb b (n / n₀)⌋₊ = k
  have k_pos : 0 < k := by {
    rw [← k_def]
    rw [Nat.floor_pos, ← Real.logb_self_eq_one, Real.logb_le_logb]
    apply le_trans' Nat.cast_div_le
    all_goals norm_cast 
    all_goals linarith [self.one_lt_b]
  }

  have subst_master := self.self_subst k k_pos hd hC hf_poly
  have subst_rec := subst_master.T_rec n (by {
    rw [← k_def, ge_iff_le, ← Nat.cast_le (α := ℝ), Nat.cast_mul, mul_comm]
    apply mul_le_of_le_div₀ <;> norm_cast
    repeat apply zero_le
    push_cast
    rw [← Real.rpow_natCast]
    apply le_trans ((Real.rpow_le_rpow_left_iff _).2 (Nat.floor_le _))
    all_goals norm_cast
    . rw [Real.rpow_logb] <;> norm_cast
      all_goals linarith [self.one_lt_b]
    . linarith [self.one_lt_b]
    . apply Real.logb_nonneg
      . norm_cast
        linarith [self.one_lt_b]
      . rw [one_le_div] <;> norm_cast
        linarith [self.one_lt_n₀]
  })
  have T_of_add_b : T n ≤ T (n + b) := self.T_monotone (le_add_right (le_refl n))

  apply le_trans T_of_add_b
  apply le_trans subst_rec
  apply add_le_add
  . rw [mul_comm]
    apply mul_le_mul
    . apply self.T_monotone
      rw [← k_def, add_mul, one_mul, add_assoc, add_comm b, ← add_assoc]
      apply add_le_add_right
      apply le_trans (Nat.ceilDiv_le_div_succ (pow_pos self.b_pos _))
      apply add_le_add_right
      rw [← Nat.cast_le (α := ℝ), Real.logb_div]
      apply le_trans Nat.cast_div_le
      push_cast
      rw [← Real.rpow_logb (b := b) (x := n), ← Real.rpow_natCast, 
          ← Real.rpow_sub, Real.rpow_logb, ← Real.rpow_one b, 
          ← Real.rpow_logb (b := b) (x := n₀), ← Real.rpow_add, 
          Real.rpow_one b, Real.rpow_logb, Real.rpow_le_rpow_left_iff]
      have le_log_sub : Real.logb b n - Real.logb b n₀ -1 ≤ 
                        ⌊Real.logb b n - Real.logb b n₀⌋₊ := by {
        rw [sub_le_iff_le_add', add_comm]
        apply le_trans (Nat.le_ceil _)
        norm_cast
        apply Nat.ceil_le_floor_add_one
      }
      apply le_trans (sub_le_sub_left le_log_sub _)
      all_goals norm_cast
      all_goals linarith [self.one_lt_b, self.one_lt_n₀]
    . rw [← k_def, ← Nat.cast_le (α := ℝ), Nat.cast_pow, ← Real.rpow_natCast]
      apply le_trans' (Nat.le_ceil _)
      rw [← Real.rpow_logb (b := b) (x := Nat.cast (R := ℝ) n),
          ← Real.rpow_mul, mul_comm, Real.rpow_mul, Real.rpow_logb, 
          Real.rpow_logb]
      . apply Real.rpow_le_rpow_of_exponent_le <;> norm_cast
        . exact self.a_pos
        . apply le_trans (Nat.floor_le (Real.logb_nonneg _ _))
          rw [Real.logb_le_logb]
          apply div_le_self
          all_goals norm_cast
          all_goals linarith [self.one_lt_n₀, self.one_lt_b]
      all_goals norm_cast
      all_goals linarith [self.a_pos, self.one_lt_b]
    all_goals (apply Nat.zero_le)
  . rw [mul_le_mul_right]
    . apply Nat.ceil_le_ceil
      apply GeometricSum.le_of_pos_of_pos_of_le
      . apply mul_pos
        . apply mul_pos
          . exact mul_pos (Nat.cast_pos.2 hC) two_pos
          . exact Real.rpow_pos_of_pos two_pos (d-1)
        . exact Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
      . apply div_pos
        . exact Nat.cast_pos.2 self.a_pos
        . exact Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
      . simp
        rw [← k_def, Nat.sub_add_cancel]
        . apply le_trans (Nat.floor_le_floor (b := Real.logb b n) _)
          . apply Nat.floor_le_ceil
          . rw [Real.logb_le_logb] <;> norm_cast
            apply div_le_self <;> norm_cast
            all_goals linarith [self.one_lt_b, self.one_lt_n₀]
        . apply Nat.ceil_pos.2
          apply Real.logb_pos <;> norm_cast
          all_goals linarith [self.one_lt_b, self.one_lt_n₀]
    . apply Nat.ceil_pos.2
      apply Real.rpow_pos_of_pos
      assumption_mod_cast

private lemma poly_pos {d : ℝ} : ∀ n > 0, Nat.cast (R := ℝ) n^d > 0 := by
  intro n n_pos
  exact Real.rpow_pos_of_pos (Nat.cast_pos.2 n_pos) d

private lemma ceil_poly_pos {d : ℝ} : ∀ n > 0, 0 < ⌈Nat.cast (R := ℝ) n^d⌉₊ := by {
  intro n n_pos
  rw [Nat.ceil_pos]
  exact poly_pos n n_pos
}

theorem O_of_O_poly_of_scale_lt_base_pow (self : MasterRecurrence T a b n₀ f) (hd : d ≥ 1) 
    (hf_poly : f ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊) (hlt : a < Nat.cast (R := ℝ) b^d) : 
    T ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊ := by
  unfold O
  simp
  apply flip le_const_mul_of_asymp_bounded_above ceil_poly_pos at hf_poly
  specialize hf_poly 0
  rcases hf_poly with ⟨C, C_pos, f_poly⟩
  obtain ⟨K, K_pos, poly_bound⟩ := self.exists_le_of_O_poly C_pos hd f_poly

  /- use a convenient value for the constant -/
  use T ((n₀ + 1) * b + 1) + ⌈K / (1 - ↑a / ↑b ^ d)⌉₊
  have b_pow_d_pos : Nat.cast (R := ℝ) b^d > 0 :=
    Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d

  apply And.intro (by {
    apply Nat.add_pos_right
    rw [Nat.ceil_pos]
    apply div_pos
    . exact K_pos
    . rw [sub_pos, div_lt_one] <;> assumption
  })
  use n₀ * b
  intro n hn
  simp

  have n_ge_n₀ : n ≥ n₀ := le_of_mul_le_of_one_le_left hn self.b_pos
  have b_le_div : b ≤ n / n₀ := by {
    rw [Nat.le_div_iff_mul_le self.n₀_pos, mul_comm]
    exact hn
  }

  have log_le_d : Real.logb b a ≤ d := by {
    rw [Real.logb_le_iff_le_rpow] <;> norm_cast
    all_goals linarith [self.one_lt_b, self.a_pos]
  }

  have left_ceil_le_ceil : T ((n₀ + 1) * b + 1) * ⌈Nat.cast (R := ℝ) n^Real.logb b a⌉₊
                  ≤ T ((n₀ + 1) * b + 1) * ⌈Nat.cast (R := ℝ) n^d⌉₊ := by {
    apply mul_le_mul <;> norm_cast
    apply Nat.ceil_le_ceil
    rw [Real.rpow_le_rpow_left_iff] <;> norm_cast
    all_goals linarith [self.one_lt_n₀]
  }

  have right_ceil_le_ceil : ⌈GeometricSum (K := ℝ) K 
      (↑a / ↑b ^ d) (⌈Real.logb b n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ ≤ 
      ⌈K / (1 - ↑a / ↑b ^ d)⌉₊ * 
      ⌈Nat.cast (R := ℝ) n^d⌉₊ := by {
    apply mul_le_mul <;> try linarith
    apply Nat.ceil_le_ceil
    apply GeometricSum.le_of_pos_scale_of_pos_base_lt_one K_pos
    apply And.intro (div_pos (Nat.cast_pos.2 self.a_pos) (b_pow_d_pos))
    rw [div_lt_one b_pow_d_pos]
    exact hlt
  }

  have indep_bound := poly_bound n n_ge_n₀ b_le_div
  rw [add_mul (c := ⌈_⌉₊)]
  apply le_trans' (add_le_add left_ceil_le_ceil right_ceil_le_ceil)
  exact indep_bound

theorem O_of_O_poly_of_scale_eq_base_pow (self : MasterRecurrence T a b n₀ f)
    (hd : d ≥ 1) (hf_poly : f ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊)
    (heq : ↑a = Nat.cast (R := ℝ) b^d) : 
    T ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d * Real.logb b n⌉₊ := by
  unfold O
  simp
  apply flip le_const_mul_of_asymp_bounded_above ceil_poly_pos at hf_poly
  specialize hf_poly 0
  rcases hf_poly with ⟨C, C_pos, f_poly⟩
  obtain ⟨K, K_pos, poly_bound⟩ := self.exists_le_of_O_poly C_pos hd f_poly

  /- use a convenient value for the constant -/
  use T ((n₀ + 1) * b + 1) + (4 * ⌈K⌉₊ + 2)
  have b_pow_d_pos : Nat.cast (R := ℝ) b^d > 0 :=
    Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d

  apply And.intro (by linarith)
  use n₀ * b
  intro n hn
  simp

  have n_ge_n₀ : n ≥ n₀ := le_of_mul_le_of_one_le_left hn self.b_pos
  have n_ge_b : n ≥ b := le_of_mul_le_of_one_le_right hn self.n₀_pos
  have n_pos : 0 < n := le_trans self.n₀_pos n_ge_n₀
  have b_le_div : b ≤ n / n₀ := by {
    rw [Nat.le_div_iff_mul_le self.n₀_pos, mul_comm]
    exact hn
  }

  have log_eq_d : Real.logb b a = d := by {
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_cast
    all_goals linarith [self.one_lt_b, self.a_pos]
  }

  have one_le_log_n : 1 ≤ Real.logb b n := by {
    rw [← Real.logb_self_eq_one, Real.logb_le_logb, Nat.cast_le] <;> norm_cast
    all_goals linarith [self.one_lt_b]
  }
  have one_le_n_pow_d : 1 ≤ Nat.cast (R := ℝ) n^d := by {
    rw [← Real.rpow_zero n]
    apply Real.rpow_le_rpow_of_exponent_le <;> norm_cast <;> linarith
  }
  have poly_le_poly_mul_log : Nat.cast (R := ℝ) n^d ≤ ↑n^d * Real.logb b n := by {
    apply flip le_mul_of_one_le_right one_le_log_n
    exact Real.rpow_nonneg (Nat.cast_nonneg n) d
  }

  have indep_bound := poly_bound n n_ge_n₀ b_le_div
  apply le_trans indep_bound
  rw [add_mul (c := ⌈_⌉₊)]
  have a_div_b_pow_pos : Nat.cast (R := ℝ) a / ↑b^d = 1 := by {
    rw [div_eq_one_iff_eq] <;> linarith
  }
  rw [a_div_b_pow_pos, log_eq_d, GeometricSum.base_eq_one]
  apply add_le_add
  . apply mul_le_mul (le_refl _)
    apply Nat.ceil_le_ceil
    . apply le_mul_of_one_le_right
      . linarith
      . rw [← Real.logb_self_eq_one (b := b), Real.logb_le_logb] <;> norm_cast
        all_goals linarith [self.one_lt_b]
    all_goals apply zero_le
  . rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add, Nat.sub_one_add_one]

    rw [← Nat.cast_le (α := ℝ)]
    push_cast
    apply le_trans ((mul_le_mul_right _).2 (Nat.cast_le.2 (Nat.ceil_le_floor_add_one _)))
    push_cast
    apply le_trans ((mul_le_mul_left _).2 (Nat.ceil_le_two_mul _))
    apply le_trans ((mul_le_mul_right _).2 (add_le_add_right (Nat.floor_le _) _))
    apply le_trans ((mul_le_mul_right _).2 (add_le_add_right 
      ((mul_le_mul_left K_pos).2 (Nat.ceil_le_two_mul _)) _))
    ring_nf
    apply add_le_add
    . rw [mul_le_mul_right four_pos, mul_assoc]
      apply mul_le_mul (Nat.le_ceil K) (Nat.le_ceil _)
      . apply mul_nonneg <;> linarith
      . apply Nat.cast_nonneg
    . rw [mul_le_mul_right two_pos]
      apply le_trans' (Nat.le_ceil _)
      linarith
    
    case _ : ⌈_⌉₊ ≠ 0 => (
      apply ne_of_gt
      rw [Nat.ceil_pos]
      linarith
    )
    all_goals try apply mul_pos
    all_goals try apply mul_nonneg
    all_goals norm_cast
    all_goals try rw [Nat.ceil_pos]
    all_goals linarith

theorem O_of_O_poly_of_scale_gt_base_pow (self : MasterRecurrence T a b n₀ f)
    (hd : d ≥ 1) (hf_poly : f ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊)
    (hgt : ↑a > Nat.cast (R := ℝ) b^d) : 
    T ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^Real.logb b a⌉₊ := by
  unfold O
  simp
  apply flip le_const_mul_of_asymp_bounded_above ceil_poly_pos at hf_poly
  specialize hf_poly 0
  rcases hf_poly with ⟨C, C_pos, f_poly⟩
  obtain ⟨K, K_pos, poly_bound⟩ := self.exists_le_of_O_poly C_pos hd f_poly

  /- use a convenient value for the constant -/
  use T ((n₀ + 1) * b + 1) + ⌈K / (1 - ↑a / ↑b ^ d)⌉₊
  have b_pow_d_pos : Nat.cast (R := ℝ) b^d > 0 :=
    Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
  have a_div_b_pow_pos : 0 < Nat.cast (R := ℝ) a / ↑b^d := by {
    apply div_pos <;> norm_cast; linarith [self.a_pos]
  }

  apply And.intro (by {
    sorry
  })
  use n₀ * b
  intro n hn
  simp

  have n_ge_n₀ : n ≥ n₀ := le_of_mul_le_of_one_le_left hn self.b_pos
  have n_ge_b : n ≥ b := le_of_mul_le_of_one_le_right hn self.n₀_pos
  have n_pos : n > 0 := le_trans self.n₀_pos n_ge_n₀
  have b_le_div : b ≤ n / n₀ := by {
    rw [Nat.le_div_iff_mul_le self.n₀_pos, mul_comm]
    exact hn
  }

  have d_le_log : d ≤ Real.logb b a := by {
    rw [Real.le_logb_iff_rpow_le] <;> norm_cast
    all_goals linarith [self.one_lt_b, self.a_pos]
  }
  
  have log_n_pos : 0 < Real.logb b n := by {
    apply Real.logb_pos <;> norm_cast <;> linarith [self.one_lt_b]
  }

  have div_pow_log : ((Nat.cast (R := ℝ) a) / ↑b^d)^Real.logb b n = 
                        n^Real.logb b a / n^d := by {
    rw [← Real.rpow_logb (b := b) (x := (_ / _)), ← Real.rpow_mul, mul_comm,
        Real.rpow_mul, Real.rpow_logb, Real.logb_div, Real.logb_rpow, 
        Real.rpow_sub] <;> norm_cast
    all_goals linarith [self.one_lt_n₀, self.one_lt_b, self.a_pos]
  }

  have right_ceil_le_ceil : ⌈GeometricSum (K := ℝ) K (↑a / ↑b ^ d) 
      (⌈Real.logb b n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ ≤ 
      ⌈K / (1 - ↑a / ↑b ^ d)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ := by {
    rw [GeometricSum.base_ne_one, Nat.sub_one_add_one, ← Nat.cast_le (α := ℝ)]
    . push_cast
      have one_lt_const : 1 < K * ((↑a / ↑b ^ d) ^ ⌈Real.logb ↑b ↑n⌉₊ - 1) / 
          (↑a / ↑b ^ d - 1) := by {
        rw [one_lt_div]
        . sorry
        . simp
          rw [one_lt_div] <;> assumption
      }
      apply le_trans 
        (mul_le_mul (Nat.ceil_le_two_mul _) (Nat.ceil_le_two_mul _) _ _)
      . sorry
      . linarith
      . apply le_trans' (Real.one_le_rpow _ _) <;> norm_cast <;> linarith
      . apply Nat.cast_nonneg
      . linarith
    . apply ne_of_gt
      apply Nat.ceil_pos.2
      exact log_n_pos
    . apply ne_of_gt
      rw [one_lt_div] <;> assumption
  }

  have indep_bound := poly_bound n n_ge_n₀ b_le_div
  rw [add_mul]
  apply le_trans indep_bound
  apply add_le_add_left
  apply le_trans right_ceil_le_ceil
  apply mul_le_mul <;> try linarith
  apply Nat.ceil_le_ceil
  apply Real.rpow_le_rpow_of_exponent_le <;> norm_cast


end MasterRecurrence

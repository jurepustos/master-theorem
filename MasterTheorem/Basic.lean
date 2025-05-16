import Mathlib
import Init.Data.Int.Order

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv
import MasterTheorem.MasterRecurrence

namespace MasterRecurrence


variable {T f : ℕ → ℕ} {a b n₀ : ℕ} {d : ℝ}

private lemma le_of_O_poly {C : ℕ} (self : MasterRecurrence T a b n₀ f)
    (hC : C > 0) (hd : d ≥ 1) (hf_poly : ∀ m > 0, f m ≤ C * ⌈Nat.cast (R := ℝ) m^d⌉₊)
    {n : ℕ} (hn: n ≥ n₀) (hb : b ≤ n / n₀) : 
    T n ≤ T ((n₀ + 1) * b + 1) * ⌈Nat.cast (R := ℝ) n ^ (Real.logb b a)⌉₊ + ⌈GeometricSum (K := ℝ) 
      (C * 2 * 2^(d-1) * ↑b^d) (↑a / ↑b^d) (⌈Real.logb b n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ := by
  have n_pos : n > 0 := le_trans self.n₀_pos hn

  have one_lt_cast_b : 1 < Nat.cast (R := ℝ) b := by {
    rw [← Nat.cast_one, Nat.cast_lt]
    exact self.one_lt_b
  }
  have cast_b_pos : 0 < Nat.cast (R := ℝ) b := lt_trans one_pos one_lt_cast_b
  have cast_b_ne_one : Nat.cast (R := ℝ) b ≠ 1 := by {
    rw [Nat.cast_ne_one]
    apply ne_of_gt
    exact self.one_lt_b
  }
  have cast_n_pos : 0 < Nat.cast (R := ℝ) n := Nat.cast_pos.2 n_pos
  have cast_n₀_pos : 0 < Nat.cast (R := ℝ) n₀ := Nat.cast_pos.2 self.n₀_pos
  have one_lt_cast_n₀ : 1 < Nat.cast (R := ℝ) n₀ := by {
    rw [← Nat.cast_one, Nat.cast_lt]
    exact self.one_lt_n₀
  }
  have cast_a_pos : 0 < Nat.cast (R := ℝ) a := Nat.cast_pos.2 self.a_pos
  have cast_n_div_n₀_pos : 0 < Nat.cast (R := ℝ) n / ↑n₀ :=
    div_pos (Nat.cast_pos.2 n_pos) (Nat.cast_pos.2 self.n₀_pos)
  have one_le_cast_n_div_n₀ : 1 ≤ Nat.cast (R := ℝ) n / ↑n₀ := by {
    apply le_trans' Nat.cast_div_le
    rw [← Nat.cast_one, Nat.cast_le]
    exact Nat.div_pos hn self.n₀_pos
  }

  generalize k_def : ⌊Real.logb b (n / n₀)⌋₊ = k
  have k_pos : 0 < k := by {
    rw [← k_def]
    rw [Nat.floor_pos, ← Real.logb_self_eq_one one_lt_cast_b, Real.logb_le_logb]
    . apply le_trans' Nat.cast_div_le
      rw [Nat.cast_le]
      exact hb
    all_goals assumption
  }

  have subst_master := self.self_subst k k_pos hd hC hf_poly
  have subst_rec := subst_master.T_rec n (by {
    rw [← k_def, ge_iff_le, ← Nat.cast_le (α := ℝ), Nat.cast_mul, mul_comm]
    apply mul_le_of_le_div₀
    repeat apply Nat.cast_nonneg
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    apply le_trans ((Real.rpow_le_rpow_left_iff _).2 (Nat.floor_le _))
    . rw [Real.rpow_logb] <;> assumption
    . exact one_lt_cast_b
    . apply Real.logb_nonneg
      . exact one_lt_cast_b
      . rw [one_le_div (Nat.cast_pos.2 self.n₀_pos), Nat.cast_le]
        exact hn
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
      rw [← Real.rpow_logb (b := b) (x := n), Nat.cast_mul, Nat.cast_pow, 
          ← Real.rpow_natCast, ← Real.rpow_sub, Real.rpow_logb, 
          ← Real.rpow_one b, ← Real.rpow_logb (b := b) (x := n₀), 
          ← Real.rpow_add, Real.rpow_one b, Real.rpow_logb, 
          Real.rpow_le_rpow_left_iff]
      have le_log_sub : Real.logb b n - Real.logb b n₀ -1 ≤ 
                        ⌊Real.logb b n - Real.logb b n₀⌋₊ := by {
        rw [sub_le_iff_le_add', add_comm]
        apply le_trans (Nat.le_ceil _)
        rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
        apply Nat.ceil_le_floor_add_one
      }
      apply le_trans (sub_le_sub_left le_log_sub _)
      all_goals linarith
    . rw [← k_def, ← Nat.cast_le (α := ℝ), Nat.cast_pow, ← Real.rpow_natCast]
      apply le_trans' (Nat.le_ceil _)
      rw [← Real.rpow_logb (b := b) (x := Nat.cast (R := ℝ) n),
          ← Real.rpow_mul, mul_comm, Real.rpow_mul, Real.rpow_logb, 
          Real.rpow_logb]
      . apply Real.rpow_le_rpow_of_exponent_le
        . rw [← Nat.cast_one, Nat.cast_le]
          exact self.a_pos
        . apply le_trans (Nat.floor_le (Real.logb_nonneg _ _))
          rw [Real.logb_le_logb]
          apply div_le_self (Nat.cast_nonneg n)
          rw [← Nat.cast_one, Nat.cast_le]
          all_goals linarith [self.one_lt_n₀]
      all_goals linarith
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
      . rw [← k_def]
        simp
        rw [Nat.sub_add_cancel]
        . apply le_trans (Nat.floor_le_floor (b := Real.logb b n) _)
          . apply Nat.floor_le_ceil
          . rw [Real.logb_le_logb]
            . apply div_le_self (Nat.cast_nonneg _)
              rw [← Nat.cast_one, Nat.cast_le]
              exact le_of_lt self.one_lt_n₀
            all_goals assumption
        . apply Nat.ceil_pos.2
          apply Real.logb_pos <;> rw [← Nat.cast_one, Nat.cast_lt]
          all_goals linarith [self.one_lt_b]
    . apply Nat.ceil_pos.2
      exact Real.rpow_pos_of_pos (Nat.cast_pos.2 n_pos) d

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

  /- use a convenient value for the constant -/
  use 1 ⊔ (T ((n₀ + 1) * b + 1) + ⌈(Nat.cast (R := ℝ) C) * 2 * 2 ^ (d - 1) * 
    ↑b ^ d / (1 - ↑a / ↑b ^ d)⌉₊)

  apply And.intro (lt_of_lt_of_le one_pos (le_max_left 1 _))
  use n₀ * b
  intro n hn
  simp

  have n_ge_n₀ : n ≥ n₀ := le_of_mul_le_of_one_le_left hn self.b_pos
  have b_le_div : b ≤ n / n₀ := by {
    rw [Nat.le_div_iff_mul_le self.n₀_pos, mul_comm]
    exact hn
  }

  have log_le_d : Real.logb b a ≤ d := by {
    rw [Real.logb_le_iff_le_rpow]
    all_goals (try simp); linarith [self.one_lt_b, self.a_pos]
  }

  have left_ceil_le_ceil : T ((n₀ + 1) * b + 1) * ⌈Nat.cast (R := ℝ) n^Real.logb b a⌉₊
                  ≤ T ((n₀ + 1) * b + 1) * ⌈Nat.cast (R := ℝ) n^d⌉₊ := by {
    apply mul_le_mul
    . apply le_refl
    . apply Nat.ceil_le_ceil
      rw [Real.rpow_le_rpow_left_iff]
      . exact log_le_d
      . rw [← Nat.cast_one, Nat.cast_lt]
        exact lt_of_lt_of_le self.one_lt_n₀ n_ge_n₀
    all_goals (apply Nat.cast_nonneg)
  }

  have right_ceil_le_ceil : ⌈GeometricSum (K := ℝ) (↑C * 2 * 2 ^ (d - 1) * ↑b ^ d) 
      (↑a / ↑b ^ d) (⌈Real.logb b n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ ≤ 
      ⌈(Nat.cast (R := ℝ) C) * 2 * 2 ^ (d - 1) * ↑b ^ d / (1 - ↑a / ↑b ^ d)⌉₊ * 
      ⌈Nat.cast (R := ℝ) n^d⌉₊ := by {
    apply mul_le_mul
    apply Nat.ceil_le_ceil
    have b_pow_d_pos : Nat.cast (R := ℝ) b^d > 0 :=
      Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
    apply GeometricSum.le_of_pos_scale_of_pos_base_lt_one
    . apply flip mul_pos b_pow_d_pos
      apply mul_pos
      . exact mul_pos (Nat.cast_pos.2 C_pos) two_pos
      . exact Real.rpow_pos_of_pos two_pos (d-1)
    . apply And.intro (div_pos (Nat.cast_pos.2 self.a_pos) (b_pow_d_pos))
      rw [div_lt_one b_pow_d_pos]
      exact hlt
    all_goals linarith
  }

  have indep_bound := self.le_of_O_poly C_pos hd f_poly n_ge_n₀ b_le_div
  rw [max_mul, add_mul (c := ⌈_⌉₊)]
  apply le_trans' (le_max_right _ _)
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

  /- use a convenient value for the constant -/
  use 1 ⊔ (T ((n₀ + 1) * b + 1) + 
    ⌈(Nat.cast (R := ℝ) C) * 2 ^ (d - 1) * ↑b ^ d⌉₊)
  apply And.intro (lt_of_lt_of_le one_pos (le_max_left _ _))
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

  have cast_b_pos : 0 < Nat.cast (R := ℝ) b := Nat.cast_pos.2 self.b_pos
  have one_lt_cast_b : 1 < Nat.cast (R := ℝ) b := by {
    rw [← Nat.cast_one, Nat.cast_lt]
    exact self.one_lt_b
  }
  have cast_b_ne_one : Nat.cast (R := ℝ) b ≠ 1 := 
    Nat.cast_ne_one.2 (ne_of_gt self.one_lt_b)
  have cast_a_pos : 0 < Nat.cast (R := ℝ) a := Nat.cast_pos.2 self.a_pos 
  have cast_n₀_pos : 0 < Nat.cast (R := ℝ) n₀ := Nat.cast_pos.2 self.n₀_pos 
  have cast_n_pos : 0 < Nat.cast (R := ℝ) n := Nat.cast_pos.2 n_pos
  have one_le_cast_n : 1 ≤ Nat.cast (R := ℝ) n := by {
    rw [← Nat.cast_one, Nat.cast_le]
    exact n_pos
  }

  generalize k_def : Nat.log b (n / n₀) = k
  have k_pos : k > 0 := by {
    rw [← k_def]
    apply Nat.log_pos self.one_lt_b b_le_div
  }
  have n_lt_b_pow_k_succ : n < n₀ * b^(k+1) := by {
    rw [← k_def, mul_comm]
    apply Nat.lt_mul_of_div_lt
    apply Nat.lt_pow_succ_log_self self.one_lt_b
    exact self.n₀_pos
  }

  have indep_bound := self.le_of_O_poly C_pos hd f_poly n_ge_n₀ b_le_div
  have log_eq_d : Real.logb b a = d := by {
    rw [Real.logb_eq_iff_rpow_eq]
    all_goals tauto
  }

  have log_n_pos : 0 < Real.logb b n := by {
    apply Real.logb_pos one_lt_cast_b
    rw [← Nat.cast_one, Nat.cast_lt]
    linarith [self.one_lt_b]
  }
  have poly_le_poly_mul_log : Nat.cast (R := ℝ) n^d ≤ ↑n^d * Real.logb b n := by {
    apply le_mul_of_one_le_right
    . exact Real.rpow_nonneg (Nat.cast_nonneg n) d
    . rw [← Real.logb_self_eq_one one_lt_cast_b, Real.logb_le_logb, Nat.cast_le]
      all_goals assumption
  }

  rw [max_mul]
  apply le_trans' (le_max_right _ _)
  apply le_trans indep_bound
  rw [add_mul (c := ⌈_⌉₊)]
  apply add_le_add <;> apply mul_le_mul <;> try linarith
  apply Nat.ceil_le_ceil
  apply le_trans' poly_le_poly_mul_log
  apply Real.rpow_le_rpow_of_exponent_le <;> linarith

theorem O_of_O_poly_of_scale_gt_base_pow (self : MasterRecurrence T a b n₀ f) (hd : d > 0) 
    (hf_poly : f ∈ O ℕ fun n ↦ n^d) (hgt : a > b^d) : T ∈ O ℕ fun n ↦ n^Nat.log b a := by
  unfold O
  simp
  apply flip le_const_mul_of_asymp_bounded_above poly_pos at hf_poly
  specialize hf_poly 0
  rcases hf_poly with ⟨C, C_pos, f_poly⟩

  /- use a convenient value for the constant -/
  use (T (n₀ * b) + 1) ⊔ (T ((n₀ + 1) * b + 1) + 
    ⌈(Nat.cast (R := ℚ) C) * 2 ^ (d - 1) * ↑b ^ d / (1 - ↑a / ↑b ^ d)⌉.toNat)

  apply And.intro (lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _))
  use n₀ * b
  intro n hn
  simp

  have n_ge_n₀ : n ≥ n₀ := le_of_mul_le_of_one_le_left hn self.b_pos
  have n_ge_b : n ≥ b := le_of_mul_le_of_one_le_right hn self.n₀_pos
  have b_le_div : b ≤ n / n₀ := by {
    rw [Nat.le_div_iff_mul_le self.n₀_pos, mul_comm]
    exact hn
  }

  have n_pos : n > 0 := le_trans self.n₀_pos n_ge_n₀
  generalize k_def : Nat.log b (n / n₀) = k
  have k_pos : k > 0 := by {
    rw [← k_def]
    apply Nat.log_pos self.one_lt_b b_le_div
  }
  have n_lt_b_pow_k_succ : n < n₀ * b^(k+1) := by {
    rw [← k_def, mul_comm]
    apply Nat.lt_mul_of_div_lt
    apply Nat.lt_pow_succ_log_self self.one_lt_b
    exact self.n₀_pos
  }

  have div_pow_log_lt : ((Nat.cast (R := ℚ) a) / ↑b^d)^(Nat.log b n - 1) ≤ 
                        n^Nat.clog b a / n^d := by {
    generalize x_def : (Nat.cast (R := ℚ) a) / ↑b^d = x
    have one_lt_x : x > 1 := by {
      rw [← x_def, gt_iff_lt, ← Nat.cast_pow, one_lt_div, Nat.cast_lt]
      . exact hgt
      . exact Nat.cast_pos.2 (pow_pos self.b_pos d)
    }
    have log_pred_le : Nat.log b n - 1 ≤ Nat.log b n := Nat.pred_le _
    apply le_trans ((pow_le_pow_iff_right₀ one_lt_x).2 log_pred_le)
    rw [← x_def, div_pow, div_eq_mul_inv, ← pow_mul, mul_comm d, pow_mul, 
        ← inv_pow, ← Nat.cast_pow b, inv_pow, div_eq_mul_inv]
    apply mul_le_mul
    . rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_le]
      apply le_trans (pow_le_pow_left₀ (zero_le a) (Nat.le_pow_clog self.one_lt_b a) 
                      (Nat.log b n))
      rw [← pow_mul, mul_comm, pow_mul]
      apply le_trans (pow_le_pow_left₀ (zero_le (b^Nat.log b n)) 
                      (Nat.pow_log_le_self b (Nat.pos_iff_ne_zero.1 n_pos)) 
                      (Nat.clog b a))
      exact le_refl (n^Nat.clog b a)
    . rw [inv_le_inv₀, pow_le_pow_iff_left₀, Nat.cast_le]
      . sorry
      . sorry
      . sorry
      . sorry
      . sorry
      . sorry
    . rw [inv_nonneg, ← Nat.cast_pow]
      apply Nat.cast_nonneg
    . rw [← Nat.cast_pow]
      apply Nat.cast_nonneg
  }

  have ceil_le_ceil : ⌈GeometricSum (↑C * 2 ^ (d - 1) * ↑b ^ d) 
      (↑a / ↑b ^ d) (Nat.log b n - 1)⌉.toNat * n^d ≤ ⌈(Nat.cast (R := ℚ) C) * 
        2 ^ (d - 1) * ↑b ^ d / (1 - ↑a / ↑b ^ d)⌉.toNat * n^d := by {
    rw [mul_le_mul_right (pow_pos n_pos d)]
    apply Int.toNat_le_toNat
    apply Int.ceil_le_ceil
    rw [GeometricSum.base_ne_one, Nat.sub_one_add_one]
    . sorry
    . exact ne_of_gt (Nat.log_pos self.one_lt_b n_ge_b)
    . apply ne_of_gt
      rw [ ← Nat.cast_pow, one_lt_div (Nat.cast_pos.2 (pow_pos self.b_pos d)), 
          Nat.cast_lt]
      exact hgt
  }

  have indep_bound := self.le_of_O_poly C_pos hd f_poly n_ge_n₀ b_le_div
  apply le_trans' (add_le_add_left ceil_le_ceil _) at indep_bound
  have d_le_log : d ≤ Nat.clog b a := by {
    rw [← Nat.clog_pow b d self.one_lt_b]
    apply Nat.clog_mono_right
    exact le_of_lt hgt
  }

  have prod_le : n^Nat.clog b a * T ((n₀ + 1) * b + 1) ≤ n^d * T ((n₀ + 1) * b + 1) := by {
    if hT : T ((n₀ + 1) * b + 1) > 0 then {
      rw [mul_le_mul_right hT]
      exact pow_le_pow_right₀ n_pos log_le_d
    }
    else {
      apply Nat.eq_zero_of_not_pos at hT
      rw [hT, mul_zero, mul_zero]
    }
  }

  apply le_trans' (add_le_add_right prod_le _) at indep_bound
  rw [mul_comm, ← add_mul (c := n^d)] at indep_bound
  rw [max_mul]
  apply le_trans' (le_max_right _ _)
  exact indep_bound


end MasterRecurrence

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
      (C * 2^(d-1) * ↑b^d) (↑a / ↑b^d) (⌈Real.logb b n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ := by
  have n_pos : n > 0 := le_trans self.n₀_pos hn
  have n_le_log : n ≤ n₀ * ⌈Nat.cast (R := ℝ) b^(Real.logb b n + 1)⌉₊ := by {
    sorry
  }

  generalize k_def : ⌈Real.logb b (n / n₀)⌉₊ = k
  have k_pos : k > 0 := by sorry

  have a_pow_le : Nat.cast (R := ℝ) a^k ≤ a^(Real.logb b n) := by sorry
  have subst_master := self.self_subst k k_pos hd hC hf_poly
  have subst_rec := subst_master.T_rec n (by sorry)
  have T_of_add_b : T n ≤ T (n + b) := self.T_monotone (le_add_right (le_refl n))
  have pow_log_swap_le : a ^ Nat.log b n ≤ n ^ Nat.clog b a := by {
    apply le_trans (pow_le_pow_left₀ (zero_le a) (Nat.le_pow_clog self.one_lt_b a) 
                    (Nat.log b n))
    rw [← pow_mul, mul_comm, pow_mul]
    apply le_trans (pow_le_pow_left₀ (zero_le (b^Nat.log b n)) 
                    (Nat.pow_log_le_self b (Nat.pos_iff_ne_zero.1 n_pos)) 
                    (Nat.clog b a))
    exact le_refl (n^Nat.clog b a)
  }

  rw [← Nat.cast_le (α := ℝ)] at T_of_add_b subst_rec
  apply le_trans T_of_add_b
  apply le_trans subst_rec
  simp
  apply add_le_add
  . apply mul_le_mul (le_trans a_pow_le pow_log_swap_le)
    . apply self.T_monotone
      rw [add_mul, one_mul, add_assoc, add_comm b, ← add_assoc]
      apply add_le_add_right
      apply le_trans (Nat.ceilDiv_le_div_succ (pow_pos (self.b_pos) k))
      apply add_le_add_right
      apply Nat.div_le_of_le_mul
      rw [mul_comm, mul_assoc, mul_comm b, ← pow_succ]
      exact le_of_lt n_lt_b_pow_k_succ
    all_goals (apply Nat.zero_le)
  . rw [mul_le_mul_right (pow_pos n_pos d)]
    apply Int.toNat_le_toNat
    apply Int.ceil_le_ceil
    apply GeometricSum.le_of_pos_of_pos_of_le
    . apply mul_pos
      . exact mul_pos (Nat.cast_pos.2 hC) (pow_pos two_pos (d-1))
      . exact pow_pos (Nat.cast_pos.2 self.b_pos) d
    . apply div_pos (Nat.cast_pos.2 self.a_pos)
      exact pow_pos (Nat.cast_pos.2 self.b_pos) d
    . exact Nat.sub_le_sub_right k_le_log_n 1

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
  use 1 ⊔ (T ((n₀ + 1) * b + 1) + ⌈(Nat.cast (R := ℝ) C) * 2 ^ (d - 1) * 
    ↑b ^ d / (1 - ↑a / ↑b ^ d)⌉₊)

  apply And.intro (lt_of_lt_of_le one_pos (le_max_left _ _))
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
    . exact le_of_lt hlt
    . rw [← Nat.cast_one, Nat.cast_lt]
      exact self.one_lt_b
    . exact Nat.cast_pos.2 self.a_pos
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

  have right_ceil_le_ceil : ⌈GeometricSum (K := ℝ) (↑C * 2 ^ (d - 1) * ↑b ^ d) (↑a / ↑b ^ d) 
      (⌈Real.logb b n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ ≤ ⌈(Nat.cast (R := ℝ) C) * 
      2 ^ (d - 1) * ↑b ^ d / (1 - ↑a / ↑b ^ d)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ := by {
    apply mul_le_mul
    . apply Nat.ceil_le_ceil
      /- rw [mul_le_mul_right (Real.rpow_pos_of_pos (Nat.cast_pos.2 n_pos) d)] -/
      have b_pow_d_pos : Nat.cast (R := ℝ) b^d > 0 :=
        Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
      apply GeometricSum.le_of_pos_scale_of_pos_base_lt_one
      . apply flip mul_pos b_pow_d_pos
        exact mul_pos (Nat.cast_pos.2 C_pos) (Real.rpow_pos_of_pos two_pos (d-1))
      . apply And.intro (div_pos (Nat.cast_pos.2 self.a_pos) (b_pow_d_pos))
        rw [div_lt_one b_pow_d_pos]
        exact hlt
    . apply le_refl
    all_goals (apply Nat.zero_le)
  }

  have indep_bound := self.le_of_O_poly C_pos hd f_poly n_ge_n₀ b_le_div

  rw [max_mul, add_mul (c := ⌈_⌉₊)]
  apply le_trans' (le_max_right _ _)
  apply le_trans' (add_le_add left_ceil_le_ceil right_ceil_le_ceil)
  exact indep_bound

theorem O_of_O_poly_of_scale_eq_base_pow (self : MasterRecurrence T a b n₀ f) (hd : d > 0) 
    (hf_poly : f ∈ O ℕ fun n ↦ n^d) (heq : a = b^d) : T ∈ O ℕ fun n ↦ n^d * Nat.log b n := by
  unfold O
  simp
  apply flip le_const_mul_of_asymp_bounded_above poly_pos at hf_poly
  specialize hf_poly 0
  rcases hf_poly with ⟨C, C_pos, f_poly⟩

  /- use a convenient value for the constant -/
  use (T (n₀ * b) + 1) ⊔ ((T ((n₀ + 1) * b + 1) + 1) + 
    ⌈(Nat.cast (R := ℚ) C) * 2 ^ (d - 1) * ↑b ^ d⌉.toNat)
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

  have indep_bound := self.le_of_O_poly C_pos hd f_poly n_ge_n₀ b_le_div
  have log_eq_d : Nat.clog b a = d := by {
    rw [← Nat.clog_pow b d self.one_lt_b, heq]
  }

  have log_n_pos : 0 < Nat.log b n := Nat.log_pos self.one_lt_b n_ge_b
  have poly_le_poly_mul_log : n^d ≤ n^d * Nat.log b n := 
    le_mul_of_one_le_right (zero_le _) log_n_pos

  rw [heq, Nat.clog_pow b d self.one_lt_b, mul_comm, ← add_mul (c := n^d), 
      Nat.cast_pow, div_self, GeometricSum.base_eq_one] at indep_bound
  . rw [max_mul]
    apply le_trans' (le_max_right _ _)
    apply le_trans indep_bound
    rw [add_mul (c := n^d), add_mul (c := n^d * Nat.log _ n)]
    apply add_le_add
    . exact mul_le_mul (Nat.le_succ _) poly_le_poly_mul_log (zero_le _) (zero_le _)
    . rw [← Nat.cast_one (R := ℚ), Nat.cast_sub log_n_pos, Rat.sub_eq_add_neg,
          add_assoc, ← add_comm (Nat.cast 1), ← Rat.sub_eq_add_neg, sub_self,
          add_zero, mul_comm (n^d), ← mul_assoc, mul_le_mul_right (pow_pos n_pos d),
          ← Int.toNat_natCast (Nat.log b n), ← Int.toNat_mul,
          Int.toNat_natCast (Nat.log b n)]
      . apply Int.toNat_le_toNat
        rw [Int.ceil_le, Int.cast_mul, Int.cast_natCast, 
            mul_le_mul_right (Nat.cast_pos.2 log_n_pos)]
        apply Int.le_ceil
      . apply Int.ceil_nonneg
        rw [← Nat.cast_two, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_pow,
            ← Nat.cast_mul]
        apply Nat.cast_nonneg
      . apply Nat.cast_nonneg
  . rw [← Nat.cast_pow, Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero]
    exact pow_pos self.b_pos d

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

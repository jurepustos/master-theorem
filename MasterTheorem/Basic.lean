import Mathlib

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv
import MasterTheorem.MasterRecurrence

namespace MasterRecurrence

variable {T f : ℕ → ℕ} {a b d n₀ : ℕ}

private lemma le_of_O_bound {C : ℕ} (self : MasterRecurrence T a b n₀ f)
    (hC : C > 0) (hd : d > 0) (hf_poly : ∀ m > 0, f m ≤ C * m^d) (hlt : a < b^d)
    {n : ℕ} (hn: n > n₀) (hb : b ≤ n / n₀) : 
    T n ≤ n ^ (Nat.clog b a) * T ((n₀ + 1) * b + 1) + 
      ⌈(Nat.cast (R := ℚ) C) * 2 ^ (d - 1) * (↑b ^ d) / (1 - ↑a / ↑b ^ d)⌉.toNat * n ^ d := by
  have n_pos : n > 0 := le_trans (Nat.succ_le_succ (zero_le n₀)) hn
  have n_le_log : n ≤ n₀ * b^(Nat.log b n + 1) := by {
    have lt_pow_log := Nat.lt_pow_succ_log_self self.one_lt_b n
    apply flip le_mul_of_le_mul_left (le_of_lt lt_pow_log)
    rw [le_mul_iff_one_le_left n_pos]
    exact le_of_lt self.one_lt_n₀
  }

  generalize k_def : Nat.log b (n / n₀) = k
  have k_le_log_n : k ≤ Nat.log b n := by {
    rw [← k_def]
    apply Nat.log_mono_right
    exact Nat.div_le_self n n₀
  }
  have n_lt_b_pow_k_succ : n < n₀ * b^(k+1) := by {
    rw [← k_def, mul_comm]
    apply Nat.lt_mul_of_div_lt
    apply Nat.lt_pow_succ_log_self self.one_lt_b
    exact self.n₀_pos
  }
  have b_pow_k_le_n : n₀ * b^k ≤ n := by {
    rw [← k_def, mul_comm]
    apply Nat.mul_le_of_le_div
    apply Nat.pow_log_le_self
    rw [← Nat.pos_iff_ne_zero]
    exact Nat.div_pos (le_of_lt hn) self.n₀_pos
  }
  have k_pos : k > 0 :=
    Eq.subst (motive := fun n ↦ n > 0) k_def (Nat.log_pos self.one_lt_b hb)

  have a_pow_le : a^k ≤ a^(Nat.log b n) := pow_le_pow_right₀ self.a_pos k_le_log_n
  have subst_master := self.self_subst k k_pos hd hC hf_poly
  have subst_rec := subst_master.T_rec n b_pow_k_le_n
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

  apply le_trans T_of_add_b
  apply le_trans subst_rec
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
    apply GeometricSum.le_of_pos_scale_of_pos_base_lt_one
    . apply mul_pos
      . exact mul_pos (Nat.cast_pos.2 hC) (pow_pos two_pos (d-1))
      . exact pow_pos (Nat.cast_pos.2 self.b_pos) d
    . constructor
      . apply div_pos (Nat.cast_pos.2 self.a_pos)
        exact pow_pos (Nat.cast_pos.2 self.b_pos) d
      . rw [div_lt_one (pow_pos (Nat.cast_pos.2 self.b_pos) d), 
            ← Nat.cast_pow, Nat.cast_lt]
        exact hlt

theorem O_of_O_poly_of_scale_lt_base_pow (self : MasterRecurrence T a b n₀ f) (hd : d > 0) 
    (hf_poly : f ∈ O ℕ fun n ↦ n^d) (hlt : a < b^d) : T ∈ O ℕ fun n ↦ n^d := by
  have poly_pos : ∀ n > 0, n^d > 0 := by {
    intro n n_pos
    exact pow_pos n_pos d 
  }

  unfold O
  simp
  rw [le_const_mul_iff_asymp_bounded_above poly_pos n₀]
  apply flip le_const_mul_of_asymp_bounded_above poly_pos at hf_poly
  specialize hf_poly 0
  rcases hf_poly with ⟨C, C_pos, f_poly⟩

  /- use a convenient value for the constant -/
  use (T (n₀ * b) + 1) ⊔ (T ((n₀ + 1) * b + 1) + 
    ⌈(Nat.cast (R := ℚ) C) * 2 ^ (d - 1) * ↑b ^ d / (1 - ↑a / ↑b ^ d)⌉.toNat)
  apply And.intro (le_trans (Nat.succ_pos _) (le_max_left _ _))
  intro n n_gt_n₀

  have n_pos : n > 0 := le_trans (Nat.succ_le_succ (zero_le n₀)) n_gt_n₀
  generalize k_def : Nat.log b (n / n₀) = k
  have n_lt_b_pow_k_succ : n < n₀ * b^(k+1) := by {
    rw [← k_def, mul_comm]
    apply Nat.lt_mul_of_div_lt
    apply Nat.lt_pow_succ_log_self self.one_lt_b
    exact self.n₀_pos
  }
  
  if hk : k > 0 then {
    have b_le_div : b ≤ n / n₀ := by {
      apply And.left
      rw [← Nat.log_pos_iff, k_def]
      exact hk
    }
    have indep_bound := self.le_of_O_bound C_pos hd f_poly hlt n_gt_n₀ b_le_div
    have log_le_d : Nat.clog b a ≤ d := by {
      rw [← Nat.clog_pow b d self.one_lt_b]
      apply Nat.clog_mono_right
      exact le_of_lt hlt
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
  }
  else {
    apply Nat.eq_zero_of_not_pos at hk
    rw [hk, zero_add, pow_one] at n_lt_b_pow_k_succ
  
    /- use upper bound of n -/
    rw [max_mul]
    apply le_trans' (le_max_left _ _)
    apply flip le_mul_of_le_mul_left (one_le_pow₀ n_pos)
    rw [mul_one]
    apply le_trans' (Nat.le_succ _)
    exact self.T_monotone (le_of_lt n_lt_b_pow_k_succ)
  }

theorem Θ_of_Θ_poly_of_scale_lt_base_pow (self : MasterRecurrence T a b n₀ f) (hd : d > 0) 
    (hf_poly : f ∈ Θ ℕ fun n ↦ n^d) (hlt : a < b^d) : T ∈ Θ ℕ fun n ↦ n^d := by
  sorry


end MasterRecurrence

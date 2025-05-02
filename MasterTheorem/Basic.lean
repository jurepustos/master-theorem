import Mathlib

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv
import MasterTheorem.MasterRecurrence

namespace MasterRecurrence

variable {T f : ℕ → ℕ} {a b d n₀ : ℕ}

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

  /- TODO: fix this to use an actual upper bound -/
  use T (n₀ * b) ⊔ C
  apply And.intro (le_trans C_pos (le_max_right _ _))
  intro n n_gt_n₀
  
  have n_pos : n > 0 := le_trans' n_gt_n₀ (Nat.succ_le_succ (zero_le n₀))
  have n_le_log : n ≤ n₀ * b^(Nat.log b n + 1) := by {
    have lt_pow_log := Nat.lt_pow_succ_log_self self.one_lt_b n
    apply flip le_mul_of_le_mul_left (le_of_lt lt_pow_log)
    rw [le_mul_iff_one_le_left n_pos]
    exact le_of_lt self.one_lt_n₀
  }

  have k_result := find_max_k (Nat.log b n + 1) (Nat.succ_pos _) n 
                    (le_of_lt n_gt_n₀) n_le_log
  rcases k_result with ⟨k, k_le, k_ge⟩
  simp at k_le k_ge
  have a_pow_k_le_a_pow_log : a^(Fin.val k) ≤ a^(Nat.log b n) :=
    Nat.pow_le_pow_right self.a_pos (Nat.lt_succ.1 k.is_lt)

  if hk : k > 0 then {
    have subst_master := self.self_subst k hk hd C_pos f_poly
    have subst_rec := subst_master.T_rec n k_ge
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
    have log_rec : T n ≤ n ^ (Nat.clog b a) * T (n₀ * b + 1 + b) + ⌈GeometricSum 
        (↑C * 2 ^ (d - 1) * ↑b ^ d) (↑a / ↑b ^ d) (Nat.log b n - 1)⌉.toNat * n ^ d := by {
      apply le_trans T_of_add_b
      apply le_trans subst_rec
      apply add_le_add
      . apply mul_le_mul (le_trans a_pow_k_le_a_pow_log pow_log_swap_le)
        . apply self.T_monotone
          apply add_le_add_right
          apply le_trans (Nat.ceilDiv_le_div_succ (pow_pos (self.b_pos) k))
          apply add_le_add_right
          apply Nat.div_le_of_le_mul
          rw [mul_comm, mul_assoc, mul_comm b, ← pow_succ]
          exact k_le
        all_goals (apply Nat.zero_le)
      . rw [mul_le_mul_right (pow_pos n_pos d)]
        apply Int.toNat_le_toNat
        apply Int.ceil_le_ceil
        apply GeometricSum.le_of_pos_of_pos_of_le
        . apply mul_pos
          . exact mul_pos (Nat.cast_pos.2 C_pos) (pow_pos two_pos (d-1))
          . exact pow_pos (Nat.cast_pos.2 self.b_pos) d
        . apply div_pos (Nat.cast_pos.2 self.a_pos)
          exact pow_pos (Nat.cast_pos.2 self.b_pos) d
        . exact Nat.sub_le_sub_right (Fin.is_le k) 1
    }

    sorry
  }
  else {
    apply Nat.eq_zero_of_not_pos at hk
    rw [hk, pow_zero, mul_one] at k_ge
    rw [hk, zero_add, pow_one] at k_le
  
    /- abuse upper bound -/
    rw [max_mul]
    apply le_trans' (le_max_left _ _)
    apply flip le_mul_of_le_mul_left (one_le_pow₀ n_pos)
    rw [mul_one]
    exact self.T_monotone k_le
  }
where
  find_max_k (M : ℕ) (hM : M > 0) (n : ℕ) (hn : n ≥ n₀) (hn_le : n ≤ n₀ * b^M) : 
      Σ' k : Fin M, n ≤ n₀ * b^((Nat.cast k)+1) ∧ n ≥ n₀ * b^(Nat.cast k) := by
    if hn_ge : n ≥ n₀ * b^(M-1) then {
      use Fin.mk (M - 1) (Nat.pred_lt_self hM)
      constructor <;> simp
      . rw [Nat.sub_one_add_one (Nat.pos_iff_ne_zero.1 hM)]
        exact hn_le
      . exact hn_ge
    }
    else {
      simp at hn_ge
      if hM_pred_pos : M - 1 > 0 then {
        have rec_result := find_max_k (M-1) hM_pred_pos n hn (le_of_lt hn_ge)
        rcases rec_result with ⟨⟨k', hk'⟩, n_le_ge⟩
        use Fin.mk k' (lt_trans hk' (Nat.sub_one_lt (Nat.pos_iff_ne_zero.1 hM)))
      }
      else {
        simp at hM_pred_pos
        apply eq_of_le_of_le hM at hM_pred_pos
        rw [← hM_pred_pos]
        use 0
        constructor <;> simp
        . rw [← hM_pred_pos, pow_one] at hn_le
          exact hn_le
        . exact hn
      }
    }

theorem Θ_of_Θ_poly_of_scale_lt_base_pow (self : MasterRecurrence T a b n₀ f) (hd : d > 0) 
    (hf_poly : f ∈ Θ ℕ fun n ↦ n^d) (hlt : a < b^d) : T ∈ Θ ℕ fun n ↦ n^d := by
  sorry


end MasterRecurrence

import Mathlib

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv
import MasterTheorem.MasterRecurrence

namespace MasterRecurrence


variable {T f : ℕ → ℕ} {a b n₀ : ℕ} {d : ℝ}

private lemma O_of_O_poly (self : MasterRecurrence T a b n₀ f)
    (hd : d ≥ 1) (hf_poly : f ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊) : 
    T ∈ O ℕ fun n ↦ T ((n₀ + 1) * b + 1) * 
    ⌈Nat.cast (R := ℝ) n ^ (Real.logb b a)⌉₊ + ⌈GeometricSum (K := ℝ) (↑a / ↑b^d) 
    (⌈Real.logb b n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ := by
  obtain ⟨C, C_pos, subst_master⟩ := self.self_subst hd hf_poly
  use C
  apply And.intro C_pos

  use n₀ * b
  intro n hn
  simp
  have n_pos : n > 0 := by {
    apply lt_of_le_of_lt' hn
    exact mul_pos self.n₀_pos self.b_pos
  }
  have one_lt_n : n > 1 := by {
    apply lt_of_le_of_lt' hn
    apply one_lt_mul <;> linarith [self.one_lt_b, self.one_lt_n₀]
  }
  have one_le_cast_n_div_n₀ : 1 ≤ Nat.cast (R := ℝ) n / ↑n₀ := by {
    rw [one_le_div] <;> norm_cast
    . apply le_of_mul_le_of_one_le hn <;> linarith [self.one_lt_b]
    . exact self.n₀_pos
  }

  generalize k_def : ⌊Real.logb b (n / n₀)⌋₊ = k
  have k_pos : 0 < k := by {
    rw [← k_def]
    rw [Nat.floor_pos, ← Real.logb_self_eq_one, Real.logb_le_logb]
    apply le_trans' Nat.cast_div_le
    all_goals norm_cast
    rw [Nat.le_div_iff_mul_le, mul_comm]
    all_goals linarith [self.one_lt_b, self.one_lt_n₀]
  }

  specialize subst_master k k_pos
  have subst_rec := subst_master.T_rec n (by {
    rw [← k_def, ge_iff_le, ← Nat.cast_le (α := ℝ), Nat.cast_mul, mul_comm]
    apply mul_le_of_le_div₀ <;> norm_cast
    repeat apply zero_le
    push_cast
    rw [← Real.rpow_natCast]
    apply le_trans ((Real.rpow_le_rpow_left_iff _).2 (Nat.floor_le _))
    all_goals norm_cast
    . rw [Real.rpow_logb] <;> norm_cast <;> linarith [self.one_lt_b]
    . linarith [self.one_lt_b]
    . apply Real.logb_nonneg
      . norm_cast
        linarith [self.one_lt_b]
      . rw [one_le_div] <;> norm_cast
        apply le_of_mul_le_of_one_le_left (b := b)
        all_goals linarith [self.one_lt_n₀, self.one_lt_b]
  })
  have T_of_add_b : T n ≤ T (n + b) := self.T_monotone (le_add_right (le_refl n))

  apply le_trans T_of_add_b
  apply le_trans subst_rec
  rw [mul_add]
  apply add_le_add
  . rw [mul_comm, ← mul_assoc]
    apply mul_le_mul
    . apply le_trans' (le_mul_of_one_le_left _ _)
      apply self.T_monotone
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
      apply Real.rpow_le_rpow_of_exponent_le
      case _ : Nat.cast (R := ℝ) ⌊_⌋₊ ≤ _ => (
        apply le_trans (Nat.floor_le (Real.logb_nonneg _ _))
        rw [Real.logb_le_logb]
        apply div_le_self
        all_goals norm_cast
        all_goals linarith [self.one_lt_n₀, self.one_lt_b]
      )
      all_goals norm_cast
      all_goals linarith [self.a_pos, self.one_lt_b]
    all_goals apply zero_le
  . rw [mul_assoc, mul_le_mul_left C_pos, mul_le_mul_right]
    . apply Nat.ceil_le_ceil
      apply GeometricSum.le_of_pos_of_le
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

theorem O_of_O_poly_of_scale_lt_base_pow (self : MasterRecurrence T a b n₀ f)
    (hd : d ≥ 1) (hf_poly : f ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊)
    (hlt : a < Nat.cast (R := ℝ) b^d) : 
    T ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊ := by
  unfold O
  simp
  have poly_bound := self.O_of_O_poly hd hf_poly

  apply asymp_bounded_above_trans poly_bound
  apply asymp_bounded_above_add
  . if hT : T ((n₀ + 1) * b + 1) > 0 then {
      apply asymp_bounded_above_pos_smul hT
      apply asymp_bounded_above_of_asymp_le
      apply asymp_le_of_le_of_forall_ge (N := 2)

      intro n hn
      apply Nat.ceil_le_ceil
      rw [Real.rpow_le_rpow_left_iff]
      rw [Real.logb_le_iff_le_rpow]
      all_goals norm_cast
      all_goals linarith [self.a_pos, self.one_lt_b]
    }
    else {
      simp at hT
      rw [hT]
      simp

      apply asymp_bounded_above_of_asymp_le
      apply asymp_le_of_le_of_forall_ge (N := 0)
      intros
      apply Nat.cast_nonneg
    }
  . have b_pow_d_pos : Nat.cast (R := ℝ) b^d > 0 :=
      Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
    have indep_const_pos : 0 < ⌈1 / (1 - Nat.cast (R := ℝ) a / ↑b^d)⌉₊ := by {
      rw [Nat.ceil_pos]
      apply div_pos one_pos
      simp
      rw [div_lt_one] <;> assumption
    }

    apply flip asymp_bounded_above_trans
      (asymp_bounded_above_pos_smul indep_const_pos asymp_bounded_above_refl)
    apply asymp_bounded_above_of_asymp_le
    apply asymp_le_of_le_of_forall_ge (N := 0)
    intro n hn
    apply mul_le_mul <;> try linarith
    apply Nat.ceil_le_ceil
    apply GeometricSum.le_of_base_pos_lt_one
    apply div_pos <;> norm_cast
    . exact self.a_pos
    . rw [div_lt_one]
      . exact hlt
      . apply Real.rpow_pos_of_pos
        norm_cast
        exact self.b_pos

theorem O_of_O_poly_of_scale_eq_base_pow (self : MasterRecurrence T a b n₀ f)
    (hd : d ≥ 1) (hf_poly : f ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊)
    (heq : ↑a = Nat.cast (R := ℝ) b^d) : 
    T ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d * Real.logb b n⌉₊ := by
  unfold O
  simp
  have poly_bound := self.O_of_O_poly hd hf_poly

  apply asymp_bounded_above_trans poly_bound
  apply asymp_bounded_above_add
  . if hT : T ((n₀ + 1) * b + 1) > 0 then {
      apply asymp_bounded_above_pos_smul hT
      apply asymp_bounded_above_of_asymp_le
      apply asymp_le_of_le_of_forall_ge (N := b)

      intro n hn
      apply Nat.ceil_le_ceil
      have logb_a_eq_d : Real.logb b a = d := by {
        rw [heq, Real.logb_rpow] <;> norm_cast <;> linarith [self.one_lt_b]
      }
      have one_le_logb_n : 1 ≤ Real.logb b n := by {
        rw [← Real.logb_self_eq_one (b := b), Real.logb_le_logb]
        all_goals norm_cast
        all_goals linarith [self.one_lt_b]
      }
      rw [logb_a_eq_d]
      apply le_mul_of_one_le_right
      apply Real.rpow_nonneg
      apply Nat.cast_nonneg
      all_goals norm_cast
    }
    else {
      simp at hT
      rw [hT]
      simp

      apply asymp_bounded_above_of_asymp_le
      apply asymp_le_of_le_of_forall_ge (N := 0)
      intros
      apply Nat.cast_nonneg
    }
  . have b_pow_d_pos : Nat.cast (R := ℝ) b^d > 0 :=
      Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
    have a_div_b_pow_eq_one : Nat.cast (R := ℝ) a / ↑b^d = 1 := by {
      rw [div_eq_one_iff_eq] <;> linarith
    }
    have geom_indep : ∀ n ≥ b + 1, ⌈GeometricSum (K := ℝ) (↑a / ↑b ^ d) 
        (⌈Real.logb ↑b ↑n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n ^ d⌉₊ ≤ 
        6 * ⌈Nat.cast (R := ℝ) n^d * Real.logb b n⌉₊ := by {
      intro n hn
      rw [a_div_b_pow_eq_one, GeometricSum.base_eq_one]

      have one_lt_n_pow_d : 1 < Nat.cast (R := ℝ) n^d := by {
        apply Real.one_lt_rpow <;> norm_cast <;> linarith [self.one_lt_b]
      }
      have one_lt_logb_n : 1 < Real.logb b n := by {
        rw [← Real.logb_self_eq_one (b := b)]
        apply Real.logb_lt_logb
        all_goals norm_cast
        all_goals linarith [self.one_lt_b]
      }
      have left_pos : 0 < 6 * Real.logb b n := by {
        apply mul_pos <;> linarith
      }

      /- destroy the outer left ceiling -/
      apply le_trans ((mul_le_mul_right _).2 (Nat.ceil_le_floor_add_one _))
      rw [Nat.cast_sub]
      simp
    
      /- add a log and destroy the inner left ceiling -/
      rw [← Nat.cast_le (α := ℝ)]
      push_cast
      apply le_trans ((mul_le_mul_right _).2 (add_le_add_left 
        (c := Real.logb b n) _ _))
      apply le_trans ((mul_le_mul_right _).2 (add_le_add_right 
        (Nat.ceil_le_two_mul _) _))

      /- deal with right ceiling and right hand side -/
      apply le_trans ((mul_le_mul_left _).2 (Nat.ceil_le_two_mul _))
      apply le_trans' ((mul_le_mul_left _).2 (Nat.le_ceil _))
      apply le_of_eq
      ring

      /- prove residual goals -/
      all_goals norm_cast
      all_goals try rw [Nat.ceil_pos]
      case _ : 1 ≤ Nat.clog b n => (
        apply Nat.clog_pos <;> linarith [self.one_lt_b]
      )
      all_goals linarith
    }

    apply asymp_bounded_above_trans (asymp_bounded_above_of_asymp_le 
      (asymp_le_of_le_of_forall_ge geom_indep))
    apply asymp_bounded_above_pos_smul
    . trivial
    . apply asymp_bounded_above_refl

theorem O_of_O_poly_of_scale_gt_base_pow (self : MasterRecurrence T a b n₀ f)
    (hd : d ≥ 1) (hf_poly : f ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊)
    (hgt : ↑a > Nat.cast (R := ℝ) b^d) : 
    T ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^Real.logb b a⌉₊ := by
  unfold O
  simp
  have poly_bound := self.O_of_O_poly hd hf_poly

  apply asymp_bounded_above_trans poly_bound
  apply asymp_bounded_above_add
  . apply flip asymp_bounded_above_trans (asymp_bounded_above_pos_smul
      (c := T ((n₀ + 1) * b + 1) + 1) 
      (g := fun n ↦ ⌈Nat.cast (R := ℝ) n^Real.logb ↑b ↑a⌉₊) (by linarith)
      asymp_bounded_above_refl)
    apply asymp_bounded_above_of_asymp_le
    apply asymp_le_of_le_of_forall_ge (N := 1)
    intro n hn
    rw [smul_eq_mul, mul_le_mul_right]
    . linarith
    . rw [Nat.ceil_pos]
      apply Real.rpow_pos_of_pos
      norm_cast
  . have one_lt_b_pow_pos : 1 < Nat.cast (R := ℝ) b^d := by {
        rw [← Real.rpow_zero b]
        apply Real.rpow_lt_rpow_of_exponent_lt <;> norm_cast
        all_goals linarith [self.one_lt_b]
    }
    have one_lt_a_div_b_pow : 1 < Nat.cast (R := ℝ) a / ↑b^d := by {
      rw [one_lt_div] <;> linarith
    }
    have logb_a_pos : 0 < Real.logb b a := by {
      apply Real.logb_pos
      . norm_cast
        linarith [self.one_lt_b]
      . linarith
    }
    have d_lt_logb_a : d < Real.logb b a := by {
      rw [Real.lt_logb_iff_rpow_lt] <;> norm_cast
      all_goals linarith [self.one_lt_b, self.a_pos]
    }

    have pow_log_le : ∀ n ≥ b + 1, 
        (Nat.cast (R := ℝ) a / ↑b^d) ^ ↑⌈Real.logb ↑b ↑n⌉₊ ≤ 
        ↑a / ↑b^d * (↑n ^ Real.logb b a) / (↑n^d) := by {
      intro n hn
      apply le_trans (pow_le_pow_right₀ _ (Nat.ceil_le_floor_add_one _))
      rw [← Real.rpow_natCast]
      push_cast
      apply le_trans (Real.rpow_le_rpow_of_exponent_le _ 
        (add_le_add_right (Nat.floor_le _) _))
      rw [Real.rpow_add, Real.rpow_one, 
          ← Real.rpow_logb (b := b) (x := Nat.cast (R := ℝ) a / ↑b^d), 
          ← Real.rpow_mul, mul_comm (Real.logb _ _), Real.rpow_mul, 
          Real.rpow_logb, Real.rpow_logb, Real.logb_div, Real.logb_rpow, 
          Real.rpow_sub]
      apply le_of_eq
      ring

      case _ : 0 ≤ Real.logb b n => (
        apply Real.logb_nonneg <;> norm_cast <;> linarith [self.one_lt_b]
      )
      all_goals norm_cast
      all_goals linarith [self.a_pos, self.one_lt_b]
    }
    have le_n_pow_log : ∀ n ≥ b + 1, ⌈GeometricSum (Nat.cast (R := ℝ) 
        ↑a / ↑b ^ d) (⌈Real.logb ↑b ↑n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ ≤ 
        (⌈(2 - 2 / (Nat.cast (R := ℝ) a / ↑b ^ d - 1))⌉₊ + 
        ⌈2 / (↑a / ↑b ^ d - 1) * (Nat.cast (R := ℝ) a / ↑b^d)⌉₊) * 
        ⌈Nat.cast (R := ℝ) n^Real.logb b a⌉₊ := by {
      intro n hn
      rw [GeometricSum.base_ne_one, Nat.sub_one_add_one]

      have one_lt_logb_n : 1 < Real.logb b n := by {
        rw [← Real.logb_self_eq_one (b := b)]
        apply Real.logb_lt_logb 
        all_goals norm_cast 
        all_goals linarith [self.one_lt_b]
      }
      have one_lt_n_pow : 1 < Nat.cast (R := ℝ) n ^ d := by {
        apply Real.one_lt_rpow <;> norm_cast <;> linarith [self.one_lt_b]
      }

      have left_eq1 : ((Nat.cast (R := ℝ) a / ↑b ^ d) ^ 
        ⌈Real.logb ↑b ↑n⌉₊ - 1) / (↑a / ↑b ^ d - 1) = 
        1 / (↑a / ↑b^d - 1) * (↑a / ↑b^d) ^ ⌈Real.logb b n⌉₊ - 
        1 / (Nat.cast (R := ℝ) a / ↑b^d - 1) := by ring

      /- destroy ceilings on the left hard side -/
      rw [left_eq1]
      apply le_trans ((mul_le_mul_right _).2 (Nat.ceil_le_floor_add_one _))
      rw [← Nat.cast_le (α := ℝ)]
      push_cast
      apply le_trans ((mul_le_mul_left _).2 (Nat.ceil_le_two_mul _))
      apply le_trans ((mul_le_mul_right _).2 (add_le_add_right
        (Nat.floor_le _) 1))

      have left_eq2 : (1 / (Nat.cast (R := ℝ) a / ↑b ^ d - 1) * (↑a / ↑b ^ d) ^ 
        ⌈Real.logb ↑b ↑n⌉₊ - 1 / (↑a / ↑b ^ d - 1) + 1) * (2 * ↑n ^ d) =
        (2 - 2 / (↑a / ↑b ^ d - 1)) * ↑n ^ d + 2 / (↑a / ↑b ^ d - 1) *
        (↑a / ↑b ^ d) ^ ⌈Real.logb ↑b ↑n⌉₊ * ↑n ^ d := by ring

      rw [left_eq2, add_mul]
      apply add_le_add
      . apply mul_le_mul
        . apply Nat.le_ceil
        . apply le_trans' (Nat.le_ceil _)
          apply Real.rpow_le_rpow_of_exponent_le <;> norm_cast <;> linarith
        . linarith
        . apply Nat.cast_nonneg
      . apply le_trans' (mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) _ _)
        . rw [mul_assoc, mul_assoc, mul_le_mul_left]
          . apply le_trans ((mul_le_mul_right _).2 (pow_log_le n hn))
            . rw [div_mul_cancel₀]
              linarith
            . linarith
          . apply div_pos <;> linarith
        . apply Real.rpow_nonneg
          apply Nat.cast_nonneg
        . apply Nat.cast_nonneg

      case _ : 0 ≤ 1 / (Nat.cast (R := ℝ) a / ↑b ^ d - 1) * 
          (↑a / ↑b ^ d) ^ ⌈Real.logb ↑b ↑n⌉₊ - 1 / (↑a / ↑b ^ d - 1) => (
        rw [sub_nonneg]
        apply le_mul_of_one_le_right
        . apply div_nonneg <;> linarith
        . rw [← pow_zero (a := (Nat.cast (R := ℝ) a / ↑b ^ d))]
          apply pow_le_pow_right₀ <;> linarith
      )

      repeat case _ : 0 < ⌈Nat.cast (R := ℝ) n ^ d⌉₊ => (
        rw [Nat.ceil_pos]
        apply Real.rpow_pos_of_pos
        norm_cast
        linarith
      )
      case _ : ⌈Real.logb ↑b ↑n⌉₊ ≠ 0 => (
        apply ne_of_gt
        rw [Nat.ceil_pos]
        apply Real.logb_pos <;> norm_cast <;> linarith [self.one_lt_b]
      )
      all_goals linarith
    }

    apply asymp_le_of_le_of_forall_ge at le_n_pow_log
    apply asymp_bounded_above_trans
      (asymp_bounded_above_of_asymp_le le_n_pow_log)
    apply flip asymp_bounded_above_pos_smul asymp_bounded_above_refl
    apply Nat.add_pos_right
    rw [Nat.ceil_pos]
    apply mul_pos
    . apply mul_pos
      . linarith
      . rw [inv_pos]
        linarith
    . linarith


end MasterRecurrence

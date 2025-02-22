import Mathlib
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Cast.Order.Basic

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum

/- We formalize the proof at https://www.cs.dartmouth.edu/~deepc/Courses/S20/lecs/lec3supp.pdf -/

/- Divide and conquer recurrence -/
structure MasterRecurrence (T : ℤ → ℤ) (a : ℤ) (b : ℤ) (f : ℤ → ℤ) where
  /- The lowest point at which the recurrence is in the base case -/
  n₀ : ℤ
  /- n₀ has to be strictly positive -/
  n₀_pos : n₀ > 0
  /- a is positive -/
  a_pos : a > 0
  /- a is positive -/
  one_lt_b : 1 < b
  /- f is nonnegative -/
  f_nonneg : f ≥ 0
  /- Negative base cases equal zero -/
  T_neg_eq_zero : ∀ n < 0, T n = 0
  /- Base cases are nonnegative -/
  T_nonneg : T ≥ 0
  /- The recurrence formula -/
  T_rec : ∀ n ≥ n₀, T n ≤ a * T ((Rat.ofInt n) / (Rat.ofInt b)).ceil + f n
  /- f is polynomial with degree d -/
  d : ℕ
  /- f is polynomial with degree d -/
  f_poly : f ∈ O ℤ fun n ↦ n ^ d


namespace MasterRecurrence

private lemma formula_pow {T f : ℚ → ℚ} {a b C : ℚ} {n₀ k d : ℕ} (ha : a > 0) 
    (hb : b > 1) (hk : k > 0) (hC : C > 0)
    (hrec : ∀ n : ℚ, n ≥ n₀ → T n ≤ a • T (n / b) + C • n^d)
    (hpow : ∀ n : ℚ, n ≥ n₀ * b^k → T n ≤ a^k • T (n / (b^k)) + (GeometricSum 1 (a / (b^d)) (k-1)) • C • n^d) :
    ∀ n : ℚ, n ≥ n₀ * b^k → T n ≤ a^(k+1) • T (n / (b^(k+1))) + (GeometricSum 1 (a / (b^d)) k) • C • n^d := by 
  simp at *
  intro n hn
  have hbk : 0 < b^k := pow_pos (lt_trans one_pos hb) k
  have hpow_n := hpow n hn
  have hrec_nk := hrec (n / b^k) ((le_div_iff₀ hbk).2 hn)
  have T_subst : a^k * T (n / (b^k)) ≤ a^(k+1) * T (n / (b^(k+1))) + a^k * C * (n / (b^k))^d := by {
    have hak : 0 < a^k := pow_pos ha k
    suffices a^k * T (n / (b^k)) ≤ a^k * (a * T (n / (b^(k+1))) + C * (n / (b^k))^d) by {
      rw [left_distrib, ← mul_assoc, ← pow_succ, ← mul_assoc] at this
      exact this
    }
    rw [mul_le_mul_left hak]
    rw [div_div, ← pow_succ] at hrec_nk
    exact hrec_nk
  }
  have hpow_n' := le_add_of_le_add_right hpow_n T_subst
  have habk : a^k * C * (n / b^k)^d = C * n^d * (a / b^d)^k := by {
    rw [mul_comm (a^k), Rat.div_def, Rat.div_def, mul_pow, mul_pow, ← mul_assoc, ← mul_assoc,
        mul_assoc C, mul_comm (a^k), ← mul_assoc C, Rat.inv_def, Rat.divInt_pow, Rat.num_pow,
        Rat.den_pow, Rat.inv_def, Rat.divInt_pow, Rat.num_pow, Rat.den_pow, ← pow_mul, ← pow_mul,
        mul_comm d k, ← Nat.cast_pow, ← Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm d k]
  }
  rw [habk, mul_comm (GeometricSum _ _ _), add_assoc, ← mul_add (C * n^d), ← mul_comm (_ + _), 
      ← Nat.pred_eq_sub_one, ← Nat.succ_pred_eq_of_pos hk, Nat.pred_succ, 
      ← one_mul (_^k.pred.succ), GeometricSum.def_succ, Nat.succ_pred] at hpow_n'
  exact hpow_n'


variable {T f : ℤ → ℤ} {a b : ℤ}

lemma b_pos (self: MasterRecurrence T a b f) : b > 0 := lt_trans one_pos self.one_lt_b 
 
def rec_pow (self: MasterRecurrence T a b f) (k : ℕ) (hk : k > 0) : 
    MasterRecurrence T (a^k) (b^k) ((GeometricSum 1 (a/b^self.d) (k - 1)).ceil • f) :=
  {
    n₀ := self.n₀,
    n₀_pos := self.n₀_pos,
    a_pos := pow_pos self.a_pos k,
    one_lt_b := one_lt_pow₀ self.one_lt_b (zero_lt_iff.1 hk),
    f_nonneg := by {
      intro n
      apply mul_nonneg
      . unfold Rat.ceil
        split_ifs with hden
        . apply Rat.num_nonneg.2
          apply le_of_lt
          apply GeometricSum.pos_of_pos_of_pos one_pos
          apply div_pos
          . simp
            exact self.a_pos
          . apply pow_pos
            . simp
              exact self.b_pos
        . apply add_nonneg
          . apply Int.ediv_nonneg
            . apply Rat.num_nonneg.2
              apply le_of_lt
              apply GeometricSum.pos_of_pos_of_pos one_pos
              apply div_pos
              . simp
                exact self.a_pos
              . apply pow_pos
                . simp
                  exact self.b_pos
            . simp
          . apply le_of_lt
            exact one_pos
      . exact self.f_nonneg n
    }
    T_neg_eq_zero := self.T_neg_eq_zero
    T_nonneg := self.T_nonneg
    T_rec := by {
      rcases self.f_poly with ⟨C₀, C₀_pos, N₀, hf₀⟩
      generalize hN : self.n₀ ⊔ N₀ = N
      simp
      simp at hf₀

      /- We handle `n₀ ≤ n < N` separately as `f` is not bounded by 
         `C • n^d` below N. -/
      intro n
      suffices n ≥ N → T n ≤ a ^ k * T ((Rat.ofInt n) / (Rat.ofInt (b^k))).ceil + 
          (GeometricSum 1 (a / b ^ self.d) (k - 1)).ceil * f n by {
        intro hn
        simp at this
        if h : n ≥ N then {
          exact this h
        }
        else {
          simp at h
          sorry
        }
      }

      intro hn
      /- TODO: adapt, cast to ℚ and apply formula_pow -/
      simp
      unfold Rat.ceil
      split_ifs with hden_nb hden_geom
      . sorry
      . sorry
      . sorry
      . sorry
    }
    d := self.d
    f_poly := by {
      apply O_pos_smul
      . simp 
        unfold Rat.ceil
        split_ifs with hden
        . apply Rat.num_pos.2
          apply GeometricSum.pos_of_pos_of_pos one_pos
          apply div_pos
          . simp
            exact self.a_pos
          . apply pow_pos
            simp
            exact self.b_pos
        . apply Left.add_pos_of_nonneg_of_pos
          . apply Int.ediv_nonneg <;> apply le_of_lt
            . apply Rat.num_pos.2
              apply GeometricSum.pos_of_pos_of_pos one_pos
              apply div_pos
              . simp
                exact self.a_pos
              . apply pow_pos
                simp
                exact self.b_pos
            . simp
              apply Rat.den_pos
          . exact one_pos
      . exact self.f_poly
    }
  }


end MasterRecurrence


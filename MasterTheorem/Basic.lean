import Mathlib
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Cast.Order.Basic

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum


namespace Nat

lemma ceilDiv_eq_div_or_div_succ {a b : ℕ} (hb : b > 0) : a ⌈/⌉ b = a / b ∨ a ⌈/⌉ b = a / b + 1 := by 
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc, Nat.add_div]
  . split_ifs with hdiv <;> simp
    . right
      apply (Nat.div_eq_zero_iff hb).2
      apply Nat.sub_one_lt
      linarith
    . left
      apply (Nat.div_eq_zero_iff hb).2
      apply Nat.sub_one_lt
      linarith
  . exact hb
  . linarith

lemma pred_div_self {a : ℕ} (h : a > 0) : (a - 1) / a = 0 := by
  apply (Nat.div_eq_zero_iff h).2
  apply Nat.sub_one_lt
  linarith

lemma ceilDiv_le_div_succ {a b : ℕ} (hb : b > 0) : a ⌈/⌉ b ≤ a / b + 1 := by 
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc, Nat.add_div]
  . split_ifs with hdiv <;> simp <;> linarith [pred_div_self hb]
  . exact hb
  . linarith

lemma ceilDiv_le_iff {a b : ℕ} (hb : b > 0) : (∃ k, a = k * b) ↔ a / b = a ⌈/⌉ b := by
  constructor <;> intro h
  . rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc, Nat.add_div]
    split_ifs with hdiv
    . have ha : a % b = 0 := by {
        apply Nat.mod_eq_zero_of_dvd
        rw [dvd_iff_exists_eq_mul_left]
        rcases h with ⟨k, _⟩
        use k
      }
      rw [ha] at hdiv
      simp at hdiv
      contrapose hdiv
      simp
      linarith
    . simp at hdiv
      simp
      apply (Nat.div_eq_zero_iff hb).2
      apply Nat.sub_one_lt
      linarith
    . linarith
    . linarith
  . rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc, Nat.add_div] at h
    . split_ifs at h with hdiv
      . simp at hdiv
        rw [pred_div_self] at h
        . simp at h
        . exact hb
      . simp at hdiv
        apply Nat.lt_sub_of_add_lt at hdiv
        rw [Nat.sub_sub_self, Nat.lt_one_iff, ← Nat.dvd_iff_mod_eq_zero] at hdiv
        . use a / b
          symm
          exact Nat.div_mul_cancel hdiv
        . linarith
    . exact hb
    . linarith

lemma ceilDiv_div_le {a b c : ℕ} (hb : b > 0) (hc : c > 0) : a ⌈/⌉ b ⌈/⌉ c ≤ a ⌈/⌉ (b * c) := by
  have hab_c := @ceilDiv_eq_div_or_div_succ (a ⌈/⌉ b) c hc
  rcases hab_c with hab_c | hab_c <;> rw [hab_c]
  . have ha_bc := @ceilDiv_eq_div_or_div_succ a b hb
    rcases ha_bc with ha_bc | ha_bc <;> rw [ha_bc]
    . rw [Nat.div_div_eq_div_mul, ← Nat.floorDiv_eq_div]
      exact floorDiv_le_ceilDiv
    . sorry
  . sorry


end Nat

/- We formalize the proof at https://www.cs.dartmouth.edu/~deepc/Courses/S20/lecs/lec3supp.pdf -/

/- Divide and conquer recurrence -/
structure MasterRecurrence (T : ℕ → ℕ) (a b : ℕ) (f : ℕ → ℕ) where
  /-The lowest point at which the recurrence is in the base case -/
  n₀ : ℕ
  /- n₀ has to be strictly positive -/
  n₀_pos : n₀ > 0
  /-a is positive -/
  a_pos : a > 0
  /- a is positive -/
  one_lt_b : 1 < b
  /- f is monotone -/
  T_monotone : Monotone T
  /- The recurrence formula -/
  T_rec : ∀ n ≥ n₀, T n ≤ a * T (n ⌈/⌉ b) + f n
  /- f is polynomial with degree d -/
  d : ℕ
  /- f is polynomial with degree d -/
  f_poly : f ∈ O ℕ fun n ↦ n ^ d


namespace MasterRecurrence

private lemma formula_pow {T : ℕ → ℕ} {a b C n₀ k d : ℕ} (ha : a > 0) (hb : b > 1) 
    (hk : k > 0) (hrec : ∀ n : ℕ, n ≥ n₀ → T n ≤ a • T (n / b) + C • n^d)
    (hpow : ∀ n : ℕ, n ≥ n₀ * b^k → T n ≤ a^k • T (n / b^k) + (GeometricSum 1 (a / (b^d)) (k-1)).ceil.toNat • C • n^d) :
    ∀ n : ℕ, n ≥ n₀ * b^k → T n ≤ a^(k+1) • T (n / b^(k+1)) + (GeometricSum 1 (a / (b^d)) k).ceil.toNat • C • n^d := by 
  simp at *
  intro n hn

  /- substitution lemma -/
  have T_subst : a^k * T (n / b^k) ≤ a^(k+1) * T (n / b^(k+1)) + a^k * C * (n / (b^k))^d := by {
    suffices ind : a^k * T (n / b^k) ≤ a^k * (a * T (n / b^(k+1)) + C * (n / b^k)^d) by {
      rw [left_distrib, ← mul_assoc, ← pow_succ, ← mul_assoc] at ind
      exact ind
    }
    rw [mul_le_mul_left (pow_pos ha k)]
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    have bk_pos : 0 < b^k := pow_pos (lt_trans one_pos hb) k
    exact hrec (n / b^k) ((Nat.le_div_iff_mul_le bk_pos).2 hn)
  }

  /- apply substitution -/
  have hpow_n := le_add_of_le_add_right (hpow n hn) T_subst

  have habk : a^k * C * (n / b^k)^d = C * n^d * (a / b^d)^k := by {
    /- rw [mul_comm (a^k), Rat.div_def, Rat.div_def, mul_pow, mul_pow, ← mul_assoc, ← mul_assoc, -/
    /-     mul_assoc C, mul_comm (a^k), ← mul_assoc C, Rat.inv_def, Rat.divInt_pow, Rat.num_pow, -/
    /-     Rat.den_pow, Rat.inv_def, Rat.divInt_pow, Rat.num_pow, Rat.den_pow, ← pow_mul, ← pow_mul, -/
    /-     mul_comm d k, ← Nat.cast_pow, ← Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm d k] -/
    sorry
  }

  sorry


variable {T f : ℕ → ℕ} {a b : ℕ}

lemma b_pos (self: MasterRecurrence T a b f) : b > 0 := lt_trans one_pos self.one_lt_b 
 
def rec_pow (self: MasterRecurrence T a b f) (k : ℕ) (hk : k > 0) : 
    MasterRecurrence T (a^k) (b^k) (fun n ↦ (GeometricSum 1 (a/b^self.d) (k - 1)).ceil.toNat • f n) :=
  {
    n₀ := self.n₀,
    n₀_pos := self.n₀_pos,
    a_pos := pow_pos self.a_pos k,
    one_lt_b := one_lt_pow₀ self.one_lt_b (zero_lt_iff.1 hk),
    T_monotone := self.T_monotone
    T_rec := by {
      have poly_pos : ∀ n : ℕ, n ≥ self.n₀ → 0 < n^self.d := by {
        intro n hn
        induction' self.d with d hd
        . rw [pow_zero]
          exact one_pos
        . rw [pow_add, pow_one]
          apply mul_pos
          . exact hd
          . exact lt_of_lt_of_le self.n₀_pos hn
      }
      have poly_nonneg : ∀ n : ℕ, n ≥ self.n₀ → 0 ≤ n^self.d := by {
        intro n hn
        exact le_of_lt (poly_pos n hn) 
      }
      have f_bound_of_lt : ∀ N₀, ∃ C > 0, ∀ n : ℕ, n < N₀ ∧ n > 0 → f n ≤ C * n^self.d := by {
        intro N₀
        induction' N₀ with m hm
        . use 1
          constructor
          . exact one_pos
          . intro n hn
            contrapose hn
            simp
        . rcases hm with ⟨C, C_pos, hm⟩
          use C + f m
          constructor
          . linarith
          . intro n hn
            rcases hn with ⟨n_lt_succ, n_pos⟩
            rw [add_mul]
            have nd_nonneg : n^self.d ≥ 0 := pow_nonneg (by linarith) self.d
            have fm_nd_nonneg : f m * n^self.d ≥ 0 := mul_nonneg (by linarith) nd_nonneg
            simp at hm
            if hn_m : n < m then {
              apply le_add_of_le_of_nonneg
              . exact hm n hn_m (by linarith)
              . exact fm_nd_nonneg
            }
            else {
              simp at hn_m
              have n_eq_m : n = m := eq_of_le_of_le (Nat.le_of_lt_add_one n_lt_succ) hn_m
              apply le_add_of_nonneg_of_le
              . exact mul_nonneg (le_of_lt C_pos) nd_nonneg
              . rw [← mul_one (f n), ← n_eq_m]
                apply Nat.mul_le_mul_left
                . exact one_le_pow₀ n_pos
            }
      }
      have f_bound : ∃ C > 0, ∀ n > 0, f n ≤ C * n^self.d := by {
        rcases self.f_poly with ⟨C₀, C₀_pos, N₀, hf₀⟩
        rcases f_bound_of_lt N₀ with ⟨C₁, C₁_pos, hf₁⟩
        use C₀ + C₁
        constructor
        . exact add_pos C₀_pos C₁_pos
        . intro n n_pos
          rw [add_mul]
          simp at hf₀ hf₁
          if hn : n < N₀ then {
            apply le_add_of_nonneg_of_le
            . apply mul_nonneg
              . exact le_of_lt C₀_pos 
              . exact pow_nonneg (by linarith) self.d
            . exact hf₁ n hn n_pos
          }
          else {
            simp at hn
            apply le_add_of_le_of_nonneg
            . exact hf₀ n hn
            . apply mul_nonneg
              . exact le_of_lt C₁_pos 
              . exact pow_nonneg (by linarith) self.d
          }
      }

      generalize S_def : (fun n ↦ T (n + b)) = S
      have S_apply : (n : ℕ) → S n = T (n + b) := by {
        intro n
        rw [← S_def]
      }

      suffices S_rec : ∀ n : ℕ, n ≥ self.n₀ - b → S n ≤ a * S (n / b) + f (n + b) by {
        intro n hn
        simp
        have temp : T n ≤ a * T (n ⌈/⌉ b) + f n := by {
          /- generalize m_def : n - b = m -/
          specialize S_rec (n - b) (Nat.sub_le_sub_right hn b)
          rw [← S_def] at S_rec
          simp at S_rec
          exact self.T_rec n hn
        }
        sorry
      }
      
      intro n hn
      rw [← S_def]
      simp
      rw [← S_apply n, ← S_apply (n / b)] 

      sorry
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


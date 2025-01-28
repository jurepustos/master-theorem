import Mathlib
import Mathlib.Algebra.Group.Pi.Basic

import MasterTheorem.BachmanLandauNotation

/- We formalize the proof at https://www.cs.dartmouth.edu/~deepc/Courses/S20/lecs/lec3supp.pdf -/

/- Divide and conquer recurrence -/
structure MasterRecurrence (T : ℕ → ℕ) (a : ℕ) (b : ℕ) (f : ℕ → ℕ) where
  /- The lowest point at which the recurrence is in the base case -/
  n₀ : ℕ
  /- n₀ has to be strictly positive -/
  n₀_pos : n₀ > 0
  /- a is positive -/
  a_pos : a > 0
  /- a is positive -/
  b_pos : b > 0
  /- f is nonnegative -/
  f_nonneg : ∀ n, f n ≥ 0
  /- Positive base cases -/
  T_base_pos : ∀ n < n₀, T n > 0
  /- The recurrence formula -/
  T_rec : ∀ n ≥ n₀, T n ≤ a • T (n ⌈/⌉ b) + f n
  /- f is polynomial with degree d -/
  d : ℕ
  /- f is polynomial with degree d -/
  f_poly : f ∈ @O _ _ ℕ _ _ _ _ _ fun n ↦ n ^ d


namespace MasterRecurrence

variable {T f : ℕ → ℕ} {a b : ℕ} 

def const_pow (master_rec: MasterRecurrence T a b f) (k : ℕ) (hk : k > 0) : 
    MasterRecurrence T (a^k) (b^k) 
      ((Nat.fold
        (fun i acc ↦ acc + (a ⌈/⌉ b^(master_rec.d))^i) k 0) • f) :=
  {
    n₀ := master_rec.n₀,
    n₀_pos := master_rec.n₀_pos,
    a_pos := pow_pos master_rec.a_pos k,
    b_pos := pow_pos master_rec.b_pos k,
    f_nonneg := by {
      intro n
      apply mul_nonneg <;> simp
    }
    T_base_pos := master_rec.T_base_pos
    T_rec := by {
      intro n hn 
      simp
      have rec_n := master_rec.T_rec n hn
      if hnb : n ⌈/⌉ b ≥ master_rec.n₀ then {
        have nb_rec := master_rec.T_rec (n ⌈/⌉ b) hnb
        
      }
      else {
        sorry
      }
    }
    d := master_rec.d
    f_poly := by {
      generalize hc : Nat.fold (fun i acc ↦ acc + (a ⌈/⌉ b ^ master_rec.d) ^ i) k 0 = c
      have c_pos : c > 0 := by {
        rw [← hc]
        unfold Nat.fold
        split
        . contradiction
        . apply add_pos
          . sorry
          . apply pow_pos
            rw [Nat.ceilDiv_eq_add_pred_div]
            apply Nat.div_pos
            . rw [add_comm, Nat.le_sub_iff_add_le]
              . linarith [master_rec.a_pos]
              . rw [Nat.one_le_iff_ne_zero, Nat.ne_zero_iff_zero_lt]
                apply lt_trans 
                . exact pow_pos master_rec.b_pos master_rec.d
                . exact lt_add_of_pos_right (b^master_rec.d) master_rec.a_pos
            . exact Nat.pow_pos master_rec.b_pos
      }
      show AsympBoundedAbove _ _ _
      have Of := master_rec.f_poly
      rcases Of with ⟨x, x_pos, N, f_le⟩
      use x * c
      constructor
      . exact mul_pos x_pos c_pos
      . rw [mul_comm, ← smul_eq_mul]
        use N
        intro n hn
        specialize f_le n hn
        simp
        simp at f_le
        rw [mul_assoc]
        exact mul_le_mul_left' f_le c
    }
  }
    

end MasterRecurrence


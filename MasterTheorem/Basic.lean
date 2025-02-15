import Mathlib
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Cast.Order.Basic

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum

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
  one_lt_b : 1 < b
  /- f is nonnegative -/
  f_nonneg : ∀ n, f n ≥ 0
  /- Positive base cases -/
  T_base_pos : ∀ n < n₀, T n > 0
  /- The recurrence formula -/
  T_rec : ∀ n ≥ n₀, T n ≤ a * T ((Rat.ofInt n) / (Rat.ofInt b)).ceil.toNat + f n
  /- f is polynomial with degree d -/
  d : ℕ
  /- f is polynomial with degree d -/
  f_poly : f ∈ O ℕ fun n ↦ n ^ d


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
  /- TODO: extract (a/b^d)^k and rewrite with GeometricSum.def_succ -/
  sorry


variable {T f : ℕ → ℕ} {a b : ℕ}

def rec_pow (master_rec: MasterRecurrence T a b f) (k : ℕ) (hk : k > 0) : 
    MasterRecurrence T (a^k) (b^k) ((GeometricSum 1 (a/b^master_rec.d) (k - 1)).ceil.toNat • f) :=
  {
    n₀ := master_rec.n₀,
    n₀_pos := master_rec.n₀_pos,
    a_pos := pow_pos master_rec.a_pos k,
    one_lt_b := one_lt_pow₀ master_rec.one_lt_b (zero_lt_iff.1 hk),
    f_nonneg := by {
      intro n
      apply mul_nonneg <;> simp
    }
    T_base_pos := master_rec.T_base_pos
    T_rec := by {
      rcases master_rec.f_poly with ⟨C₀, C₀_pos, N₀, hf₀⟩
      generalize hN : master_rec.n₀ ⊔ N₀ = N
      simp
      simp at hf₀

      /- We handle `n₀ ≤ n < N` separately as `f` is not bounded by 
         `C • n^d` below N. -/
      intro n
      suffices n ≥ N → T n ≤ a ^ k * T ((Rat.ofInt n) / (Rat.ofInt (b^k))).ceil.toNat + 
          (GeometricSum 1 (a / b ^ master_rec.d) (k - 1)).ceil.toNat * f n by {
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
      unfold Int.toNat Rat.ceil
      split_ifs with hden_nb hden_geom
      . split <;> split
        case pos.h_1.h_1 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case pos.h_1.h_2 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case pos.h_2.h_1 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case pos.h_2.h_2 x m hnum_nb y l hnum_geom := by {
          sorry
        }
      . split <;> split
        case neg.h_1.h_1 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case neg.h_1.h_2 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case neg.h_2.h_1 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case neg.h_2.h_2 x m hnum_nb y l hnum_geom := by {
          sorry
        }
      . split <;> split
        case pos.h_1.h_1 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case pos.h_1.h_2 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case pos.h_2.h_1 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case pos.h_2.h_2 x m hnum_nb y l hnum_geom := by {
          sorry
        }
      . split <;> split
        case neg.h_1.h_1 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case neg.h_1.h_2 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case neg.h_2.h_1 x m hnum_nb y l hnum_geom := by {
          sorry
        }
        case neg.h_2.h_2 x m hnum_nb y l hnum_geom := by {
          sorry
        }
    }
    d := master_rec.d
    f_poly := by {
      apply O_pos_smul
      . simp 
        unfold Rat.ceil
        split_ifs with hden
        . apply Rat.num_pos.2
          apply GeometricSum.pos_of_pos_pos one_pos
          apply div_pos
          . simp
            exact master_rec.a_pos
          . apply pow_pos
            simp
            exact lt_trans one_pos master_rec.one_lt_b
        . apply Left.add_pos_of_nonneg_of_pos
          . apply Int.ediv_nonneg <;> apply le_of_lt
            . apply Rat.num_pos.2
              apply GeometricSum.pos_of_pos_pos one_pos
              apply div_pos
              . simp
                exact master_rec.a_pos
              . apply pow_pos
                simp
                exact lt_trans one_pos master_rec.one_lt_b
            . simp
              apply Rat.den_pos
          . exact one_pos
      . exact master_rec.f_poly
    }
  }


end MasterRecurrence


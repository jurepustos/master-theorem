import Mathlib

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv
import MasterTheorem.MasterRecurrence

namespace MasterRecurrence

variable {T f : ℕ → ℕ} {a b d : ℕ}

theorem O_of_O_poly_of_scale_lt_base_pow (self : MasterRecurrence T a b f) (hd : d > 0) 
    (hf_poly : f ∈ O ℕ fun n ↦ n^d) (hlt : a < b^d) : T ∈ O ℕ fun n ↦ n^d := by
  have poly_pos : ∀ n > 0, n^d > 0 := by {
    intro n n_pos
    exact pow_pos n_pos d 
  }

  apply flip le_const_mul_of_asymp_bounded_above poly_pos at hf_poly
  rcases hf_poly with ⟨C, C_pos, f_poly⟩
  have subst_lemma (k : ℕ) (k_pos : k > 0) := self.self_subst k k_pos hd C_pos f_poly
  use C
  apply And.intro C_pos
  use b
  intro n hn
  simp

  specialize subst_lemma (Nat.log b n) (Nat.log_pos self.one_lt_b hn)
  sorry

theorem Θ_of_Θ_poly_of_scale_lt_base_pow (self : MasterRecurrence T a b f) (hd : d > 0) 
    (hf_poly : f ∈ Θ ℕ fun n ↦ n^d) (hlt : a < b^d) : T ∈ Θ ℕ fun n ↦ n^d := by
  sorry


end MasterRecurrence

import Mathlib

variable {K : Type*} [Field K]

def GeometricSum (x : K) (n : ℕ) : K :=
  match n with
  | Nat.zero => 1
  | Nat.succ k => x^n + GeometricSum x k

namespace GeometricSum

lemma def_zero (x : K) : GeometricSum x 0 = 1 := by
  rfl

lemma def_succ (x : K) (k : ℕ) : 
    x^(k + 1) + GeometricSum x k = GeometricSum x (k + 1) := by
  unfold GeometricSum
  split
  . simp
    rw [GeometricSum.def_zero]
  . simp
    apply GeometricSum.def_succ

lemma pos_of_pos [LinearOrder K] [IsStrictOrderedRing K]
    {x : K} (hx : x > 0) (n : ℕ) : GeometricSum x n > 0 := by
  induction n with
  | zero => {
    rw [GeometricSum.def_zero]
    exact one_pos
  }
  | succ k hk => exact add_pos (pow_pos hx k.succ) hk

theorem base_eq_one (n : ℕ) : GeometricSum (1 : K) n = ↑n + 1 := by
  induction n with
  | zero => {
    rw [GeometricSum.def_zero]
    ring
  }
  | succ k hk => {
    rw [← GeometricSum.def_succ, hk]
    simp
    ring
  }

theorem base_ne_one {x : K} (h : x ≠ 1) (n : ℕ) : 
    GeometricSum x n = (x^(n+1) - 1) / (x - 1) := by
  have x_pred_ne_zero : x - 1 ≠ 0 := sub_ne_zero.2 h
  induction n with
  | zero => {
    rw [GeometricSum.def_zero]
    simp
    rw [div_self]
    exact x_pred_ne_zero
  }
  | succ k hk => {
    rw [← GeometricSum.def_succ, ← mul_one (x^(k+1)), 
        ← div_self x_pred_ne_zero, mul_div, hk, div_self x_pred_ne_zero]
    ring
  }

variable [LinearOrder K] [IsStrictOrderedRing K] 

theorem le_of_base_pos_lt_one {x : K} (hpos : 0 < x) 
    (hle : x < 1) (n : ℕ) : GeometricSum x n ≤ 1 / (1 - x) := by
  rw [GeometricSum.base_ne_one, ← neg_div_neg_eq, neg_sub, 
      div_le_div_iff₀, neg_sub, mul_le_mul_right]
  simp
  apply pow_nonneg
  all_goals linarith

lemma lt_of_pos_of_succ {x : K} (hpos : x > 0) (n : ℕ) :
    GeometricSum x n < GeometricSum x (n + 1) := by
  rw [← GeometricSum.def_succ]
  apply lt_add_of_pos_left
  exact pow_pos hpos (n + 1)

theorem lt_of_pos_of_lt {x : K} {n m : ℕ} (hpos : x > 0) 
    (hlt : n < m) : GeometricSum x n < GeometricSum x m := by
  rw [lt_iff_exists_add] at hlt
  rcases hlt with ⟨c, c_pos, m_def⟩
  if hc : c = 1 then {
    rw [m_def, hc]
    exact GeometricSum.lt_of_pos_of_succ hpos n
  }
  else {
    replace hc := lt_of_le_of_ne c_pos (Ne.intro (Ne.symm hc))
    have n_succ_lt_m : n + 1 < m := 
      lt_of_lt_of_eq (add_lt_add_left hc n) (Eq.symm m_def)
    apply lt_trans' (GeometricSum.lt_of_pos_of_lt hpos n_succ_lt_m)
    exact GeometricSum.lt_of_pos_of_succ hpos n
  }

theorem le_of_pos_of_le {x : K} {n m : ℕ} (hpos : x > 0) 
    (hle : n ≤ m) : GeometricSum x n ≤ GeometricSum x m := by
  apply lt_or_eq_of_le at hle
  rcases hle with hlt | heq
  . exact le_of_lt (GeometricSum.lt_of_pos_of_lt hpos hlt)
  . rw [heq]

end GeometricSum

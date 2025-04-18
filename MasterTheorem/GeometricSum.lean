import Mathlib

def GeometricSum (a b : ℚ) (n : ℕ) : ℚ :=
  match n with
  | Nat.zero => a
  | Nat.succ k => a * b^n + GeometricSum a b k

namespace GeometricSum

lemma def_zero (a b : ℚ) : GeometricSum a b 0 = a := by
  rfl

lemma def_succ (a b : ℚ) (k : ℕ) : a * b^(k + 1) + GeometricSum a b k = GeometricSum a b (k + 1) := by
  unfold GeometricSum
  split
  . simp
    rw [def_zero]
  . simp
    apply def_succ

lemma const_mul (a b : ℚ) (k : ℕ) (x : ℚ) : x * GeometricSum a b k = GeometricSum (x * a) b k := by
  unfold GeometricSum
  split
  . rfl
  . rw [mul_add, ← mul_assoc, const_mul]

lemma pos_of_pos_of_pos {a b : ℚ} (ha : a > 0) (hb : b > 0) (n : ℕ) : GeometricSum a b n > 0 := by
  induction n with
  | zero => exact ha
  | succ k hk => exact add_pos (mul_pos ha (pow_pos hb k.succ)) hk

theorem base_eq_one (a : ℚ) (n : ℕ) : GeometricSum a 1 n = a * (n + 1) := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_add, mul_one, GeometricSum.def_zero]
  | succ k hk => rw [← GeometricSum.def_succ, one_pow, Nat.cast_add, 
                    Nat.cast_one, mul_add, mul_one, add_comm, hk]

theorem base_ne_one (a : ℚ) {b : ℚ} (h : b ≠ 1) (n : ℕ) : 
    GeometricSum a b n = a * (b^(n+1) - 1) / (b - 1) := by
  have b_pred_neq_zero : b - 1 ≠ 0 := sub_ne_zero.2 h
  induction n with
  | zero => rw [zero_add, pow_one, ← mul_div, div_self b_pred_neq_zero, 
                mul_one, GeometricSum.def_zero]
  | succ k hk => {
    rw [← GeometricSum.def_succ, ← mul_one (a * b^(k+1)), 
        ← div_self b_pred_neq_zero, mul_div, mul_sub, hk, mul_sub, mul_sub, 
        mul_one, mul_assoc, ← pow_succ, div_self b_pred_neq_zero, mul_one,
        ← add_div, sub_eq_add_neg, add_assoc, ← add_sub_assoc, add_comm (-_),
        ← sub_eq_add_neg, sub_self, zero_sub, ← sub_eq_add_neg]
  }

theorem le_of_pos_coef_of_pos_base_lt_one {a b : ℚ} (ha : a > 0) (hb : b < 1 ∧ 0 < b) 
    (n : ℕ) : GeometricSum a b n ≤ a / (1 - b) := by
  have b_ne_one : b ≠ 1 := ne_of_lt (And.left hb)
  have one_sub_b_pos : 0 < 1 - b := sub_pos.2 (And.left hb)
  rw [GeometricSum.base_ne_one a b_ne_one, ← neg_div_neg_eq, neg_sub, 
      div_le_div_iff one_sub_b_pos one_sub_b_pos, ← mul_neg, neg_sub, mul_assoc]
  apply mul_le_mul (le_refl a)
  . apply mul_le_of_le_one_left (le_of_lt one_sub_b_pos)
    apply sub_le_self
    exact pow_nonneg (le_of_lt (And.right hb)) (n + 1)
  . apply flip mul_nonneg (le_of_lt one_sub_b_pos)
    apply sub_nonneg.2
    exact pow_le_one₀ (le_of_lt (And.right hb)) (le_of_lt (And.left hb))
  . exact le_of_lt ha


end GeometricSum

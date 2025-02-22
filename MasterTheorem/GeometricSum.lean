import Mathlib

def GeometricSum (a b : ℚ) (n : ℕ) : ℚ :=
  match n with
  | Nat.zero => a
  | Nat.succ k => a * b^n + GeometricSum a b k

namespace GeometricSum

lemma def_zero (a b : ℚ) : GeometricSum a b 0 = a := by
  unfold GeometricSum
  rfl

lemma def_succ (a b : ℚ) (k : ℕ) : a * b^(Nat.succ k) + GeometricSum a b k = GeometricSum a b (Nat.succ k) := by
  unfold GeometricSum
  split
  . simp
    rw [def_zero]
  . simp
    apply def_succ

lemma pos_of_pos_of_pos {a b : ℚ} (ha : a > 0) (hb : b > 0) (n : ℕ) : GeometricSum a b n > 0 := by
  unfold GeometricSum
  induction n with
  | zero => {
    simp
    exact ha
  }
  | succ k hk => {
    simp
    unfold GeometricSum
    have hab : a * b ^ k.succ > 0 := mul_pos ha (pow_pos hb k.succ)
    exact add_pos hab hk
  }


end GeometricSum

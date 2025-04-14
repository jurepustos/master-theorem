import Mathlib

namespace Nat


private lemma pred_div_self {a : ℕ} (h : a > 0) : (a - 1) / a = 0 := by
  apply (Nat.div_eq_zero_iff h).2
  apply Nat.sub_one_lt
  exact Nat.ne_zero_iff_zero_lt.2 h

lemma ceilDiv_eq_div_or_div_succ {a b : ℕ} (hb : b > 0) : a ⌈/⌉ b = a / b ∨ a ⌈/⌉ b = a / b + 1 := by 
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc hb, Nat.add_div hb]
  split_ifs with hdiv <;> simp
  . right
    exact pred_div_self hb
  . left
    exact pred_div_self hb

lemma ceilDiv_le_div_succ {a b : ℕ} (hb : b > 0) : a ⌈/⌉ b ≤ a / b + 1 := by 
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc hb, Nat.add_div hb]
  split_ifs with hdiv <;> simp <;> rw [pred_div_self hb]
  exact zero_le 1

theorem ceilDiv_eq_div_iff_dvd {a b : ℕ} (hb : b > 0) : b ∣ a ↔ a ⌈/⌉ b = a / b := by
  constructor <;> intro h
  . rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc hb, Nat.add_div hb]
    split_ifs with hdiv
    . rw [Nat.mod_eq_zero_of_dvd h] at hdiv
      simp at hdiv
      contrapose hdiv
      simp
      exact hb
    . simp at hdiv
      simp
      exact pred_div_self hb
  . rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc hb, Nat.add_div hb] at h
    . split_ifs at h with hdiv <;> simp at hdiv
      . rw [pred_div_self hb] at h
        simp at h
      . apply Nat.lt_sub_of_add_lt at hdiv
        rw [Nat.sub_sub_self hb, Nat.lt_one_iff, ← Nat.dvd_iff_mod_eq_zero] at hdiv
        use a / b
        symm
        exact Nat.mul_div_cancel' hdiv

private lemma one_div_of_one_lt {a : ℕ} (ha : a > 1) : 1 / a = 0 := (Nat.div_eq_zero_iff (lt_trans one_pos ha)).2 ha

theorem ceilDiv_ceilDiv_of_mul_dvd {a b c : ℕ} (hbc : b * c > 0) (hdvd : (b * c) ∣ a) : a ⌈/⌉ b ⌈/⌉ c = a / (b * c) := by
  have b_pos : b > 0 := pos_of_mul_pos_left hbc (zero_le c)
  have c_pos : c > 0 := pos_of_mul_pos_right hbc (zero_le b)
  have hdvd_b : b ∣ a := dvd_of_mul_right_dvd hdvd
  have hdvd_c : c ∣ a / b := Nat.dvd_div_of_mul_dvd hdvd
  rw [(Nat.ceilDiv_eq_div_iff_dvd b_pos).1 hdvd_b, (Nat.ceilDiv_eq_div_iff_dvd c_pos).1 hdvd_c]
  apply Nat.div_div_eq_div_mul

theorem ceilDiv_ceilDiv_le_of_right_dvd {a b c : ℕ} (hb : b > 0) (hc : c > 1) (hdvd : c ∣ a ⌈/⌉ b) : a ⌈/⌉ b ⌈/⌉ c ≤ a ⌈/⌉ (b * c) + 1 := by
  have c_pos : c > 0 := lt_trans one_pos hc
  have div_c : 1 / c = 0 := (Nat.div_eq_zero_iff c_pos).2 hc
  have bc_pos := mul_pos hb c_pos
  rw [(Nat.ceilDiv_eq_div_iff_dvd c_pos).1 hdvd, Nat.ceilDiv_eq_add_pred_div, 
      Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc hb, Nat.add_sub_assoc bc_pos, 
      add_div hb, add_div bc_pos]
  split_ifs with hmod_b hmod_bc hmod_bc <;> 
    rw [Nat.pred_div_self hb, Nat.pred_div_self bc_pos] <;> simp <;> 
      simp at hmod_b <;> simp at hmod_bc
  . rw [add_div c_pos, div_c]
    split_ifs with hmod_c <;> simp <;> rw [Nat.div_div_eq_div_mul] <;> 
      (try rw [add_assoc]) <;> apply le_add_right
  . rw [add_div c_pos, div_c]
    split_ifs with hmod_c <;> simp <;> rw [Nat.div_div_eq_div_mul]
    apply le_succ
  . rw [Nat.div_div_eq_div_mul, add_assoc, one_add_one_eq_two]
    apply le_add_right
  . rw [Nat.div_div_eq_div_mul]
    apply le_succ

theorem ceilDiv_ceilDiv_le {a b c : ℕ} (hb : b > 0) (hc : c > 1) : a ⌈/⌉ b ⌈/⌉ c ≤ a ⌈/⌉ (b * c) + 2 := by
  have c_pos : c > 0 := lt_trans one_pos hc
  have bc_pos := mul_pos hb c_pos
  apply le_trans (Nat.ceilDiv_le_div_succ c_pos)
  simp
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc hb, 
      Nat.add_sub_assoc bc_pos, Nat.add_div hb, Nat.add_div bc_pos, 
      Nat.pred_div_self hb, Nat.pred_div_self bc_pos]
  split_ifs with hmod_b hmod_bc <;> simp
  . rw [Nat.add_div c_pos, Nat.one_div_of_one_lt hc, Nat.div_div_eq_div_mul]
    split_ifs with hmod_c <;> simp
    rw [add_assoc]
    apply le_add_right
  . rw [Nat.add_div c_pos, Nat.one_div_of_one_lt hc, Nat.div_div_eq_div_mul]
    split_ifs with hmod_c <;> simp
  all_goals (
    rw [Nat.div_div_eq_div_mul]
    try rw [add_assoc]
    apply le_add_right
  )

lemma le_ceilDiv_ceilDiv {a b c : ℕ} (hb : b > 0) (hc : c > 1) : a ⌈/⌉ (b * c) - 1 ≤ a ⌈/⌉ b ⌈/⌉ c := by
  have c_pos : c > 0 := lt_trans one_pos hc
  have bc_pos := mul_pos hb c_pos
  apply le_trans' (floorDiv_le_ceilDiv)
  simp
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc bc_pos, 
      Nat.add_sub_assoc hb, Nat.add_div hb, Nat.pred_div_self hb]
  split_ifs with hmod_b <;> simp
  . rw [Nat.add_div bc_pos, Nat.add_div c_pos]
    split_ifs with hmod_bc hmod_c <;> 
      rw [Nat.pred_div_self bc_pos, Nat.one_div_of_one_lt hc, Nat.div_div_eq_div_mul] <;> simp
    rw [add_assoc]
    apply le_add_right
  . rw [Nat.add_div bc_pos]
    split_ifs with hmod_bc <;> rw [Nat.pred_div_self bc_pos, Nat.div_div_eq_div_mul]
    simp

lemma le_div_ceilDiv {a b c : ℕ} (hc : c > 1) : a / (b * c) ≤ a / b ⌈/⌉ c := by
  have c_pos : c > 0 := lt_trans one_pos hc
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc c_pos, Nat.add_div c_pos]
  split_ifs with hmod <;> rw [pred_div_self c_pos, Nat.div_div_eq_div_mul] <;> simp


end Nat

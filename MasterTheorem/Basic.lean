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

theorem ceilDiv_eq_div_iff_dvd {a b : ℕ} (hb : b > 0) : b ∣ a ↔ a ⌈/⌉ b = a / b := by
  constructor <;> intro h
  . rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc, Nat.add_div]
    split_ifs with hdiv
    . rw [Nat.mod_eq_zero_of_dvd h] at hdiv
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
    . split_ifs at h with hdiv <;> simp at hdiv
      . rw [pred_div_self] at h
        . simp at h
        . exact hb
      . apply Nat.lt_sub_of_add_lt at hdiv
        rw [Nat.sub_sub_self, Nat.lt_one_iff, ← Nat.dvd_iff_mod_eq_zero] at hdiv
        . use a / b
          symm
          exact Nat.mul_div_cancel' hdiv
        . linarith
    . exact hb
    . linarith

lemma one_div_of_gt_one {a : ℕ} (ha : a > 1) : 1 / a = 0 := (Nat.div_eq_zero_iff (by linarith)).2 ha

theorem ceilDiv_ceilDiv_of_mul_dvd {a b c : ℕ} (hbc : b * c > 0) (hdvd : (b * c) ∣ a) : a ⌈/⌉ b ⌈/⌉ c = a / (b * c) := by
  have b_pos : b > 0 := pos_of_mul_pos_left hbc (by linarith)
  have c_pos : c > 0 := pos_of_mul_pos_right hbc (by linarith)
  have hdvd_b : b ∣ a := dvd_of_mul_right_dvd hdvd
  have hdvd_c : c ∣ a / b := Nat.dvd_div_of_mul_dvd hdvd
  rw [(Nat.ceilDiv_eq_div_iff_dvd b_pos).1 hdvd_b, (Nat.ceilDiv_eq_div_iff_dvd c_pos).1 hdvd_c]
  apply Nat.div_div_eq_div_mul

theorem ceilDiv_ceilDiv_le_of_right_dvd {a b c : ℕ} (hb : b > 0) (hc : c > 1) (hdvd : c ∣ a ⌈/⌉ b) : a ⌈/⌉ b ⌈/⌉ c ≤ a ⌈/⌉ (b * c) + 1 := by
  have c_pos : c > 0 := by linarith
  have div_c : 1 / c = 0 := (Nat.div_eq_zero_iff c_pos).2 hc
  have bc_pos := mul_pos hb c_pos
  rw [(Nat.ceilDiv_eq_div_iff_dvd c_pos).1 hdvd, Nat.ceilDiv_eq_add_pred_div, 
      Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc hb, Nat.add_sub_assoc bc_pos, 
      add_div hb, add_div bc_pos]
  split_ifs with hmod_b hmod_bc hmod_bc <;> 
    rw [Nat.pred_div_self hb, Nat.pred_div_self bc_pos] <;> simp <;> 
      simp at hmod_b <;> simp at hmod_bc
  . rw [add_div c_pos, div_c]
    split_ifs with hmod_c <;> simp <;> rw [Nat.div_div_eq_div_mul] <;> linarith
  . rw [add_div c_pos, div_c]
    split_ifs with hmod_c <;> simp <;> rw [Nat.div_div_eq_div_mul]
    apply le_succ
  . rw [Nat.div_div_eq_div_mul]
    linarith
  . rw [Nat.div_div_eq_div_mul]
    apply le_succ

theorem ceilDiv_ceilDiv_le {a b c : ℕ} (hb : b > 0) (hc : c > 1) : a ⌈/⌉ b ⌈/⌉ c ≤ a ⌈/⌉ (b * c) + 2 := by
  have c_pos : c > 0 := by linarith
  have bc_pos := mul_pos hb c_pos
  apply le_trans (Nat.ceilDiv_le_div_succ (by linarith))
  simp
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc (by linarith), 
      Nat.add_sub_assoc (by linarith), Nat.add_div hb, Nat.add_div bc_pos, 
      Nat.pred_div_self hb, Nat.pred_div_self bc_pos]
  split_ifs with hmod_b hmod_bc <;> simp
  . rw [Nat.add_div c_pos, Nat.one_div_of_gt_one hc, Nat.div_div_eq_div_mul]
    split_ifs with hmod_c <;> simp
    linarith
  . rw [Nat.add_div c_pos, Nat.one_div_of_gt_one hc, Nat.div_div_eq_div_mul]
    split_ifs with hmod_c <;> simp
  . rw [Nat.div_div_eq_div_mul]
    linarith
  . rw [Nat.div_div_eq_div_mul]
    linarith

lemma le_ceilDiv_ceilDiv {a b c : ℕ} (hb : b > 0) (hc : c > 1) : a ⌈/⌉ (b * c) - 1 ≤ a ⌈/⌉ b ⌈/⌉ c := by
  have c_pos : c > 0 := by linarith
  have bc_pos := mul_pos hb c_pos
  apply le_trans' (floorDiv_le_ceilDiv)
  simp
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc (by linarith), 
      Nat.add_sub_assoc (by linarith), Nat.add_div hb, Nat.pred_div_self hb]
  split_ifs with hmod_b <;> simp
  . rw [Nat.add_div bc_pos, Nat.add_div c_pos]
    split_ifs with hmod_bc hmod_c <;> 
      rw [Nat.pred_div_self bc_pos, Nat.one_div_of_gt_one hc, Nat.div_div_eq_div_mul] <;> linarith
  . rw [Nat.add_div bc_pos]
    split_ifs with hmod_bc <;> rw [Nat.pred_div_self bc_pos, Nat.div_div_eq_div_mul]
    simp

lemma poly_pos {n d : ℕ} (hn : 0 < n) : 0 < n^d := by
  induction' d with m hm
  . rw [pow_zero]
    exact one_pos
  . rw [pow_add, pow_one]
    exact mul_pos hm hn

theorem func_le_mul_func_of_lt (f : ℕ → ℕ) {g : ℕ → ℕ} (N : ℕ) (hg : g ≥ 1) : ∃ C > 0, ∀ n < N, f n ≤ C * g n := by
  induction' N with m hm
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
    . intro n n_lt_succ
      rw [add_mul]
      if hn_m : n < m then {
        apply le_add_of_le_of_nonneg
        . exact hm n hn_m
        . apply mul_nonneg <;> linarith
      }
      else {
        simp at hn_m
        have n_eq_m : n = m := eq_of_le_of_le (Nat.le_of_lt_add_one n_lt_succ) hn_m
        apply le_add_of_nonneg_of_le
        . exact mul_nonneg (le_of_lt C_pos) (by linarith)
        . rw [← mul_one (f n), ← n_eq_m]
          apply Nat.mul_le_mul_left
          exact hg n
      }

theorem func_le_mul_func_of_asymp_bounded_above {f g : ℕ → ℕ} (h : AsympBoundedAbove ℕ f g) (hg : g ≥ 1) : ∃ C > 0, ∀ n, f n ≤ C * g n := by
  rcases h with ⟨C₀, C₀_pos, N, hbound⟩
  rcases Nat.func_le_mul_func_of_lt f N hg with ⟨C₁, C₁_pos, hlt⟩
  use C₀ + C₁
  constructor
  . exact add_pos_of_pos_of_nonneg C₀_pos (by linarith)
  . intro n
    rw [add_mul]
    if hn : N ≤ n then {
      simp at hbound
      apply le_add_of_le_of_nonneg
      . exact hbound n hn
      . exact mul_nonneg (le_of_lt C₁_pos) (by linarith)
    }
    else {
      simp at hn
      apply le_add_of_nonneg_of_le
      . apply mul_nonneg (le_of_lt C₀_pos) (by linarith)
      . exact hlt n hn
    }

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
  /- The recurrence formula -/
  T_rec : ∀ n ≥ n₀, T n ≤ a * T (n ⌈/⌉ b) + f n
  /- f is polynomial with degree d -/
  d : ℕ
  /- f is polynomial with degree d -/
  f_poly : f ∈ O ℕ fun n ↦ n ^ d


namespace MasterRecurrence

private lemma formula_le_ceil {T f : ℕ → ℕ} {a b n₀ : ℕ} {C : ℚ} (hC : C > 0)
    (hrec : ∀ n ≥ n₀, T n ≤ a * T (n / b) + C * (Rat.ofInt (f n))) : 
    ∀ n ≥ n₀, T n ≤ a * T (n / b) + ⌈C⌉.toNat * f n := by
  intro n hn
  specialize hrec n hn
  simp at hrec
  rw [← @Nat.cast_le ℚ]
  apply le_trans hrec
  simp
  unfold Int.toNat
  split
  . next k m heq => (
      rw [Int.ofNat_eq_natCast, ← @Int.cast_inj ℚ] at heq
      simp at heq
      if hfn : f n > 0 then {
        simp at hfn
        rw [← heq, mul_le_mul_right]
        . apply Int.le_ceil
        . simp
          exact hfn
      }
      else {
        simp at hfn
        rw [hfn]
        simp
      }
    )
  . next k m hCf => (
      contrapose hCf
      simp at hCf
      intro heq
      have ceil_C_nonneg : 0 ≤ ⌈C⌉ := Int.ceil_nonneg (by linarith)
      rw [heq, Int.negSucc_not_nonneg m] at ceil_C_nonneg
      exact ceil_C_nonneg
    )

private lemma formula_subst_once {T : ℕ → ℕ} {a b d C n₀ k : ℕ} (n : ℕ) (ha : a > 0)
    (hb : b > 1) (hn : n ≥ n₀ * b^k) (hC : C > 0) (hd : d > 0)
    (hrec : T (n / b^k) ≤ a * T (n / b^(k+1)) + C * (n / b^k)^d)
    (hformula : T n ≤ a^k * T (n / b^k) + (GeometricSum C (a / (b^d)) (k-1)) * n^d) :
    T n ≤ a^(k+1) * T (n / b^(k+1)) + (GeometricSum C (a / (b^d)) k) * n^d := by
  if hk : k = 0 then {
    rw [hk, GeometricSum.def_zero, zero_add, pow_one, pow_one, ← Nat.cast_mul,
        ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_le]
    rw [hk, pow_zero, Nat.div_one, zero_add, pow_one] at hrec 
    exact hrec
  }
  else {
    replace hk : k ≠ 0 := Ne.intro hk
    have b_pos : b > 0 := lt_trans one_pos hb
    have b_pow_k_pred_nonzero : b^(k-1) ≠ 0 := Nat.ne_zero_iff_zero_lt.2 (pow_pos b_pos (k-1))
    have n₀_mul_b_pow_k_pred_le_n : n₀ * b^(k-1) ≤ n := by {
      rw [← Nat.sub_one_add_one hk, pow_succ, ← mul_assoc] at hn
      exact le_of_mul_le_of_one_le_left hn b_pos
    }

    rw [← @Nat.cast_le ℚ, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow] at hrec
    rw [pow_succ, mul_assoc, ← Nat.sub_one_add_one hk, ← GeometricSum.def_succ,
        ← Nat.add_one, Nat.sub_one_add_one hk, add_mul, ← add_assoc, div_pow,
        ← pow_mul, mul_assoc (Nat.cast C), div_mul_eq_mul_div, 
        mul_comm ((Nat.cast a)^k) ((Nat.cast n)^d), ← div_mul_eq_mul_div, mul_comm d k,
        pow_mul, ← div_pow, mul_comm _ ((Nat.cast a)^k), ← mul_assoc (Nat.cast C), 
        mul_comm (Nat.cast C), mul_assoc, ← mul_add]

    apply le_add_of_le_add_right hformula
    rw [mul_le_mul_left]
    . apply le_add_of_le_add_left hrec
      rw [mul_le_mul_left, pow_le_pow_iff_left₀]
      . rw [← Nat.cast_pow]
        exact Nat.cast_div_le
      . simp
      . apply div_nonneg
        . simp
        . apply pow_nonneg
          simp
      . exact Nat.ne_zero_iff_zero_lt.2 hd
      . simp
        exact hC
    . apply pow_pos
      simp
      exact ha
  }

private theorem formula_subst {T : ℕ → ℕ} {a b d C n₀ : ℕ} (k n : ℕ) (ha : a > 0)
    (hb : b > 1) (hn : n ≥ n₀ * b^k) (hC : C > 0) (hd : d > 0)
    (hrec : ∀ m : ℕ, m ≥ n₀ → T m ≤ a * T (m / b) + C * m^d) :
    T n ≤ a^k * T (n / b^k) + (GeometricSum C (a / b^d) (k-1)) * n^d := by
  induction' k with x hx
  . rw [← Nat.cast_pow, pow_zero, Nat.zero_sub, pow_zero, 
        Nat.div_one, GeometricSum.def_zero, Nat.cast_one, one_mul]
    rw [pow_zero, mul_one] at hn
    apply le_add_of_le_of_nonneg
    . apply le_refl
    . apply mul_nonneg <;> simp
  . have n₀_mul_b_pow_x_le_n : n₀ * b^x ≤ n := by {
      rw [pow_succ, ← mul_assoc] at hn
      exact le_of_mul_le_of_one_le_left hn (le_of_lt hb)
    }
    have n₀_le_x_div_b_pow_x : n₀ ≤ n / b^x := by {
      apply (Nat.le_div_iff_mul_le (pow_pos (le_of_lt hb) x)).2 
      exact n₀_mul_b_pow_x_le_n
    }
    specialize hx n₀_mul_b_pow_x_le_n
    rw [Nat.add_one_sub_one]
    apply formula_subst_once n ha hb n₀_mul_b_pow_x_le_n hC hd
    . specialize hrec (n / b^x) n₀_le_x_div_b_pow_x
      rw [Nat.div_div_eq_div_mul, ← pow_succ] at hrec
      exact hrec
    . exact hx

variable {T f : ℕ → ℕ} {a b : ℕ}

lemma b_pos (self: MasterRecurrence T a b f) : b > 0 := lt_trans one_pos self.one_lt_b 
 
def repeat_subst (self: MasterRecurrence T a b f) (k : ℕ) (hk : k > 0) : 
    MasterRecurrence T (a^k) (b^k) (fun n ↦ (GeometricSum 1 (a/b^self.d) (k - 1)).ceil.toNat • f n) :=
  {
    n₀ := self.n₀,
    n₀_pos := self.n₀_pos,
    a_pos := pow_pos self.a_pos k,
    one_lt_b := one_lt_pow₀ self.one_lt_b (zero_lt_iff.1 hk),
    T_monotone := self.T_monotone
    T_rec := by {
      generalize S_def : (fun n ↦ T (n + 2)) = S
      have S_apply : (n : ℕ) → S n = T (n + 2) := by {
        intro n
        rw [← S_def]
      }

      intro n hn
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


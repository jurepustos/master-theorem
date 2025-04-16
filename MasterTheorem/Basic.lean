import Mathlib
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Cast.Order.Basic

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv


namespace Nat

private lemma poly_pos {n d : ℕ} (hn : 0 < n) : 0 < n^d := by
  induction' d with m hm
  . rw [pow_zero]
    exact one_pos
  . rw [pow_add, pow_one]
    exact mul_pos hm hn

private theorem func_le_mul_func_of_lt (f : ℕ → ℕ) {g : ℕ → ℕ} (N : ℕ) (hg : ∀ n ≥ 1, g n ≥ 1) : ∃ C > 0, ∀ n < N, n ≥ 1 → f n ≤ C * g n := by
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
    . exact add_pos_of_pos_of_nonneg C_pos (Nat.zero_le (f m))
    . intro n n_lt_succ n_pos
      rw [add_mul]
      if hn_m : n < m then {
        apply le_add_of_le_of_nonneg (hm n hn_m n_pos)
        apply mul_nonneg <;> apply Nat.zero_le
      }
      else {
        simp at hn_m
        have n_eq_m : n = m := eq_of_le_of_le (Nat.le_of_lt_add_one n_lt_succ) hn_m
        apply le_add_of_nonneg_of_le (mul_nonneg (le_of_lt C_pos) (zero_le (g n)))
        rw [← mul_one (f n), ← n_eq_m]
        exact Nat.mul_le_mul_left (f n) (hg n n_pos)
      }

private theorem func_le_const_mul_func_of_asymp_bounded_above {f g : ℕ → ℕ}
    (h : AsympBoundedAbove ℕ f g) (hg : ∀ n ≥ 1, g n ≥ 1) : ∃ C > 0, ∀ n ≥ 1, f n ≤ C * g n := by
  rcases h with ⟨C₀, C₀_pos, N, hbound⟩
  rcases Nat.func_le_mul_func_of_lt f N hg with ⟨C₁, C₁_pos, hlt⟩
  use C₀ + C₁
  constructor
  . exact add_pos_of_pos_of_nonneg C₀_pos (zero_le C₁)
  . intro n n_pos
    rw [add_mul]
    if hn : N ≤ n then {
      simp at hbound
      apply le_add_of_le_of_nonneg (hbound n hn)
      exact mul_nonneg (le_of_lt C₁_pos) (zero_le (g n))
    }
    else {
      simp at hn
      apply le_add_of_nonneg_of_le
      . exact mul_nonneg (le_of_lt C₀_pos) (zero_le (g n))
      . exact hlt n hn n_pos
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
  /- T is monotone -/
  T_monotone : Monotone T
  /- The recurrence formula -/
  T_rec : ∀ n ≥ n₀, T n ≤ a * T (n ⌈/⌉ b) + f n
  /- f is polynomial with degree d -/
  d : ℕ
  /- d is positive, since constant functions aren't of interest -/
  d_pos : d > 0
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
      have ceil_C_nonneg : 0 ≤ ⌈C⌉ := Int.ceil_nonneg (le_of_lt hC)
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

private lemma add_poly (self : MasterRecurrence T a b f) : 
    (fun n ↦ (n + b)^self.d) ∈ O ℕ fun n ↦ n^self.d := by
  have binom_def : ∀ x, ∀ n, (n + b)^x = ∑ m ∈ Finset.range (x + 1), 
                    n ^ m * b ^ (x - m) * ↑(x.choose m) := by {
    intro x n
    rw [add_pow]
    simp
  }
  
  induction' self.d with x hx
  . use 1
    constructor
    . exact one_pos
    . use 0
      intro n hn
      simp
  . rcases hx with ⟨C, C_pos, N, hpoly⟩
    use C + C * b
    constructor
    . exact add_pos C_pos (mul_pos C_pos self.b_pos)
    . use N + 1
      intro n hn
      simp
      rw [pow_succ, binom_def]
      specialize hpoly n (le_of_add_le_left hn)
      simp at hpoly
      rw [binom_def] at hpoly
      have n_pos : n > 0 := by linarith
      apply (mul_le_mul_right (add_pos n_pos self.b_pos)).2 at hpoly

      apply le_trans hpoly
      rw [mul_add, mul_assoc, ← pow_succ n x, mul_assoc, mul_comm _ b, ← mul_assoc]
      have le_mul_n : C * b * n^x ≤ C * b * n^(x + 1) := by {
        rw [pow_succ]
        apply mul_le_mul
        . exact le_refl (C * b)
        . exact le_mul_of_one_le_right (zero_le (n^x)) n_pos
        . exact zero_le (n^x)
        . exact zero_le (C * b)
      }
      apply le_trans (add_le_add (le_refl (C * n^(x + 1))) le_mul_n)
      rw [add_mul]

private lemma f_of_add_b_poly (self : MasterRecurrence T a b f) : 
    (fun n ↦ f (n + b)) ∈ O ℕ fun n ↦ n^self.d := by
  apply flip (O_trans ℕ) self.add_poly
  rcases self.f_poly with ⟨C, C_pos, N, hle⟩
  use C
  constructor
  . exact C_pos
  . simp
    simp at hle
    use N
    intro n n_le_N
    exact hle (n + b) (le_add_of_le_of_nonneg n_le_N (zero_le b))

noncomputable def self_subst (self : MasterRecurrence T a b f) (k : ℕ) (hk : k > 0) : 
    Σ g : ℕ → ℕ, Σ' _ : (g ∈ O ℕ fun n ↦ n^self.d),
      MasterRecurrence (fun n ↦ T (n + b)) (a^k) (b^k) 
      (fun n ↦ ⌈GeometricSum 1 (a/b^self.d) (k - 1)⌉.toNat * g n) := by
  have poly_func_pos : ∀ n ≥ 1, (fun n ↦ n^self.d) n ≥ 1 := by {
    intro n n_pos
    simp
    exact Nat.pow_pos n_pos
  }
  have f_poly := Nat.func_le_const_mul_func_of_asymp_bounded_above self.f_of_add_b_poly poly_func_pos
  generalize C_def : f_poly.choose = C
  have C_pos := f_poly.choose_spec.1
  replace f_poly := f_poly.choose_spec.2
  rw [C_def] at C_pos f_poly

  generalize g_def : (fun n ↦ C * n^self.d) = g
  use g

  have g_poly : g ∈ O ℕ fun n ↦ n^self.d := by {
    use C
    constructor
    . exact C_pos
    . use 0
      rw [← g_def]
      simp
  }
  use g_poly
  exact {
    n₀ := self.n₀ * b^k,
    n₀_pos := mul_pos self.n₀_pos (pow_pos (self.b_pos) k),
    a_pos := pow_pos self.a_pos k,
    one_lt_b := one_lt_pow₀ self.one_lt_b (zero_lt_iff.1 hk),
    T_monotone := by {
      intro x y x_le_y
      apply self.T_monotone
      exact add_le_add x_le_y (le_refl b) 
    }
    T_rec := by {
      intro n hn

      suffices T (n + b) ≤ a ^ k * T (n / b ^ k + b) + 
                ⌈GeometricSum 1 (↑a / ↑b ^ self.d) (k - 1)⌉.toNat * g n by {
        apply le_add_of_le_add_right this
        apply Nat.mul_le_mul_left
        apply self.T_monotone
        simp
        rw [← Nat.floorDiv_eq_div]
        exact floorDiv_le_ceilDiv
      }

      generalize S_def : (fun n ↦ T (n + b)) = S
      have S_apply : ∀ (n : ℕ), T (n + b) = S n := by {
        intro n
        rw [← S_def]
      }
      have n_pos : n ≥ 1 := le_trans (mul_pos self.n₀_pos (pow_pos self.b_pos k)) hn

      have rec_apply : ∀ m ≥ self.n₀, S m ≤ a * S (m / b) + C * m ^ self.d := by {
        intro m n₀_le_m
        have m_pos : m ≥ 1 := le_trans self.n₀_pos n₀_le_m
        have ceilDiv_apply := self.T_rec (m + b) (le_add_right n₀_le_m) 
        have ceilDiv_le : a * T ((m + b) ⌈/⌉ b) ≤ a * T ((m + b) / b + 1) := by {
          apply Nat.mul_le_mul_left
          apply self.T_monotone
          exact Nat.ceilDiv_le_div_succ self.b_pos
        }

        apply flip le_add_of_le_add_right ceilDiv_le at ceilDiv_apply
        rw [Nat.add_div self.b_pos, Nat.div_self self.b_pos] at ceilDiv_apply
        split_ifs at ceilDiv_apply with hrec_mod <;> simp at hrec_mod
        . contrapose hrec_mod
          intro hmod
          have hcontra := Nat.mod_lt m self.b_pos
          exact not_le_of_lt hcontra hmod 
        . simp at ceilDiv_apply
          rw [add_assoc, one_add_one_eq_two] at ceilDiv_apply
          have rec_T_le_m_add_b : a * T (m / b + 2) ≤ a * T (m / b + b) := by {
            apply Nat.mul_le_mul_left
            apply self.T_monotone
            exact add_le_add (le_refl (m / b)) self.one_lt_b
          }
          apply flip le_add_of_le_add_right rec_T_le_m_add_b at  ceilDiv_apply
          rw [S_apply, S_apply] at ceilDiv_apply
          apply flip le_add_of_le_add_left (f_poly m m_pos) at ceilDiv_apply
          exact ceilDiv_apply
      }
      
      rw [← g_def, ← mul_assoc, ← @Nat.cast_le ℚ, Nat.cast_add, Nat.cast_mul, 
          Nat.cast_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Int.ceil_toNat]

      have geom_le_ceil : GeometricSum 1 (↑a / ↑b ^ self.d) (k - 1) * C * n^self.d ≤ 
                          ⌈GeometricSum 1 (↑a / ↑b ^ self.d) (k - 1)⌉₊ * C * n^self.d := by {
        rw [mul_assoc, mul_assoc]
        have right_pos : 0 < (@Nat.cast ℚ _ C) * ↑n^self.d :=
          mul_pos (Nat.cast_pos.2 C_pos) (pow_pos (Nat.cast_pos.2 n_pos) self.d)
        apply (mul_le_mul_right right_pos).2
        apply Nat.le_ceil
      }
      rw [S_apply, S_apply]
      apply flip le_add_of_le_add_left geom_le_ceil
      rw [ ← mul_comm (Nat.cast C), GeometricSum.const_mul, mul_one]
      exact formula_subst k n self.a_pos self.one_lt_b hn C_pos self.d_pos rec_apply
    }
    d := self.d
    d_pos := self.d_pos
    f_poly := by {
      apply flip (O_pos_smul ℕ) g_poly
      simp
      apply GeometricSum.pos_of_pos_of_pos one_pos
      exact div_pos (Nat.cast_pos.2 self.a_pos) (pow_pos (Nat.cast_pos.2 self.b_pos) self.d)
    }
  }


end MasterRecurrence


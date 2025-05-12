import Mathlib

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv


theorem le_const_mul_of_asymp_bounded_above {f g : ℕ → ℕ}
    (h : AsympBoundedAbove ℕ f g) (hg : ∀ n > 0, g n > 0) (N : ℕ) : 
    ∃ C > 0, ∀ n > N, f n ≤ C * g n := by
  rcases h with ⟨C₀, C₀_pos, N', hbound⟩
  rcases func_le_mul_func_of_lt N N' with ⟨C₁, C₁_pos, hle⟩
  use C₀ + C₁
  apply And.intro (add_pos_of_pos_of_nonneg C₀_pos (zero_le C₁))
  intro n n_gt
  rw [add_mul]
  if hn : N' ≤ n then {
    simp at hbound
    apply le_add_of_le_of_nonneg (hbound n hn)
    exact mul_nonneg (le_of_lt C₁_pos) (zero_le (g n))
  }
  else {
    simp at hn
    apply le_add_of_nonneg_of_le
    . exact mul_nonneg (le_of_lt C₀_pos) (zero_le (g n))
    . exact hle n n_gt hn
  }
where
  func_le_mul_func_of_lt (N N' : ℕ) : ∃ C > 0, ∀ n > N, n < N' → f n ≤ C * g n := by
    induction' N' with m hm
    . use 1
      apply And.intro one_pos
      intro n n_pos n_lt
      contrapose n_lt
      exact Nat.not_lt_zero n
    . rcases hm with ⟨C, C_pos, f_le⟩
      use C + f m
      apply And.intro (add_pos_of_pos_of_nonneg C_pos (Nat.zero_le (f m)))
      intro n n_gt n_lt_succ
      rw [add_mul]
      if hn_m : n < m then {
        apply le_add_of_le_of_nonneg (f_le n n_gt hn_m)
        apply mul_nonneg <;> apply Nat.zero_le
      }
      else {
        simp at hn_m
        have n_eq_m : n = m := eq_of_le_of_le (Nat.le_of_lt_add_one n_lt_succ) hn_m
        apply le_add_of_nonneg_of_le (mul_nonneg (le_of_lt C_pos) (zero_le (g n)))
        rw [← mul_one (f n), ← n_eq_m]
        exact Nat.mul_le_mul_left (f n) (hg n (Nat.zero_lt_of_lt n_gt))
      }

theorem le_const_mul_iff_asymp_bounded_above {f g : ℕ → ℕ} (hg : ∀ n > 0, g n > 0) 
    (N : ℕ) : AsympBoundedAbove ℕ f g ↔ ∃ C > 0, ∀ n > N, f n ≤ C * g n := by
  constructor
  . intro h
    exact le_const_mul_of_asymp_bounded_above h hg N
  . intro h
    rcases h with ⟨C, C_pos, poly⟩
    use C
    apply And.intro C_pos
    use N + 1
    intro n n_ge
    specialize poly n n_ge
    exact poly


/- We formalize the proof at https://www.cs.dartmouth.edu/~deepc/Courses/S20/lecs/lec3supp.pdf -/

/- Divide and conquer recurrence -/
structure MasterRecurrence (T : ℕ → ℕ) (a b n₀ : ℕ) (f : ℕ → ℕ) where
  /- n₀ has to be strictly positive -/
  one_lt_n₀ : 1 < n₀
  /-a is positive -/
  a_pos : a > 0
  /- a is positive -/
  one_lt_b : 1 < b
  /- T is monotone -/
  T_monotone : Monotone T
  /- The recurrence formula -/
  T_rec : ∀ n ≥ n₀, T n ≤ a * T (n ⌈/⌉ b) + f n


namespace MasterRecurrence


private lemma formula_subst_once {T : ℕ → ℕ} {a b k : ℕ} {d C : ℝ} (n : ℕ) (ha : a > 0)
    (hC : C > 0) (hrec : T (n / b^k) ≤ a * T (n / b^(k+1)) + ⌈C * (n / Nat.cast (R := ℝ) b^k)^d⌉₊)
    (hformula : T n ≤ a^k * T (n / b^k) + ⌈(GeometricSum (K := ℝ) C (a / (b^d)) (k-1)) * n^d⌉₊) :
    T n ≤ a^(k+1) * T (n / b^(k+1)) + ⌈(GeometricSum (K := ℝ) C (a / (b^d)) k) * n^d⌉₊ := by
  if hk : k = 0 then {
    rw [hk, GeometricSum.def_zero, zero_add, pow_one, pow_one]
    rw [hk, pow_zero, Nat.div_one, zero_add, pow_one, pow_zero, div_one] at hrec 
    exact hrec
  }
  else {
    rw [pow_succ, mul_assoc, ← Nat.sub_one_add_one hk, ← GeometricSum.def_succ,
        Nat.sub_one_add_one hk, add_mul, ← add_assoc, div_pow, ← Real.rpow_natCast, 
        ← Real.rpow_natCast, ← Real.rpow_mul, mul_assoc C, 
        div_mul_eq_mul_div, mul_comm ((Nat.cast a)^(Nat.cast k)) ((Nat.cast n)^d),
        ← div_mul_eq_mul_div, mul_comm d k, Real.rpow_mul, ← Real.div_rpow, 
        mul_comm _ ((Nat.cast a)^(Nat.cast k)), ← mul_assoc C, 
        mul_comm C, mul_assoc, ← mul_add]

    apply le_add_of_le_add_right hformula
    . rw [Real.rpow_natCast, mul_le_mul_left (pow_pos (Nat.cast_pos.2 ha) k)]
      apply le_add_of_le_add_left hrec
      rw [Real.rpow_natCast, mul_le_mul_left hC]
    . apply Nat.cast_nonneg
    . rw [Real.rpow_natCast, ← Nat.cast_pow]
      apply Nat.cast_nonneg
    all_goals (apply Nat.cast_nonneg)
  }

private theorem formula_subst {T : ℕ → ℕ} {a b n₀ : ℕ} {d C : ℝ} (k n : ℕ) (ha : a > 0)
    (hb : b > 1) (hn : n ≥ n₀ * b^k) (hC : C > 0) (hd : d ≥ 1)
    (hrec : ∀ m : ℕ, m ≥ n₀ → T m ≤ a * T (m / b) + ⌈C * (Nat.cast (R := ℝ) m)^d⌉₊) :
    T n ≤ a^k * T (n / b^k) + ⌈(GeometricSum (K := ℝ) C (a / b^d) (k-1)) * n^d⌉₊ := by
  induction' k with x hx
  . rw [pow_zero, Nat.zero_sub, pow_zero, Nat.div_one, 
        GeometricSum.def_zero, one_mul]
    rw [pow_zero, mul_one] at hn
    apply le_add_of_le_of_nonneg (le_refl _)
    apply Nat.zero_le
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
    apply flip (formula_subst_once n ha hC) hx
    specialize hrec (n / b^x) n₀_le_x_div_b_pow_x
    rw [Nat.div_div_eq_div_mul, ← pow_succ] at hrec
    apply le_trans hrec
    have bound_cast_le : C * ↑(n / b ^ x) ^ d ≤ C * (Nat.cast (R := ℝ) n / ↑b ^ x) ^ d := by {
      rw [mul_le_mul_left hC, ← Nat.cast_pow]
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le
      exact le_trans (le_of_lt one_pos) hd
    }
    apply le_add_of_le_add_left _ (Nat.ceil_le_ceil bound_cast_le)
    apply le_refl


variable {T f : ℕ → ℕ} {a b n₀ : ℕ} {d : ℝ}

lemma n₀_pos (self: MasterRecurrence T a b n₀ f) : n₀ > 0 := lt_trans one_pos self.one_lt_n₀ 

lemma b_pos (self: MasterRecurrence T a b n₀ f) : b > 0 := lt_trans one_pos self.one_lt_b 

private lemma add_poly (hd : d ≥ 1) (hb : b > 1) {n : ℕ} (hn : n > 1) : 
    Nat.cast (R := NNReal) (n + b)^d ≤ (2 : NNReal)^(d-1) * b^d * n^d := by
  have one_lt_n_add_b : 1 < (Nat.cast (R := ℝ) n + ↑b) := by {
    rw [← Nat.cast_add, ← Nat.cast_one, Nat.cast_lt]
    exact Nat.lt_add_right b hn
  }

  rw [Nat.cast_add]
  apply le_trans (NNReal.rpow_add_le_mul_rpow_add_rpow n b hd)

  have n_pos : n > 0 := lt_trans one_pos hn
  have one_le_cast {k : ℕ} (hk_pos : k > 0) : 1 ≤ Nat.cast (R := NNReal) k := by {
    rw [← Nat.cast_one, Nat.cast_le]
    exact hk_pos
  }
  rw [add_comm, mul_assoc, mul_le_mul_left (NNReal.rpow_pos two_pos)]
  apply add_le_mul
  . apply le_trans' (NNReal.rpow_le_rpow_of_exponent_le _ hd)
    . rw [NNReal.rpow_one, ← Nat.cast_two, Nat.cast_le]
      exact hb
    . rw [← Nat.cast_one, Nat.cast_le]
      exact le_of_lt hb
  . apply le_trans' (NNReal.rpow_le_rpow_of_exponent_le _ hd)
    . rw [NNReal.rpow_one, ← Nat.cast_two, Nat.cast_le]
      exact hn
    . rw [← Nat.cast_one, Nat.cast_le]
      exact le_of_lt hn

private lemma f_of_add_b_poly {C : ℕ} (hd : d ≥ 1) (hC : C > 0) (hb : b > 1)
    (hf_poly : ∀ n > 0, f n ≤ C * ⌈(Nat.cast (R := ℝ) n)^d⌉₊) {n : ℕ} (hn : n > 1) : 
    f (n + b) ≤ ⌈C * (2 : ℝ) * 2^(d-1) * b^d * n^d⌉₊ := by
  specialize hf_poly (n + b) (le_add_of_le_of_nonneg (le_of_lt hn) (zero_le b))
  apply le_trans hf_poly
  have poly_le := Nat.ceil_le_ceil (add_poly hd hb hn)
  apply le_trans ((mul_le_mul_left hC).2 poly_le)
  have inner_le : C * ⌈(2 : ℝ) ^ (d - 1) * ↑b ^ d * ↑n ^ d⌉₊ ≤ 
                  C * ((2 : ℝ) * (2 ^ (d - 1) * ↑b ^ d * ↑n ^ d)) := by {
    rw [mul_le_mul_left (Nat.cast_pos.2 hC)]
    apply Nat.ceil_le_two_mul
    apply le_trans (le_of_lt two_inv_lt_one)
    apply one_le_mul_of_one_le_of_one_le
    . apply one_le_mul_of_one_le_of_one_le
      . apply Real.one_le_rpow 
        . exact one_le_two
        . exact sub_nonneg.2 hd
      . apply Real.one_le_rpow
        . rw [← Nat.cast_one, Nat.cast_le]
          exact le_of_lt hb
        . exact le_trans (le_of_lt one_pos) hd
    . apply Real.one_le_rpow
      . rw [← Nat.cast_one, Nat.cast_le]
        exact le_of_lt hn
      . exact le_trans (le_of_lt one_pos) hd
  }

  apply Nat.ceil_le_ceil at inner_le
  rw [← Nat.cast_mul, Nat.ceil_natCast, ← mul_assoc, ← mul_assoc, 
      ← mul_assoc] at inner_le
  exact inner_le

private lemma le_mul_ceil {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] {n : ℕ} {x : R} : ⌈n * x⌉₊ ≤ n * ⌈x⌉₊ := by
  induction' n with k hk
  . rw [zero_mul, Nat.cast_zero, zero_mul, ← Nat.ceil_zero (R := R)]
  . rw [add_mul, one_mul, Nat.cast_add, add_mul, Nat.cast_one, one_mul]
    apply le_trans (Nat.ceil_add_le _ _)
    apply add_le_add_right
    exact hk


def self_subst {C : ℕ} (self : MasterRecurrence T a b n₀ f) (k : ℕ)
    (hk : k > 0) (hd : d ≥ 1) (hC : C > 0) (hf_poly : ∀ n > 0, f n ≤ C * ⌈(Nat.cast (R := ℝ) n)^d⌉₊) : 
    MasterRecurrence (fun n ↦ T (n + b)) (a^k) (b^k) (n₀ * b^k)
    (fun n ↦ ⌈GeometricSum (K := ℝ) (↑C * 2 * (2 : ℝ)^(d-1) * ↑b^d) (a/b^d) (k - 1) * n^d⌉₊) :=
  {
    one_lt_n₀ := one_lt_mul_of_lt_of_le self.one_lt_n₀ (pow_pos self.b_pos k),
    a_pos := pow_pos self.a_pos k,
    one_lt_b := one_lt_pow₀ self.one_lt_b (zero_lt_iff.1 hk),
    T_monotone := by {
      intro x y x_le_y
      exact self.T_monotone (add_le_add x_le_y (le_refl b))
    }
    T_rec := by {
      intro n hn

      suffices add_b : T (n + b) ≤ a ^ k * T (n / b ^ k + b) + 
                ⌈GeometricSum (K := ℝ) (C * 2 * 2^(d-1) * b^d) (↑a/↑b^d) (k-1) * n^d⌉₊ by {
        apply le_add_of_le_add_right add_b
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
      have n_pos : n > 0 := le_trans (mul_pos self.n₀_pos (pow_pos self.b_pos k)) hn

      have rec_apply : ∀ m ≥ n₀, S m ≤ a * S (m / b) + ⌈C * 2 * (2 : ℝ)^(d-1) * b^d * m^d⌉₊ := by {
        intro m n₀_le_m
        have m_gt_one : m > 1 := lt_of_lt_of_le self.one_lt_n₀ n₀_le_m
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
          
          have f_le := f_of_add_b_poly hd hC self.one_lt_b hf_poly m_gt_one
          exact le_add_of_le_add_left ceilDiv_apply f_le
      }
      
      rw [← Nat.cast_le (α := ℝ), Nat.cast_add, Nat.cast_mul, Nat.cast_pow]

      have const_pos : 0 < ↑C * 2 * (2 : ℝ)^(d-1) * b^d := by {
        apply mul_pos
        . apply mul_pos 
          . exact mul_pos (Nat.cast_pos.2 hC) two_pos
          . exact NNReal.rpow_pos two_pos
        . exact NNReal.rpow_pos (Nat.cast_pos.2 self.b_pos)
      }
      rw [S_apply, S_apply]
      rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_le]
      exact formula_subst k n self.a_pos self.one_lt_b hn const_pos hd rec_apply
    }
  }


end MasterRecurrence


import Mathlib

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv


namespace Nat

lemma bounded_above_of_asymp_le {f g : ℕ → ℕ}
    (h : AsympLE f g) {N : ℕ} (hg : ∀ n > N, g n > 0) : 
    ∃ C > 0, ∀ n > N, f n ≤ C * g n := by
  rcases h with ⟨N', hbound⟩
  rcases func_le_mul_func_of_lt N' with ⟨C, C_pos, hle⟩
  use C
  apply And.intro C_pos
  intro n n_gt
  if hn : N' ≤ n then {
    apply le_trans (hbound n hn)
    specialize hg n n_gt
    apply le_mul_of_one_le_left <;> linarith
  }
  else {
    simp at hn
    exact hle n n_gt hn
  }
where
  func_le_mul_func_of_lt (N' : ℕ) : ∃ C > 0, ∀ n > N, n < N' → f n ≤ C * g n := by
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
        exact Nat.mul_le_mul_left (f n) (hg n n_gt)
      }

end Nat


/- We formalize the proof at https://www.cs.dartmouth.edu/~deepc/Courses/S20/lecs/lec3supp.pdf -/

/- Divide and conquer recurrence -/
structure MasterRecurrence (T : ℕ → ℕ) (a b n₀ : ℕ) (f : ℕ → ℕ) (d : ℝ) where
  /- there should be at least one boundary condition -/
  one_lt_n₀ : 1 < n₀
  /-a is positive -/
  a_pos : a > 0
  /- we always divide into more than than one part -/
  one_lt_b : 1 < b
  /- f is polynomially bounded above -/
  f_poly : f ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊
  /- polynomial degree is at least 1 -/
  one_le_d : 1 ≤ d
  /- T is monotone -/
  T_monotone : Monotone T
  /- The recurrence formula -/
  T_rec : ∀ n ≥ n₀, T n ≤ a * T (n ⌈/⌉ b) + f n


namespace MasterRecurrence


private lemma formula_subst_once {T : ℕ → ℕ} {a b k : ℕ} {d C : ℝ} (n : ℕ) 
    (ha : a > 0) (hrec : T (n / b^k) ≤ a * T (n / b^(k+1)) + 
      C * (n / Nat.cast (R := ℝ) b^k)^d)
    (hformula : T n ≤ a^k * T (n / b^k) + C * GeometricSum (K := ℝ)
      (a / (b^d)) (k-1) * Nat.cast (R := ℝ) n^d) :
    T n ≤ a^(k+1) * T (n / b^(k+1)) + C * GeometricSum (K := ℝ) 
      (a / (b^d)) k * Nat.cast (R := ℝ) n^d := by
  if hk : k = 0 then {
    rw [hk, GeometricSum.def_zero]
    simp
    rw [hk] at hrec
    simp at hrec
    exact hrec
  }
  else {
    rw [pow_succ, mul_assoc, ← Nat.sub_one_add_one hk, ← GeometricSum.def_succ,
        Nat.sub_one_add_one hk, mul_add, add_mul, ← add_assoc]

    apply le_add_of_le_add_right hformula
    have pow_k_eq : (Nat.cast (R := ℝ) a / ↑b ^ d) ^ k = 
        (Nat.cast (R := ℝ) a ^ k / (b^k)^d) := by {
      rw [div_pow, ← Real.rpow_natCast (Nat.cast (R := ℝ) b^d), ← Real.rpow_mul,
          mul_comm d, Real.rpow_mul, Real.rpow_natCast]
      all_goals apply Nat.cast_nonneg
    }
    rw [pow_k_eq, mul_assoc, div_mul_comm, ← mul_assoc C, mul_right_comm C, 
        mul_comm C, mul_assoc _ C, ← mul_add, ← Real.div_rpow, mul_le_mul_left]
    exact hrec

    all_goals norm_cast
    . apply pow_pos
      exact ha
    . apply zero_le
    . apply pow_nonneg
      apply zero_le
  }

private theorem formula_subst {T : ℕ → ℕ} {a b n₀ : ℕ} {d C : ℝ} (k n : ℕ) (ha : a > 0)
    (hb : b > 1) (hn : n ≥ n₀ * b^k) (hC : C > 0) (hd : d ≥ 1)
    (hrec : ∀ m : ℕ, m ≥ n₀ → T m ≤ a * T (m / b) + C * (Nat.cast (R := ℝ) m)^d) :
    T n ≤ a^k * T (n / b^k) + C * GeometricSum (K := ℝ) (a / b^d) (k-1) * Nat.cast (R := ℝ) n^d := by
  induction' k with x hx
  . rw [pow_zero, Nat.zero_sub, pow_zero, Nat.div_one, 
        GeometricSum.def_zero, one_mul]
    rw [pow_zero, mul_one] at hn
    apply le_add_of_le_of_nonneg (le_refl _)
    rw [mul_one]
    apply mul_nonneg
    . linarith
    . apply Real.rpow_nonneg
      apply Nat.cast_nonneg
  . have n₀_mul_b_pow_x_le_n : n₀ * b^x ≤ n := by {
      rw [pow_succ, ← mul_assoc] at hn
      exact le_of_mul_le_of_one_le_left hn (le_of_lt hb)
    }
    have n₀_le_x_div_b_pow_x : n₀ ≤ n / b^x := by {
      apply (Nat.le_div_iff_mul_le (pow_pos (le_of_lt hb) x)).2 
      exact n₀_mul_b_pow_x_le_n
    }

    rw [Nat.add_one_sub_one]
    specialize hx n₀_mul_b_pow_x_le_n
    apply flip (formula_subst_once n ha) hx
    specialize hrec (n / b^x) n₀_le_x_div_b_pow_x
    rw [Nat.div_div_eq_div_mul, ← pow_succ] at hrec
    apply le_trans hrec
    have bound_cast_le : C * ↑(n / b ^ x) ^ d ≤ 
        C * (Nat.cast (R := ℝ) n / ↑b ^ x) ^ d := by {
      rw [mul_le_mul_left hC, ← Nat.cast_pow]
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le
      exact le_trans (le_of_lt one_pos) hd
    }
    exact le_add_of_le_add_left (le_refl _) bound_cast_le


variable {T f : ℕ → ℕ} {a b n₀ : ℕ} {d : ℝ}

lemma n₀_pos (self: MasterRecurrence T a b n₀ f d) : n₀ > 0 := lt_trans one_pos self.one_lt_n₀ 

lemma b_pos (self: MasterRecurrence T a b n₀ f d) : b > 0 := lt_trans one_pos self.one_lt_b 

private lemma add_poly (hd : d ≥ 1) (hb : b > 1) {n : ℕ} (hn : n > 1) : 
    Nat.cast (R := NNReal) (n + b)^d ≤ (2 : NNReal)^(d-1) * b^d * n^d := by
  have one_lt_n_add_b : 1 < (Nat.cast (R := ℝ) n + ↑b) := by {
    norm_cast
    exact Nat.lt_add_right b hn
  }

  rw [Nat.cast_add]
  apply le_trans (NNReal.rpow_add_le_mul_rpow_add_rpow n b hd)

  have n_pos : n > 0 := lt_trans one_pos hn
  have one_le_cast {k : ℕ} (hk_pos : k > 0) : 1 ≤ Nat.cast (R := NNReal) k := 
    by norm_cast
  rw [add_comm, mul_assoc, mul_le_mul_left (NNReal.rpow_pos two_pos)]
  apply add_le_mul
  . apply le_trans' (NNReal.rpow_le_rpow_of_exponent_le _ hd)
    . rw [NNReal.rpow_one]
      norm_cast
    . norm_cast
      linarith
  . apply le_trans' (NNReal.rpow_le_rpow_of_exponent_le _ hd)
    . rw [NNReal.rpow_one]
      norm_cast
    . norm_cast

private lemma f_of_add_b_poly {C : ℕ} (hd : d ≥ 1) (hC : C > 0) (hb : b > 1)
    (hf_poly : ∀ n > 0, f n ≤ C * Nat.cast (R := ℝ) n^d) {n : ℕ} (hn : n > 1) : 
    f (n + b) ≤ C * (2 : ℝ)^(d-1) * b^d * Nat.cast (R := ℝ) n^d := by
  specialize hf_poly (n + b) (le_add_of_le_of_nonneg (le_of_lt hn) (zero_le b))
  apply le_trans hf_poly
  have poly_le : Nat.cast (R := ℝ) (n + b) ^ d ≤ (2 : ℝ)^(d - 1) * 
      ↑b ^ d * Nat.cast (R := ℝ) n^d := by {
    apply add_poly hd hb hn
  }
  apply le_trans ((mul_le_mul_left (Nat.cast_pos.2 hC)).2 poly_le)
  rw [← mul_assoc, ← mul_assoc, mul_le_mul_right]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.2 (lt_trans one_pos hn)) d


lemma self_subst (self : MasterRecurrence T a b n₀ f d) : 
    ∃ C > 0, ∀ k > 0, MasterRecurrence 
      (fun n ↦ T (n + b)) (a^k) (b^k) (n₀ * b^k) 
      (fun n ↦ C * ⌈GeometricSum (K := ℝ) (a/b^d) (k - 1)⌉₊ * 
        ⌈Nat.cast (R := ℝ) n^d⌉₊) d := by
  obtain ⟨C₀, C₀_pos, f_poly₀⟩ := exists_pos_smul_asymp_le_iff_O.2 self.f_poly
  have ceil_poly_pos : ∀ n > 0, 0 < C₀ * ⌈Nat.cast (R := ℝ) n ^ d⌉₊ := by {
    intro n n_pos
    apply mul_pos C₀_pos
    rw [Nat.ceil_pos]
    apply Real.rpow_pos_of_pos
    norm_cast
  }
  apply Nat.bounded_above_of_asymp_le at f_poly₀
  specialize f_poly₀ ceil_poly_pos
  rcases f_poly₀ with ⟨C₁, C₁_pos, f_poly₁⟩

  have const_pos : 0 < ↑C₁ * (2 : ℝ) * C₀ * 2^(d-1) * ↑b^d := by {
    repeat' apply mul_pos <;> norm_cast
    all_goals apply Real.rpow_pos_of_pos; norm_cast
    exact self.b_pos
  }

  have const_ceil_pos : 0 < ⌈↑C₁ * (2 : ℝ) * C₀ * 2^(d-1) * ↑b^d⌉₊ := by {
    rw [Nat.ceil_pos]
    exact const_pos
  }
  use ⌈↑C₁ * (2 : ℝ) * C₀ * 2^(d-1) * ↑b^d⌉₊
  apply And.intro const_ceil_pos

  intro k hk
  exact {
    one_lt_n₀ := one_lt_mul_of_lt_of_le self.one_lt_n₀ (pow_pos self.b_pos k),
    a_pos := pow_pos self.a_pos k,
    one_lt_b := one_lt_pow₀ self.one_lt_b (zero_lt_iff.1 hk),
    one_le_d := self.one_le_d,
    f_poly := by {
      rw [O_iff_asymp_bounded_above, 
          ← exists_pos_smul_asymp_le_iff_asymp_bounded_above]
      use ⌈↑C₁ * (2 : ℝ) * ↑C₀ * 2 ^ (d - 1) * ↑b ^ d⌉₊ * 
          ⌈GeometricSum (K := ℝ) (↑a / ↑b ^ d) (k - 1)⌉₊
      apply And.intro (by {
        apply mul_pos
        . exact const_ceil_pos
        . rw [Nat.ceil_pos]
          apply GeometricSum.pos_of_pos
          apply div_pos
          . norm_cast
            exact self.a_pos
          . apply Real.rpow_pos_of_pos
            norm_cast
            exact self.b_pos
      })
      apply asymp_le_refl
    },
    T_monotone := by {
      intro x y x_le_y
      exact self.T_monotone (add_le_add x_le_y (le_refl b))
    }
    T_rec := by {
      intro n hn
      have n_pos := le_trans (mul_pos self.n₀_pos (pow_pos self.b_pos k)) hn

      generalize S_def : (fun n ↦ T (n + b)) = S
      have S_apply : ∀ (n : ℕ), T (n + b) = S n := by {
        intro n
        rw [← S_def]
      }

      have f_poly₂ : ∀ n > 0, f n ≤ ↑(C₁ * 2 * C₀) * Nat.cast (R := ℝ) n^d := by {
        intro n' n'_pos
        have one_le_n'_pow : 1 ≤ Nat.cast (R := ℝ) n' ^ d := by {
          apply Real.one_le_rpow <;> norm_cast
          linarith [self.one_le_d]
        }
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_two]

        specialize f_poly₁ n' n'_pos
        rw [← Nat.cast_le (α := ℝ), Nat.cast_mul] at f_poly₁
        rw [mul_assoc (Nat.cast (R := ℝ) C₁), mul_assoc]
        apply le_trans' ((mul_le_mul_left (by norm_cast)).2 _) f_poly₁
        simp
        rw [mul_comm 2, mul_assoc, mul_le_mul_left] <;> norm_cast
        apply Nat.ceil_le_two_mul
        linarith
      }

      have rec_apply : ∀ n ≥ n₀, S n ≤ a * S (n / b) + 
          C₁ * 2 * C₀ * (2 : ℝ)^(d-1) * b^d * Nat.cast (R := ℝ) n^d := by {
        intro n n₀_le_n 
        have n_gt_one : n > 1 := lt_of_lt_of_le self.one_lt_n₀ n₀_le_n
        have ceilDiv_apply := self.T_rec (n + b) (le_add_right n₀_le_n) 
        have ceilDiv_le : a * T ((n + b) ⌈/⌉ b) ≤ a * T ((n + b) / b + 1) := by {
          apply Nat.mul_le_mul_left
          apply self.T_monotone
          exact Nat.ceilDiv_le_div_succ self.b_pos
        }

        apply flip le_add_of_le_add_right ceilDiv_le at ceilDiv_apply
        rw [Nat.add_div self.b_pos, Nat.div_self self.b_pos] at ceilDiv_apply
        split_ifs at ceilDiv_apply with hrec_mod <;> simp at hrec_mod
        . contrapose hrec_mod
          intro hmod
          have hcontra := Nat.mod_lt n self.b_pos
          linarith
        . simp at ceilDiv_apply
          rw [add_assoc, one_add_one_eq_two] at ceilDiv_apply
          have rec_T_le_n_add_b : a * T (n / b + 2) ≤ a * T (n / b + b) := by {
            apply Nat.mul_le_mul_left
            apply self.T_monotone
            apply add_le_add_left self.one_lt_b
          }
          apply flip le_add_of_le_add_right rec_T_le_n_add_b at ceilDiv_apply
          rw [S_apply, S_apply, ← Nat.cast_le (α := ℝ), Nat.cast_add,
              Nat.cast_mul] at ceilDiv_apply
          
          have C_mul_two_pos : C₁ * 2 * C₀ > 0 := by {
            apply mul_pos <;> linarith
          }
          have f_le := f_of_add_b_poly self.one_le_d C_mul_two_pos 
            self.one_lt_b f_poly₂ n_gt_one
          push_cast at f_le
          exact le_add_of_le_add_left ceilDiv_apply f_le
      }

      suffices add_b : T (n + b) ≤ a ^ k * T (n / b ^ k + b) + 
          ((C₁ * 2 * C₀ * 2^(d-1) * b^d) * GeometricSum (K := ℝ) (↑a/↑b^d) 
          (k-1)) * Nat.cast (R := ℝ) n^d by {
        rw [← Nat.cast_le (α := ℝ)]
        push_cast
        apply le_trans add_b (add_le_add _ _)
        . rw [mul_le_mul_left, Nat.cast_le, ← Nat.floorDiv_eq_div]
          apply self.T_monotone
          apply add_le_add_right floorDiv_le_ceilDiv
          norm_cast
          exact pow_pos self.a_pos k
        . apply mul_le_mul
          . apply mul_le_mul
            . apply Nat.le_ceil
            . apply Nat.le_ceil
            . apply le_of_lt
              apply GeometricSum.pos_of_pos
              apply div_pos
              . norm_cast
                exact self.a_pos
              . apply Real.rpow_pos_of_pos
                norm_cast
                exact self.b_pos
            . apply Nat.cast_nonneg
          . apply Nat.le_ceil
          . apply Real.rpow_nonneg
            norm_cast
            linarith
          . apply mul_nonneg 
            all_goals apply Nat.cast_nonneg
      }

      rw [S_apply, S_apply]
      exact formula_subst k n self.a_pos self.one_lt_b hn const_pos 
                          self.one_le_d rec_apply
    }
  }

lemma O_of_O_poly (self : MasterRecurrence T a b n₀ f d) : 
    T ∈ O ℕ fun n ↦ T ((n₀ + 1) * b + 1) * ⌈Nat.cast (R := ℝ) n ^ 
      (Real.logb b a)⌉₊ + ⌈GeometricSum (K := ℝ) (↑a / ↑b^d) 
      (⌈Real.logb b n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ := by
  obtain ⟨C, C_pos, subst_master⟩ := self.self_subst
  use C
  apply And.intro C_pos

  use n₀ * b
  intro n hn
  simp
  have n_pos : n > 0 := by {
    apply lt_of_le_of_lt' hn
    exact mul_pos self.n₀_pos self.b_pos
  }
  have one_lt_n : n > 1 := by {
    apply lt_of_le_of_lt' hn
    apply one_lt_mul <;> linarith [self.one_lt_b, self.one_lt_n₀]
  }
  have one_le_cast_n_div_n₀ : 1 ≤ Nat.cast (R := ℝ) n / ↑n₀ := by {
    rw [one_le_div] <;> norm_cast
    . apply le_of_mul_le_of_one_le hn <;> linarith [self.one_lt_b]
    . exact self.n₀_pos
  }

  generalize k_def : ⌊Real.logb b (n / n₀)⌋₊ = k
  have k_pos : 0 < k := by {
    rw [← k_def]
    rw [Nat.floor_pos, ← Real.logb_self_eq_one, Real.logb_le_logb]
    apply le_trans' Nat.cast_div_le
    all_goals norm_cast
    rw [Nat.le_div_iff_mul_le, mul_comm]
    all_goals linarith [self.one_lt_b, self.one_lt_n₀]
  }

  specialize subst_master k k_pos
  have subst_rec := subst_master.T_rec n (by {
    rw [← k_def, ge_iff_le, ← Nat.cast_le (α := ℝ), Nat.cast_mul, mul_comm]
    apply mul_le_of_le_div₀ <;> norm_cast
    repeat apply zero_le
    push_cast
    rw [← Real.rpow_natCast]
    apply le_trans ((Real.rpow_le_rpow_left_iff _).2 (Nat.floor_le _))
    all_goals norm_cast
    . rw [Real.rpow_logb] <;> norm_cast <;> linarith [self.one_lt_b]
    . linarith [self.one_lt_b]
    . apply Real.logb_nonneg
      . norm_cast
        linarith [self.one_lt_b]
      . rw [one_le_div] <;> norm_cast
        apply le_of_mul_le_of_one_le_left (b := b)
        all_goals linarith [self.one_lt_n₀, self.one_lt_b]
  })
  have T_of_add_b : T n ≤ T (n + b) := 
    self.T_monotone (le_add_right (le_refl n))

  apply le_trans T_of_add_b
  apply le_trans subst_rec
  rw [mul_add]
  apply add_le_add
  . rw [mul_comm, ← mul_assoc]
    apply mul_le_mul
    . apply le_trans' (le_mul_of_one_le_left _ _)
      apply self.T_monotone
      rw [← k_def, add_mul, one_mul, add_assoc, add_comm b, ← add_assoc]
      apply add_le_add_right
      apply le_trans (Nat.ceilDiv_le_div_succ (pow_pos self.b_pos _))
      apply add_le_add_right
      rw [← Nat.cast_le (α := ℝ), Real.logb_div]
      apply le_trans Nat.cast_div_le
      push_cast
      rw [← Real.rpow_logb (b := b) (x := n), ← Real.rpow_natCast, 
          ← Real.rpow_sub, Real.rpow_logb, ← Real.rpow_one b, 
          ← Real.rpow_logb (b := b) (x := n₀), ← Real.rpow_add, 
          Real.rpow_one b, Real.rpow_logb, Real.rpow_le_rpow_left_iff]
      have le_log_sub : Real.logb b n - Real.logb b n₀ -1 ≤ 
                        ⌊Real.logb b n - Real.logb b n₀⌋₊ := by {
        rw [sub_le_iff_le_add', add_comm]
        apply le_trans (Nat.le_ceil _)
        norm_cast
        apply Nat.ceil_le_floor_add_one
      }
      apply le_trans (sub_le_sub_left le_log_sub _)
      all_goals norm_cast
      all_goals linarith [self.one_lt_b, self.one_lt_n₀]
    . rw [← k_def, ← Nat.cast_le (α := ℝ), Nat.cast_pow, ← Real.rpow_natCast]
      apply le_trans' (Nat.le_ceil _)
      rw [← Real.rpow_logb (b := b) (x := Nat.cast (R := ℝ) n),
          ← Real.rpow_mul, mul_comm, Real.rpow_mul, Real.rpow_logb, 
          Real.rpow_logb]
      apply Real.rpow_le_rpow_of_exponent_le
      case _ : Nat.cast (R := ℝ) ⌊_⌋₊ ≤ _ => (
        apply le_trans (Nat.floor_le (Real.logb_nonneg _ _))
        rw [Real.logb_le_logb]
        apply div_le_self
        all_goals norm_cast
        all_goals linarith [self.one_lt_n₀, self.one_lt_b]
      )
      all_goals norm_cast
      all_goals linarith [self.a_pos, self.one_lt_b]
    all_goals apply zero_le
  . rw [mul_assoc, mul_le_mul_left C_pos, mul_le_mul_right]
    . apply Nat.ceil_le_ceil
      apply GeometricSum.le_of_pos_of_le
      . apply div_pos
        . exact Nat.cast_pos.2 self.a_pos
        . exact Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
      . simp
        rw [← k_def, Nat.sub_add_cancel]
        . apply le_trans (Nat.floor_le_floor (b := Real.logb b n) _)
          . apply Nat.floor_le_ceil
          . rw [Real.logb_le_logb] <;> norm_cast
            apply div_le_self <;> norm_cast
            all_goals linarith [self.one_lt_b, self.one_lt_n₀]
        . apply Nat.ceil_pos.2
          apply Real.logb_pos <;> norm_cast
          all_goals linarith [self.one_lt_b, self.one_lt_n₀]
    . rw [Nat.ceil_pos]
      apply Real.rpow_pos_of_pos
      assumption_mod_cast

theorem O_of_O_poly_of_lt (self : MasterRecurrence T a b n₀ f d)
    (hlt : a < Nat.cast (R := ℝ) b^d) : 
    T ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊ := by
  apply O_trans self.O_of_O_poly
  apply O_add
  . if hT : T ((n₀ + 1) * b + 1) > 0 then {
      apply O_pos_smul hT
      apply O_of_asymp_le
      apply asymp_le_of_le_of_forall_ge (N := 2)

      intro n hn
      apply Nat.ceil_le_ceil
      rw [Real.rpow_le_rpow_left_iff]
      rw [Real.logb_le_iff_le_rpow]
      all_goals norm_cast
      all_goals linarith [self.a_pos, self.one_lt_b]
    }
    else {
      simp at hT
      rw [hT]
      simp

      apply O_of_asymp_le
      apply asymp_le_of_le_of_forall_ge (N := 0)
      intros
      apply Nat.cast_nonneg
    }
  . have b_pow_d_pos : Nat.cast (R := ℝ) b^d > 0 :=
      Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
    have indep_const_pos : 0 < ⌈1 / (1 - Nat.cast (R := ℝ) a / ↑b^d)⌉₊ := by {
      rw [Nat.ceil_pos]
      apply div_pos one_pos
      simp
      rw [div_lt_one] <;> assumption
    }

    apply flip O_trans
      (O_pos_smul indep_const_pos O_refl)
    apply O_of_asymp_le
    apply asymp_le_of_le_of_forall_ge (N := 0)
    intro n hn
    apply mul_le_mul <;> try linarith
    apply Nat.ceil_le_ceil
    apply GeometricSum.le_of_base_pos_lt_one
    apply div_pos <;> norm_cast
    . exact self.a_pos
    . rw [div_lt_one]
      . exact hlt
      . apply Real.rpow_pos_of_pos
        norm_cast
        exact self.b_pos

theorem O_of_O_poly_of_eq (self : MasterRecurrence T a b n₀ f d)
    (heq : ↑a = Nat.cast (R := ℝ) b^d) : 
    T ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d * Real.logb b n⌉₊ := by
  apply O_trans self.O_of_O_poly
  apply O_add
  . if hT : T ((n₀ + 1) * b + 1) > 0 then {
      apply O_pos_smul hT
      apply O_of_asymp_le
      apply asymp_le_of_le_of_forall_ge (N := b)

      intro n hn
      apply Nat.ceil_le_ceil
      have logb_a_eq_d : Real.logb b a = d := by {
        rw [heq, Real.logb_rpow] <;> norm_cast <;> linarith [self.one_lt_b]
      }
      have one_le_logb_n : 1 ≤ Real.logb b n := by {
        rw [← Real.logb_self_eq_one (b := b), Real.logb_le_logb]
        all_goals norm_cast
        all_goals linarith [self.one_lt_b]
      }
      rw [logb_a_eq_d]
      apply le_mul_of_one_le_right
      apply Real.rpow_nonneg
      apply Nat.cast_nonneg
      all_goals norm_cast
    }
    else {
      simp at hT
      rw [hT]
      simp

      apply O_of_asymp_le
      apply asymp_le_of_le_of_forall_ge (N := 0)
      intros
      apply Nat.cast_nonneg
    }
  . have b_pow_d_pos : Nat.cast (R := ℝ) b^d > 0 :=
      Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
    have a_div_b_pow_eq_one : Nat.cast (R := ℝ) a / ↑b^d = 1 := by {
      rw [div_eq_one_iff_eq] <;> linarith
    }
    have geom_indep : ∀ n ≥ b + 1, ⌈GeometricSum (K := ℝ) (↑a / ↑b ^ d) 
        (⌈Real.logb ↑b ↑n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n ^ d⌉₊ ≤ 
        6 * ⌈Nat.cast (R := ℝ) n^d * Real.logb b n⌉₊ := by {
      intro n hn
      rw [a_div_b_pow_eq_one, GeometricSum.base_eq_one]

      have one_lt_n_pow_d : 1 < Nat.cast (R := ℝ) n^d := by {
        apply Real.one_lt_rpow <;> norm_cast 
        all_goals linarith [self.one_lt_b, self.one_le_d]
      }
      have one_lt_logb_n : 1 < Real.logb b n := by {
        rw [← Real.logb_self_eq_one (b := b)]
        apply Real.logb_lt_logb
        all_goals norm_cast
        all_goals linarith [self.one_lt_b]
      }
      have left_pos : 0 < 6 * Real.logb b n := by {
        apply mul_pos <;> linarith
      }

      /- destroy the outer left ceiling -/
      apply le_trans ((mul_le_mul_right _).2 (Nat.ceil_le_floor_add_one _))
      rw [Nat.cast_sub]
      simp
    
      /- add a log and destroy the inner left ceiling -/
      rw [← Nat.cast_le (α := ℝ)]
      push_cast
      apply le_trans ((mul_le_mul_right _).2 (add_le_add_left 
        (c := Real.logb b n) _ _))
      apply le_trans ((mul_le_mul_right _).2 (add_le_add_right 
        (Nat.ceil_le_two_mul _) _))

      /- deal with right ceiling and right hand side -/
      apply le_trans ((mul_le_mul_left _).2 (Nat.ceil_le_two_mul _))
      apply le_trans' ((mul_le_mul_left _).2 (Nat.le_ceil _))
      apply le_of_eq
      ring

      /- prove residual goals -/
      all_goals norm_cast
      all_goals try rw [Nat.ceil_pos]
      case _ : 1 ≤ Nat.clog b n => (
        apply Nat.clog_pos <;> linarith [self.one_lt_b]
      )
      all_goals linarith
    }

    apply O_trans (O_of_asymp_le (asymp_le_of_le_of_forall_ge geom_indep))
    apply O_pos_smul <;> simp

theorem O_of_O_poly_of_gt (self : MasterRecurrence T a b n₀ f d)
    (hgt : ↑a > Nat.cast (R := ℝ) b^d) : 
    T ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^Real.logb b a⌉₊ := by
  apply O_trans self.O_of_O_poly
  apply O_add
  . apply flip O_trans (O_pos_smul
      (c := T ((n₀ + 1) * b + 1) + 1) 
      (g := fun n ↦ ⌈Nat.cast (R := ℝ) n^Real.logb ↑b ↑a⌉₊) (by linarith)
      O_refl)
    apply O_of_asymp_le
    apply asymp_le_of_le_of_forall_ge (N := 1)
    intro n hn
    rw [smul_eq_mul, mul_le_mul_right]
    . linarith
    . rw [Nat.ceil_pos]
      apply Real.rpow_pos_of_pos
      norm_cast
  . have one_lt_b_pow_pos : 1 < Nat.cast (R := ℝ) b^d := by {
        rw [← Real.rpow_zero b]
        apply Real.rpow_lt_rpow_of_exponent_lt <;> norm_cast
        all_goals linarith [self.one_lt_b, self.one_le_d]
    }
    have one_lt_a_div_b_pow : 1 < Nat.cast (R := ℝ) a / ↑b^d := by {
      rw [one_lt_div] <;> linarith
    }
    have logb_a_pos : 0 < Real.logb b a := by {
      apply Real.logb_pos
      . norm_cast
        linarith [self.one_lt_b]
      . linarith
    }
    have d_lt_logb_a : d < Real.logb b a := by {
      rw [Real.lt_logb_iff_rpow_lt] <;> norm_cast
      all_goals linarith [self.one_lt_b, self.a_pos]
    }

    have pow_log_le : ∀ n ≥ b + 1, 
        (Nat.cast (R := ℝ) a / ↑b^d) ^ ↑⌈Real.logb ↑b ↑n⌉₊ ≤ 
        ↑a / ↑b^d * (↑n ^ Real.logb b a) / (↑n^d) := by {
      intro n hn
      apply le_trans (pow_le_pow_right₀ _ (Nat.ceil_le_floor_add_one _))
      rw [← Real.rpow_natCast]
      push_cast
      apply le_trans (Real.rpow_le_rpow_of_exponent_le _ 
        (add_le_add_right (Nat.floor_le _) _))
      rw [Real.rpow_add, Real.rpow_one, 
          ← Real.rpow_logb (b := b) (x := Nat.cast (R := ℝ) a / ↑b^d), 
          ← Real.rpow_mul, mul_comm (Real.logb _ _), Real.rpow_mul, 
          Real.rpow_logb, Real.rpow_logb, Real.logb_div, Real.logb_rpow, 
          Real.rpow_sub]
      apply le_of_eq
      ring

      case _ : 0 ≤ Real.logb b n => (
        apply Real.logb_nonneg <;> norm_cast <;> linarith [self.one_lt_b]
      )
      all_goals norm_cast
      all_goals linarith [self.a_pos, self.one_lt_b]
    }
    have le_n_pow_log : ∀ n ≥ b + 1, ⌈GeometricSum (Nat.cast (R := ℝ) 
        ↑a / ↑b ^ d) (⌈Real.logb ↑b ↑n⌉₊ - 1)⌉₊ * ⌈Nat.cast (R := ℝ) n^d⌉₊ ≤ 
        (⌈(2 - 2 / (Nat.cast (R := ℝ) a / ↑b ^ d - 1))⌉₊ + 
        ⌈2 / (↑a / ↑b ^ d - 1) * (Nat.cast (R := ℝ) a / ↑b^d)⌉₊) * 
        ⌈Nat.cast (R := ℝ) n^Real.logb b a⌉₊ := by {
      intro n hn
      rw [GeometricSum.base_ne_one, Nat.sub_one_add_one]

      have one_lt_logb_n : 1 < Real.logb b n := by {
        rw [← Real.logb_self_eq_one (b := b)]
        apply Real.logb_lt_logb 
        all_goals norm_cast 
        all_goals linarith [self.one_lt_b]
      }
      have one_lt_n_pow : 1 < Nat.cast (R := ℝ) n ^ d := by {
        apply Real.one_lt_rpow <;> norm_cast 
        all_goals linarith [self.one_lt_b, self.one_le_d]
      }

      have left_eq1 : ((Nat.cast (R := ℝ) a / ↑b ^ d) ^ 
        ⌈Real.logb ↑b ↑n⌉₊ - 1) / (↑a / ↑b ^ d - 1) = 
        1 / (↑a / ↑b^d - 1) * (↑a / ↑b^d) ^ ⌈Real.logb b n⌉₊ - 
        1 / (Nat.cast (R := ℝ) a / ↑b^d - 1) := by ring

      /- destroy ceilings on the left hard side -/
      rw [left_eq1]
      apply le_trans ((mul_le_mul_right _).2 (Nat.ceil_le_floor_add_one _))
      rw [← Nat.cast_le (α := ℝ)]
      push_cast
      apply le_trans ((mul_le_mul_left _).2 (Nat.ceil_le_two_mul _))
      apply le_trans ((mul_le_mul_right _).2 (add_le_add_right
        (Nat.floor_le _) 1))

      have left_eq2 : (1 / (Nat.cast (R := ℝ) a / ↑b ^ d - 1) * (↑a / ↑b ^ d) ^ 
        ⌈Real.logb ↑b ↑n⌉₊ - 1 / (↑a / ↑b ^ d - 1) + 1) * (2 * ↑n ^ d) =
        (2 - 2 / (↑a / ↑b ^ d - 1)) * ↑n ^ d + 2 / (↑a / ↑b ^ d - 1) *
        (↑a / ↑b ^ d) ^ ⌈Real.logb ↑b ↑n⌉₊ * ↑n ^ d := by ring

      rw [left_eq2, add_mul]
      apply add_le_add
      . apply mul_le_mul
        . apply Nat.le_ceil
        . apply le_trans' (Nat.le_ceil _)
          apply Real.rpow_le_rpow_of_exponent_le <;> norm_cast <;> linarith
        . linarith
        . apply Nat.cast_nonneg
      . apply le_trans' (mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) _ _)
        . rw [mul_assoc, mul_assoc, mul_le_mul_left]
          . apply le_trans ((mul_le_mul_right _).2 (pow_log_le n hn))
            rw [div_mul_cancel₀]
            all_goals linarith
          . apply div_pos <;> linarith
        . apply Real.rpow_nonneg
          apply Nat.cast_nonneg
        . apply Nat.cast_nonneg

      case _ : 0 ≤ 1 / (Nat.cast (R := ℝ) a / ↑b ^ d - 1) * 
          (↑a / ↑b ^ d) ^ ⌈Real.logb ↑b ↑n⌉₊ - 1 / (↑a / ↑b ^ d - 1) => (
        rw [sub_nonneg]
        apply le_mul_of_one_le_right
        . apply div_nonneg <;> linarith
        . rw [← pow_zero (a := (Nat.cast (R := ℝ) a / ↑b ^ d))]
          apply pow_le_pow_right₀ <;> linarith
      )

      repeat case _ : 0 < ⌈Nat.cast (R := ℝ) n ^ d⌉₊ => (
        rw [Nat.ceil_pos]
        apply Real.rpow_pos_of_pos
        norm_cast
        linarith
      )
      case _ : ⌈Real.logb ↑b ↑n⌉₊ ≠ 0 => (
        apply ne_of_gt
        rw [Nat.ceil_pos]
        apply Real.logb_pos <;> norm_cast <;> linarith [self.one_lt_b]
      )
      all_goals linarith
    }

    apply asymp_le_of_le_of_forall_ge at le_n_pow_log
    apply O_trans (O_of_asymp_le le_n_pow_log)
    apply flip O_pos_smul O_refl
    apply Nat.add_pos_right
    rw [Nat.ceil_pos]
    apply mul_pos
    . apply mul_pos
      . linarith
      . rw [inv_pos]
        linarith
    . linarith


end MasterRecurrence


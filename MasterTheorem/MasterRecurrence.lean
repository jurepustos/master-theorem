import Mathlib

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv


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
  f_poly : Nat.cast ∘ f ∈ O ℝ fun n ↦ Nat.cast (R := ℝ) n^d
  /- polynomial degree is at least 1 -/
  one_le_d : 1 ≤ d
  /-T is monotone -/
  T_monotone : Monotone T
  /- The recurrence formula -/
  T_rec : ∀ n ≥ n₀, T n ≤ a * T (n ⌈/⌉ b) + f n


namespace MasterRecurrence


private lemma formula_subst_once {T : ℕ → ℕ} {a b k n : ℕ} {d C : ℝ}
    (ha : a > 0) (hrec : T (n / b^k) ≤ a * T (n / b^(k+1)) + 
                                       C * (n / Nat.cast (R := ℝ) b^k)^d)
    (hformula : T n ≤ a^k * T (n / b^k) + 
                      C * GeometricSum (K := ℝ) (↑a / ↑b^d) (k-1) * 
                      Nat.cast (R := ℝ) n^d) :
    T n ≤ a^(k+1) * T (n / b^(k+1)) + 
          C * GeometricSum (K := ℝ) (↑a / ↑b^d) k * 
          Nat.cast (R := ℝ) n^d := by
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
        (Nat.cast (R := ℝ) a ^ k / (↑b^k)^d) := by {
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

private theorem formula_subst {T k : ℕ → ℕ} {a b n₀ : ℕ} {d C : ℝ}
    (ha : a > 0) (hb : b > 1) (hC : C > 0) (hd : d ≥ 1)
    (hrec : ∀ n ≥ n₀, T n ≤ a * T (n / b) + 
                            C * (Nat.cast (R := ℝ) n)^d) :
    ∀ {n : ℕ}, n ≥ n₀ * b^k n → 
      T n ≤ a^k n * T (n / b^k n) + 
            C * GeometricSum (K := ℝ) (↑a / ↑b^d) (k n - 1) * 
            Nat.cast (R := ℝ) n^d := by
  intro n
  induction' k n with x hx
  . intros
    simp
    apply mul_nonneg
    . linarith
    . apply Real.rpow_nonneg
      apply Nat.cast_nonneg
  . intro hn
    have n₀_mul_b_pow_x_le_n : n₀ * b^x ≤ n := by {
      rw [pow_succ, ← mul_assoc] at hn
      exact le_of_mul_le_of_one_le_left hn (le_of_lt hb)
    }
    have n₀_le_x_div_b_pow_x : n₀ ≤ n / b^x := by {
      rw [Nat.le_div_iff_mul_le (pow_pos (le_of_lt hb) x)]
      exact n₀_mul_b_pow_x_le_n
    }

    rw [Nat.add_one_sub_one]
    specialize hx n₀_mul_b_pow_x_le_n
    apply flip (formula_subst_once ha) hx
    specialize hrec (n / b^x) n₀_le_x_div_b_pow_x
    rw [Nat.div_div_eq_div_mul, ← pow_succ] at hrec
    apply le_trans hrec
    apply le_add_of_le_add_left (le_refl _)
    rw [mul_le_mul_left hC, ← Nat.cast_pow]
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le
    linarith


private lemma formula_subst_once' {T : ℕ → ℕ} {a b k n : ℕ} {d C : ℝ}
    (ha : a > 0) (hrec : T (n / b^k) ≥ a * T (n / b^(k+1)) + 
                                       C * (n / Nat.cast (R := ℝ) b^k)^d)
    (hformula : T n ≥ a^k * T (n / b^k) + C * GeometricSum (K := ℝ)
      (↑a / ↑b^d) (k-1) * Nat.cast (R := ℝ) n^d) :
    T n ≥ a^(k+1) * T (n / b^(k+1)) + 
          C * GeometricSum (K := ℝ) (↑a / ↑b^d) k * 
          Nat.cast (R := ℝ) n^d := by
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

    apply add_le_of_add_le_right hformula
    have pow_k_eq : (Nat.cast (R := ℝ) a / ↑b ^ d) ^ k = 
        (Nat.cast (R := ℝ) a ^ k / (↑b^k)^d) := by {
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


private theorem formula_subst' {T : ℕ → ℕ} {a b n₀ : ℕ} {d C : ℝ} 
    (ha : a > 0) (hb : b > 1) (hn₀ : 1 < n₀) (hC : C > 0) (hd : d ≥ 1)
    (hrec : ∀ n ≥ n₀, T n ≥ a * T (n / b) + 
                            C * (Nat.cast (R := ℝ) n)^d) :
    ∀ {k : ℕ → ℕ}, ∀ {n : ℕ}, k n > 0 → n ≥ (n₀ ⊔ b)^k n → 
      T n ≥ a^k n * T (n / b^k n) +
            C / 2^d * GeometricSum (K := ℝ) (↑a / ↑b^d) (k n - 1) * 
            Nat.cast (R := ℝ) n^d := by
  have const_pos : 0 < C / 2^d := by {
    apply div_pos hC
    apply Real.rpow_pos_of_pos
    exact two_pos
  }
  intro k n hk hn

  generalize k'_def : k n - 1 = k'
  have k_ne_zero : k n ≠ 0 := by linarith
  rw [← Nat.sub_one_add_one k_ne_zero, k'_def] at hn
  rw [← Nat.sub_one_add_one k_ne_zero, k'_def]
  clear k_ne_zero k'_def

  induction' k' with x hx
  . simp
    simp at hn
    obtain ⟨n_ge_n₀, n_ge_b⟩ := hn
    specialize hrec n n_ge_n₀

    apply le_trans' hrec
    apply add_le_add_left
    rw [mul_le_mul_right]
    . apply div_le_self
      . linarith
      . apply Real.one_le_rpow <;> linarith
    . apply Real.rpow_pos_of_pos
      norm_cast
      linarith
  . have b_pos : b > 0 := by linarith
    have b_pow_pos : b^(x+1) > 0 := pow_pos b_pos (x+1)

    have n_ge_max_ind : n ≥ (n₀ ⊔ b) ^ (x + 1) := by {
      apply le_trans' hn
      apply pow_le_pow_right₀ <;> linarith [le_max_left n₀ b]
    }
    have b_pow_le_max_pow : b^(x+1) ≤ (n₀ ⊔ b) ^ (x + 1) := by {
      apply pow_le_pow_left'
      apply le_max_right
    }
    have cast_n_div_b_pow_nonneg : 0 ≤ Nat.cast (R := ℝ) n / ↑b ^ (x+1) := by {
      apply div_nonneg <;> norm_cast <;> linarith
    }

    specialize hx n_ge_max_ind
    apply flip (formula_subst_once' ha) hx
    specialize hrec (n / b^(x+1)) (by {
      apply le_trans (le_max_left n₀ b)
      rw [Nat.le_div_iff_mul_le]
      . apply le_trans ((mul_le_mul_left _).2 b_pow_le_max_pow)
        . rw [mul_comm, ← pow_succ]
          exact hn
        . apply lt_max_of_lt_left
          linarith
      . apply pow_pos
        linarith
    })

    apply le_trans' hrec
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
    apply add_le_add_left
    rw [div_eq_mul_inv, mul_assoc, ← Real.inv_rpow, mul_le_mul_left, 
        ← Real.mul_rpow]
    apply Real.rpow_le_rpow
    . apply mul_nonneg <;> linarith
    . rw [← Nat.ceil_le, Nat.le_div_iff_mul_le b_pow_pos, 
          ← Nat.cast_le (α := ℝ), Nat.cast_mul]
      apply le_trans ((mul_le_mul_right _).2 (Nat.ceil_le_two_mul _))
      all_goals norm_cast
      . rw [← mul_assoc, mul_assoc, div_mul_cancel₀]
        . linarith
        . norm_cast
          linarith
      . apply le_mul_of_one_le_right
        . linarith
        . rw [one_le_div₀] <;> norm_cast
          linarith [pow_le_pow_left' (le_max_right n₀ b) (x + 1)]
    all_goals linarith


variable {T f : ℕ → ℕ} {a b n₀ : ℕ} {d : ℝ}

lemma n₀_pos (self: MasterRecurrence T a b n₀ f d) : n₀ > 0 := 
  lt_trans one_pos self.one_lt_n₀ 

lemma b_pos (self: MasterRecurrence T a b n₀ f d) : b > 0 := 
  lt_trans one_pos self.one_lt_b 

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

private lemma f_of_add_b_poly {C d : ℝ} {N b : ℕ} 
    (hd : d ≥ 1) (hC : C > 0) (hb : b > 1) 
    (hf_poly : ∀ n ≥ N, ↑(f n) ≤ C * Nat.cast (R := ℝ) n^d) (hN : N > 1) : 
    ∀ n ≥ N, f (n + b) ≤ C * (2 : ℝ)^(d-1) * b^d * Nat.cast (R := ℝ) n^d := by
  intro n hn
  specialize hf_poly (n + b) (le_add_of_le_of_nonneg hn (zero_le b))
  apply le_trans hf_poly
  have poly_le : Nat.cast (R := ℝ) (n + b) ^ d ≤ (2 : ℝ)^(d - 1) * 
                ↑b ^ d * Nat.cast (R := ℝ) n^d := by {
    apply add_poly hd hb
    linarith
  }
  apply le_trans ((mul_le_mul_left hC).2 poly_le)
  rw [← mul_assoc, ← mul_assoc, mul_le_mul_right]
  apply Real.rpow_pos_of_pos
  norm_cast
  linarith


private lemma k_subst (self : MasterRecurrence T a b n₀ f d) : 
    ∃ C > 0, ∃ N ≥ n₀, ∀ {k : ℕ → ℕ}, ∀ {n : ℕ}, n ≥ N * b^k n →
      ↑(T (n + b)) ≤ ↑a^k n * ↑(T (n / b^k n + b)) + 
                     C * GeometricSum (K := ℝ) (a/b^d) (k n - 1) * ↑n^d := by
  obtain ⟨C, C_pos, N, f_poly₁⟩ := exists_pos_smul_asymp_le_iff_O.2 self.f_poly

  have const_pos : 0 < C * 2^(d-1) * ↑b^d := by {
    repeat' apply mul_pos <;> norm_cast
    all_goals apply Real.rpow_pos_of_pos; norm_cast
    exact self.b_pos
  }

  use C * 2^(d-1) * ↑b^d
  apply And.intro const_pos

  generalize M_def : N ⊔ n₀ = M
  have M_ge_N : M ≥ N := by {
    rw [← M_def]
    apply le_max_left
  }
  have M_ge_n₀ : M ≥ n₀ := by {
    rw [← M_def]
    apply le_max_right
  }
  have one_lt_M : 1 < M := by linarith [self.one_lt_n₀]

  use M
  apply And.intro M_ge_n₀

  have f_poly₂ : ∀ n ≥ M, f n ≤ C * Nat.cast (R := ℝ) n^d := by {
    intro n n_ge
    have one_le_n_pow : 1 ≤ Nat.cast (R := ℝ) n^d := by {
      apply Real.one_le_rpow <;> norm_cast
      all_goals linarith [self.one_le_d]
    }

    specialize f_poly₁ n (by linarith)
    simp at f_poly₁
    linarith
  }

  generalize S_def : (fun n ↦ T (n + b)) = S
  have S_apply (n : ℕ) : T (n + b) = S n := by rw [← S_def]

  have rec_apply : ∀ n ≥ M, S n ≤ a * S (n / b) + 
                                  C * (2 : ℝ)^(d-1) * b^d * 
                                  Nat.cast (R := ℝ) n^d := by {
    intro n n_ge_M
    have n_gt_one : n > 1 := by linarith
    have ceilDiv_apply := self.T_rec (n + b) (le_add_right (by linarith))
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
      
      have C_mul_two_pos : 2 * C > 0 := by {
        apply mul_pos <;> linarith
      }
      have f_le := f_of_add_b_poly self.one_le_d C_pos 
                    self.one_lt_b f_poly₂ (by linarith) n n_ge_M
      push_cast at f_le
      exact le_add_of_le_add_left ceilDiv_apply f_le
  }

  intro k n hn
  rw [S_apply, S_apply]
  exact formula_subst self.a_pos self.one_lt_b const_pos 
                      self.one_le_d rec_apply hn

private lemma k_subst' (self : MasterRecurrence T a b n₀ f d) {g : ℕ → ℕ}
    (hg_poly : Nat.cast ∘ g ∈ Ω ℝ fun n ↦ Nat.cast (R := ℝ) n^d)
    (hrec : ∀ n ≥ n₀, T n ≥ a * T (n / b) + g n) :
    ∃ C > 0, ∃ N ≥ n₀, ∀ {k : ℕ → ℕ}, ∀ {n : ℕ}, k n > 0 → n ≥ (N ⊔ b)^k n →
    ↑(T n) ≥ ↑a^k n * ↑(T (n / b^k n)) + 
             C * GeometricSum (K := ℝ) (↑a / ↑b^d) (k n - 1) * n^d := by
  obtain ⟨C, C_pos, N, g_poly₁⟩ := exists_pos_smul_asymp_ge_iff_Ω.2 hg_poly

  generalize M_def : N ⊔ n₀ = M
  have M_ge_N : M ≥ N := by {
    rw [← M_def]
    apply le_max_left
  }
  have M_ge_n₀ : M ≥ n₀ := by {
    rw [← M_def]
    apply le_max_right
  }
  have one_lt_M : 1 < M := by linarith [self.one_lt_n₀]

  have g_poly₂ : ∀ n ≥ M, g n ≥ ↑C * Nat.cast (R := ℝ) n^d := by {
    intro n n_ge
    apply g_poly₁ n
    linarith
  }

  have rec_apply : ∀ n ≥ M, T n ≥ ↑a * ↑(T (n / b)) + 
                                  ↑C * Nat.cast (R := ℝ) n^d := by {
    intro n hn
    apply flip add_le_of_add_le_left (g_poly₂ n hn)
    norm_cast
    apply hrec n
    linarith
  }

  use C / 2^d
  apply And.intro (by {
    apply div_pos C_pos
    apply Real.rpow_pos_of_pos
    exact two_pos
  })

  use M
  apply And.intro M_ge_n₀
  intro k n hk hn
  have subst_rec := formula_subst' self.a_pos self.one_lt_b one_lt_M C_pos 
                                   self.one_le_d rec_apply hk hn
  linarith


private lemma O_rec (self : MasterRecurrence T a b n₀ f d) : 
    Nat.cast ∘ T ∈ O ℝ fun n ↦ Nat.cast (R := ℝ) n ^ (Real.logb b a) +
                    GeometricSum (K := ℝ) (↑a / ↑b^d) (⌊Real.logb b n⌋₊ - 1) *
                    Nat.cast (R := ℝ) n^d := by
  obtain ⟨C, C_pos, N, N_ge, subst_master⟩ := self.k_subst

  have T_of_add_b_asymp_le : AsympLE (Nat.cast (R := ℝ) ∘ T) 
                                     (fun n ↦ Nat.cast (T (n + b))) := by {
    use 0
    intro n hn
    simp
    apply self.T_monotone
    apply le_add_right
    exact le_refl n
  }

  apply O_trans (O_of_asymp_le T_of_add_b_asymp_le)

  have N_le_mul_b : N ≤ N * b := by {
    apply le_mul_of_one_le_right <;> linarith [self.one_lt_b]
  }
  have n_ge_N {n : ℕ} (hn : n ≥ N * b) : n ≥ N := by linarith
  have one_le_cast_n_div_N {n : ℕ} (hn : n ≥ N) : 
      1 ≤ Nat.cast (R := ℝ) n / ↑N := by {
    rw [one_le_div] <;> norm_cast
    linarith [self.one_lt_n₀]
  }
  have cast_n_div_N_pos {n : ℕ} (hn : n ≥ N) : 
      0 < Nat.cast (R := ℝ) n / ↑N := by {
    apply one_le_cast_n_div_N at hn
    linarith
  }

  generalize k_def : (fun n : ℕ ↦ ⌊Real.logb ↑b (↑n / ↑N)⌋₊) = k
  have k_pos {n : ℕ} (hn : n ≥ N * b) : 0 < k n := by {
    rw [← k_def]
    rw [Nat.floor_pos, ← Real.logb_self_eq_one, Real.logb_le_logb]
    apply le_trans' Nat.cast_div_le
    all_goals norm_cast
    rw [Nat.le_div_iff_mul_le, mul_comm]

    case _ : 0 < (Nat.cast (R := ℝ)) n / ↑N := cast_n_div_N_pos (n_ge_N hn)
    all_goals linarith [self.one_lt_b, self.one_lt_n₀]
  }

  have subst_rec : ∀ n ≥ N * b, 
      ↑(T (n + b)) ≤ ↑a^(k n) * ↑(T (n / b ^ (k n) + b)) + 
                  C * GeometricSum (K := ℝ) (↑a / ↑b ^ d) (k n - 1) * 
                  n ^ d := by {
    intro n hn

    apply subst_master
    rw [← k_def, ge_iff_le, ← Nat.cast_le (α := ℝ), Nat.cast_mul, mul_comm]
    apply mul_le_of_le_div₀ <;> norm_cast
    repeat apply zero_le
    push_cast
    rw [← Real.rpow_natCast]
    apply le_trans ((Real.rpow_le_rpow_left_iff _).2 (Nat.floor_le _))
    all_goals norm_cast
    . rw [Real.rpow_logb] <;> norm_cast
      case _ : 0 < Nat.cast (R := ℝ) n / ↑N => (
        apply div_pos <;> norm_cast <;> linarith [self.one_lt_n₀]
      )
      all_goals linarith [self.one_lt_b, self.one_lt_n₀]
    . linarith [self.one_lt_b]
    . apply Real.logb_nonneg
      . norm_cast
        linarith [self.one_lt_b]
      . rw [one_le_div] <;> norm_cast
        all_goals linarith [self.one_lt_n₀]
  }

  have const_pos : 0 < (C + 1) * ↑(T ((N + 1) * b + 1) + 1) := by {
    apply mul_pos
    . exact add_pos C_pos one_pos
    . norm_cast
      apply Nat.add_one_pos
  }
  apply O_trans (O_of_asymp_le (asymp_le_of_le_of_forall_ge subst_rec))
  apply O_add <;> rw [← exists_pos_smul_asymp_le_iff_O]
  . use (C + 1) * ↑(T ((N + 1) * b + 1) + 1)
    apply And.intro const_pos
    apply asymp_le_of_le_of_forall_ge (N := N)
    intro n hn
    push_cast
    rw [mul_add, add_smul]
    simp
    apply le_add_of_le_add_left (c := 0)
    simp
    rw [mul_add]
    apply le_add_of_le_add_left (c := 0)
    simp
    rw [mul_comm]
    specialize cast_n_div_N_pos hn 
    specialize one_le_cast_n_div_N hn

    apply mul_le_mul
    . apply le_trans' (le_mul_of_one_le_left _ _)
      norm_cast
      apply self.T_monotone
      rw [← k_def, add_mul, one_mul, add_assoc, add_comm b, ← add_assoc]
      apply add_le_add_right
      apply le_add_right
      simp
      rw [← Nat.cast_le (α := ℝ), Real.logb_div]
      apply le_trans Nat.cast_div_le
      push_cast
      rw [← Real.rpow_logb (b := b) (x := n), ← Real.rpow_natCast, 
          ← Real.rpow_sub, Real.rpow_logb, ← Real.rpow_one b, 
          ← Real.rpow_logb (b := b) (x := N), ← Real.rpow_add, 
          Real.rpow_one b, Real.rpow_logb, Real.rpow_le_rpow_left_iff]
      rw [sub_le_iff_le_add', add_left_comm, ← sub_le_iff_le_add']
      apply le_trans (Nat.le_ceil _)
      norm_cast
      apply Nat.ceil_le_floor_add_one
      all_goals norm_cast
      all_goals linarith [self.one_lt_b, self.one_lt_n₀]
    . rw [← k_def, ← Real.rpow_natCast]
      rw [← Real.rpow_logb (b := b) (x := Nat.cast (R := ℝ) n),
          ← Real.rpow_mul, mul_comm, Real.rpow_mul, Real.rpow_logb]
      apply Real.rpow_le_rpow_of_exponent_le
      case _ : Nat.cast (R := ℝ) ⌊Real.logb _ _⌋₊ ≤ Real.logb _ _ => (
        apply le_trans (Nat.floor_le (Real.logb_nonneg _ _))
        rw [Real.logb_le_logb]
        apply div_le_self
        all_goals norm_cast
        all_goals linarith [self.one_lt_n₀, self.one_lt_b]
      )
      all_goals norm_cast
      all_goals linarith [self.a_pos, self.one_lt_b, self.one_lt_n₀]
    . norm_cast
      apply pow_nonneg
      apply zero_le
    . apply mul_nonneg <;> linarith
    . apply mul_nonneg <;> apply mul_nonneg
      . linarith
      . linarith
      . apply GeometricSum.nonneg_of_nonneg
        apply div_nonneg
        . linarith
        . apply Real.rpow_nonneg
          linarith
      . apply Real.rpow_nonneg
        linarith
    . apply mul_nonneg
      . linarith
      . apply add_nonneg
        . apply Real.rpow_nonneg
          linarith
        . apply mul_nonneg
          . apply GeometricSum.nonneg_of_nonneg
            apply div_nonneg
            . linarith
            . apply Real.rpow_nonneg
              linarith
          . apply Real.rpow_nonneg
            linarith
  . use C 
    apply And.intro C_pos
    apply asymp_le_of_le_of_forall_ge (N := b)
    intro n hn
    simp
    rw [mul_assoc, mul_le_mul_left C_pos, ← k_def]
    apply le_add_of_le_add_right (b := 0)
    simp
    rw [mul_le_mul_right]
    apply GeometricSum.le_of_pos_of_le
    . apply div_pos
      . norm_cast
        exact self.a_pos
      . apply Real.rpow_pos_of_pos
        norm_cast
        exact self.b_pos
    . simp
      rw [Nat.sub_one_add_one]
      apply Nat.floor_le_floor
      rw [Real.logb_le_logb]
      apply div_le_self
      all_goals norm_cast
      . linarith
      . linarith [self.one_lt_n₀]
      . exact self.one_lt_b
      . apply div_pos <;> (norm_cast; linarith [self.one_lt_b, self.one_lt_n₀])
      . linarith [self.one_lt_b]
      . apply ne_of_gt
        apply Nat.log_pos self.one_lt_b
        linarith
    . apply Real.rpow_pos_of_pos
      norm_cast
      linarith [self.one_lt_b]
    . apply Real.rpow_nonneg
      linarith


lemma Ω_rec (self : MasterRecurrence T a b n₀ f d) {g : ℕ → ℕ} 
    (hg_poly : Nat.cast ∘ g ∈ Ω ℝ fun n ↦ Nat.cast (R := ℝ) n^d) 
    (hrec : ∀ n ≥ n₀, T n ≥ a * T (n / b) + g n) : 
    ∃ c : ℕ, Nat.cast ∘ T ∈ Ω ℝ fun n : ℕ ↦ GeometricSum (K := ℝ) (↑a / ↑b^d) 
                                              (⌊Real.logb ↑c ↑n⌋₊ - 1) *
                                            Nat.cast (R := ℝ) n^d := by
  obtain ⟨C, C_pos, N, N_ge, subst_master⟩ := self.k_subst' hg_poly hrec
  have n_ge_N {n : ℕ} (hn : n ≥ N ⊔ b) : n ≥ N := by {
    apply le_trans' hn
    apply le_max_left
  }
  have one_le_cast_n_div_N {n : ℕ} (hn : n ≥ N) : 
      1 ≤ Nat.cast (R := ℝ) n / ↑N := by {
    rw [one_le_div] <;> norm_cast
    linarith [self.one_lt_n₀]
  }
  have cast_n_div_N_pos {n : ℕ} (hn : n ≥ N) : 
      0 < Nat.cast (R := ℝ) n / ↑N := by {
    apply one_le_cast_n_div_N at hn
    linarith
  }

  generalize k_def : (fun n : ℕ ↦ ⌊Real.logb ↑(N ⊔ b) ↑n⌋₊) = k
  have k_pos {n : ℕ} (hn : n ≥ N ⊔ b) : 0 < k n := by {
    rw [← k_def]
    have one_lt_max := lt_max_of_lt_right (b := N) self.one_lt_b
    rw [Nat.floor_pos, ← Real.logb_self_eq_one (b := ↑(N ⊔ b)), 
        Real.logb_le_logb] <;> norm_cast
    all_goals linarith [self.one_lt_n₀]
  }

  have subst_rec : ∀ n ≥ N ⊔ b, 
      ↑(T n) ≥ ↑a^(k n) * ↑(T (n / b ^ (k n))) + 
               C * GeometricSum (K := ℝ) (↑a / ↑b ^ d) (k n - 1) *
               Nat.cast (R := ℝ) n ^ d := by {
    intro n hn

    apply le_trans (le_refl _) (subst_master (k_pos hn) _)
    rw [← k_def, ge_iff_le, ← Nat.cast_le (α := ℝ), Nat.cast_le]
    simp
    rw [← Nat.cast_max, Real.natFloor_logb_natCast]
    apply Nat.pow_log_le_self
    linarith [le_max_right N b, self.one_lt_b]
  }

  use N ⊔ b

  apply Ω_trans (Ω_of_asymp_ge (asymp_ge_of_ge_of_forall_ge subst_rec))
  rw [← exists_pos_smul_asymp_ge_iff_Ω]
  use C
  apply And.intro C_pos
  use 1
  intro n n_ge_one
  apply le_add_of_le_add_right (b := 0)
  . simp
    rw [← k_def, mul_assoc, mul_le_mul_left C_pos,
        mul_le_mul_right, Nat.cast_max]
    apply Real.rpow_pos_of_pos
    norm_cast
  . norm_cast
    apply mul_nonneg
    . apply pow_nonneg
      linarith
    . linarith


theorem O_of_lt (self : MasterRecurrence T a b n₀ f d)
    (hlt : a < Nat.cast (R := ℝ) b^d) : 
    Nat.cast ∘ T ∈ O ℝ fun n ↦ Nat.cast (R := ℝ) n^d := by
  apply O_trans self.O_rec
  apply O_add
  . apply O_of_asymp_le
    apply asymp_le_of_le_of_forall_ge (N := 2)

    intro n hn
    rw [Real.rpow_le_rpow_left_iff]
    rw [Real.logb_le_iff_le_rpow]
    all_goals norm_cast
    all_goals linarith [self.a_pos, self.one_lt_b]
  . have b_pow_d_pos : Nat.cast (R := ℝ) b^d > 0 :=
      Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
    have indep_const_pos : 0 < 1 / (1 - Nat.cast (R := ℝ) a / ↑b^d) := by {
      apply div_pos one_pos
      simp
      rw [div_lt_one] <;> assumption
    }

    apply flip O_trans
      (O_pos_smul indep_const_pos O_refl)
    apply O_of_asymp_le
    apply asymp_le_of_le_of_forall_ge (N := 0)
    intro n hn
    apply mul_le_mul
    . apply GeometricSum.le_of_base_pos_lt_one
      apply div_pos <;> norm_cast
      . exact self.a_pos
      . rw [div_lt_one]
        . exact hlt
        . apply Real.rpow_pos_of_pos
          norm_cast
          exact self.b_pos
    . trivial
    . apply Real.rpow_nonneg
      linarith
    . linarith

theorem O_of_eq (self : MasterRecurrence T a b n₀ f d)
    (heq : ↑a = Nat.cast (R := ℝ) b^d) : 
    Nat.cast ∘ T ∈ O ℝ fun n ↦ Real.logb b (Nat.cast (R := ℝ) n) * ↑n^d := by
  apply O_trans self.O_rec
  apply O_add
  . apply O_of_asymp_le
    apply asymp_le_of_le_of_forall_ge (N := b)

    intro n hn
    have logb_a_eq_d : Real.logb b a = d := by {
      rw [heq, Real.logb_rpow] <;> norm_cast <;> linarith [self.one_lt_b]
    }
    have one_le_logb_n : 1 ≤ Real.logb b n := by {
      rw [← Real.logb_self_eq_one (b := b), Real.logb_le_logb]
      all_goals norm_cast
      all_goals linarith [self.one_lt_b]
    }
    rw [logb_a_eq_d]
    apply le_mul_of_one_le_left
    apply Real.rpow_nonneg
    apply Nat.cast_nonneg
    all_goals norm_cast
  . have b_pow_d_pos : Nat.cast (R := ℝ) b^d > 0 :=
      Real.rpow_pos_of_pos (Nat.cast_pos.2 self.b_pos) d
    have a_div_b_pow_eq_one : Nat.cast (R := ℝ) a / ↑b^d = 1 := by {
      rw [div_eq_one_iff_eq] <;> linarith
    }
    have geom_indep : ∀ n ≥ b + 1, 
        GeometricSum (K := ℝ) (↑a / ↑b ^ d) (⌊Real.logb ↑b ↑n⌋₊ - 1) * 
        Nat.cast (R := ℝ) n ^ d ≤ Real.logb b n * ↑n^d := by {
      intro n hn
      rw [a_div_b_pow_eq_one, GeometricSum.base_eq_one]

      have one_lt_logb_n : 1 < Real.logb b n := by {
        rw [← Real.logb_self_eq_one (b := b)]
        apply Real.logb_lt_logb
        all_goals norm_cast
        all_goals linarith [self.one_lt_b]
      }
      
      rw [add_mul, Nat.cast_sub, sub_mul]
      . simp
        apply le_trans ((mul_le_mul_right _).2 (Nat.floor_le _)) (le_refl _)
        . apply Real.rpow_pos_of_pos
          norm_cast
          linarith
        . linarith
      . apply Nat.le_floor
        norm_cast
        linarith 
    }

    apply O_trans (O_of_asymp_le (asymp_le_of_le_of_forall_ge geom_indep))
    apply O_refl

theorem Θ_of_eq_of_rec_of_Ω (self : MasterRecurrence T a b n₀ f d)  
    (heq : a = Nat.cast (R := ℝ) b^d) {g : ℕ → ℕ}
    (hg : g ∈ O ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d⌉₊)
    (hrec : ∀ n ≥ n₀, T n ≥ a * T (n ⌈/⌉ b) + g n) :
    T ∈ Θ ℕ fun n ↦ ⌈Nat.cast (R := ℝ) n^d * Real.logb b n⌉₊ := by
  rw [← O_Ω_iff_Θ]
  rcases hg with ⟨C, C_pos, N, g_poly⟩
  sorry

theorem O_of_gt (self : MasterRecurrence T a b n₀ f d)
    (hgt : ↑a > Nat.cast (R := ℝ) b^d) : 
    Nat.cast ∘ T ∈ O ℝ fun n ↦ Nat.cast (R := ℝ) n^Real.logb b a := by
  apply O_trans self.O_rec
  apply O_add
  . apply flip O_trans (O_pos_smul
      (c := Nat.cast (R := ℝ) (T ((n₀ + 1) * b + 1)) + 1)
      (g := fun n ↦ Nat.cast (R := ℝ) n^Real.logb ↑b ↑a) (by linarith)
      O_refl)
    apply O_of_asymp_le
    apply asymp_le_of_le_of_forall_ge (N := 1)
    intro n hn
    apply le_mul_of_one_le_left
    . apply Real.rpow_nonneg
      linarith
    . linarith
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

    have pow_log_eq : ∀ n ≥ b + 1, 
        (Nat.cast (R := ℝ) a / ↑b^d) ^ Real.logb ↑b ↑n = 
        (↑n ^ Real.logb b a) / (↑n^d) := by {
      intro n hn
      rw [← Real.rpow_logb (b := b) (x := Nat.cast (R := ℝ) a / ↑b^d), 
          ← Real.rpow_mul, mul_comm (Real.logb _ _), Real.rpow_mul, 
          Real.rpow_logb, Real.logb_div, Real.logb_rpow, 
          Real.rpow_sub] <;> norm_cast
      all_goals linarith [self.one_lt_b, self.a_pos]
    }

    have geom_le : ∀ n ≥ b + 1, 
        GeometricSum (K := ℝ) (↑a / ↑b^d) (⌊Real.logb b n⌋₊ - 1) ≤
        ↑n^Real.logb b a / (↑n^d * (↑a / ↑b^d - 1)) := by {
      intro n hn
      rw [GeometricSum.base_ne_one (by linarith), Nat.sub_one_add_one,
          sub_div]
      apply le_trans (sub_le_self _ _)
      have pow_floor_le : 
          (Nat.cast (R := ℝ) a / ↑b ^ d) ^ ⌊Real.logb ↑b ↑n⌋₊ ≤ 
          (↑a / ↑b ^ d) ^ Real.logb ↑b ↑n := by {
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le
        . linarith
        . apply Nat.floor_le
          apply Real.logb_nonneg <;> (norm_cast; linarith [self.one_lt_b])
      }
      apply le_trans ((div_le_div_iff_of_pos_right _).2 pow_floor_le)
      rw [pow_log_eq, div_div]
      . exact hn
      . linarith
      . rw [one_div_nonneg]
        linarith
      . apply ne_of_gt
        rw [Nat.floor_pos, ← Real.logb_self_eq_one (b := b), 
            Real.logb_le_logb] <;> (norm_cast; linarith [self.one_lt_b])
    }

    have geom_asymp_le : 
        AsympLE (fun n : ℕ ↦ 
          GeometricSum (K := ℝ) (↑a / ↑b^d) (⌊Real.logb b n⌋₊ - 1) * ↑n^d)
        (fun n : ℕ ↦ 1 / (↑a / ↑b^d - 1) * ↑n^Real.logb b a) := by {
      apply asymp_le_of_le_of_forall_ge (N := b + 1)
      intro n hn
      apply le_trans ((mul_le_mul_right _).2 (geom_le n hn))
      rw [← mul_div_right_comm, ← div_div, ← mul_div, div_self, 
          ← mul_div, mul_comm]
      apply ne_of_gt
      repeat case _ : 0 < Nat.cast (R := ℝ) n^d => (
        apply Real.rpow_pos_of_pos
        norm_cast
        linarith
      )
    }

    apply O_trans (O_of_asymp_le geom_asymp_le)
    apply flip O_pos_smul O_refl
    rw [gt_iff_lt, one_div_pos]
    linarith


end MasterRecurrence


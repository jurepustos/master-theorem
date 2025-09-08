import Mathlib

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv


/- We formalize the proof at https://www.cs.dartmouth.edu/~deepc/Courses/S20/lecs/lec3supp.pdf -/

/- Divide and conquer recurrence -/
private structure MasterRecBase (T : ℕ → ℕ) (a b n₀ : ℕ) (f : ℕ → ℕ) (d : ℝ) 
where
  /- there should be at least one boundary condition -/
  one_lt_n₀ : 1 < n₀
  /-a is positive -/
  a_pos : a > 0
  /- we always divide into more than than one part -/
  n₀_lt_b : n₀ < b
  /- polynomial degree is at least 1 -/
  one_le_d : 1 ≤ d
  /-T is monotone -/
  T_monotone : Monotone T

structure UpperMasterRec (T : ℕ → ℕ) (a b n₀ : ℕ) (f : ℕ → ℕ) (d : ℝ) 
    extends MasterRecBase T a b n₀ f d where
  /- f is polynomially bounded above -/
  f_upper_poly : Nat.cast ∘ f ∈ O ℝ fun n ↦ Nat.cast (R := ℝ) n^d
  /- The recurrence formula -/
  T_upper_rec : ∀ n ≥ n₀, T n ≤ a * T (n ⌈/⌉ b) + f n

structure LowerMasterRec (T : ℕ → ℕ) (a b n₀ : ℕ) (f : ℕ → ℕ) (d : ℝ) 
    extends MasterRecBase T a b n₀ f d where
  /- f is positive -/
  f_pos : ∀ n ≥ n₀, f n > 0
  /- f is polynomially bounded above -/
  f_lower_poly : Nat.cast ∘ f ∈ Ω ℝ fun n ↦ Nat.cast (R := ℝ) n^d
  /- The recurrence formula -/
  T_lower_rec : ∀ n ≥ n₀, T n ≥ a * T (n / b) + f n

structure MasterRec (T : ℕ → ℕ) (a b n₀ : ℕ) (f : ℕ → ℕ) (d : ℝ)
  extends UpperMasterRec T a b n₀ f d, 
          LowerMasterRec T a b n₀ f d


private lemma add_poly {b n : ℕ} {d : ℝ} (hd : d ≥ 1) 
    (hb : b > 1) (hn : n > 1) : 
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
  rw [add_comm, mul_assoc, mul_le_mul_iff_right₀ (NNReal.rpow_pos two_pos)]
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

private lemma f_of_add_b_poly {f : ℕ → ℕ} {C d : ℝ} {N b : ℕ} 
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
  apply le_trans ((mul_le_mul_iff_right₀ hC).2 poly_le)
  rw [← mul_assoc, ← mul_assoc, mul_le_mul_iff_left₀]
  apply Real.rpow_pos_of_pos
  norm_cast
  linarith


variable {T f : ℕ → ℕ} {a b n₀ : ℕ} {d : ℝ}


namespace MasterRecBase


private lemma n₀_pos (self: MasterRecBase T a b n₀ f d) : n₀ > 0 := 
  lt_trans one_pos self.one_lt_n₀

private lemma one_lt_b (self: MasterRecBase T a b n₀ f d) : b > 1 := by 
  linarith [self.one_lt_n₀, self.n₀_lt_b]

private lemma b_pos (self: MasterRecBase T a b n₀ f d) : b > 0 := 
  lt_trans one_pos self.one_lt_b

end MasterRecBase


namespace UpperMasterRec


private lemma formula_subst_once {k n : ℕ} {C : ℝ}
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
        mul_comm C, mul_assoc _ C, ← mul_add, ← Real.div_rpow, 
        mul_le_mul_iff_right₀]
    exact hrec

    all_goals norm_cast
    . apply pow_pos
      exact ha
    . apply zero_le
    . apply pow_nonneg
      apply zero_le
  }

private theorem formula_subst {k : ℕ → ℕ} {C : ℝ}
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
    rw [mul_le_mul_iff_right₀ hC, ← Nat.cast_pow]
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le
    linarith

private lemma k_subst (self : UpperMasterRec T a b n₀ f d) : 
    ∃ C > 0, ∃ N ≥ n₀, ∀ {k : ℕ → ℕ}, ∀ {n : ℕ}, n ≥ N * b^k n →
      ↑(T (n + b)) ≤ ↑a^k n * ↑(T (n / b^k n + b)) + 
                     C * GeometricSum (K := ℝ) (a/b^d) (k n - 1) * ↑n^d := by
  obtain ⟨C, C_pos, N, f_poly₁⟩ := 
    exists_pos_smul_asymp_le_iff_O.2 self.f_upper_poly

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
    have ceilDiv_apply := self.T_upper_rec (n + b) (le_add_right (by linarith))
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

lemma O_geom (self : UpperMasterRec T a b n₀ f d) : 
    Nat.cast ∘ T ∈ O ℝ fun n ↦ Nat.cast (R := ℝ) n ^ (Real.logb b a) +
                    GeometricSum (K := ℝ) (↑a / ↑b^d) (⌊Real.logb b n⌋₊ - 1) *
                    Nat.cast (R := ℝ) n^d := by
  rcases self.k_subst with ⟨C, C_pos, N, N_ge, subst_master⟩

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
    rw [mul_assoc, mul_le_mul_iff_right₀ C_pos, ← k_def]
    apply le_add_of_le_add_right (b := 0)
    simp
    rw [mul_le_mul_iff_left₀]
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
        exact Nat.log_pos self.one_lt_b hn
    . apply Real.rpow_pos_of_pos
      norm_cast
      exact le_trans self.b_pos hn
    . apply Real.rpow_nonneg
      apply Nat.cast_nonneg

theorem O_of_lt (self : UpperMasterRec T a b n₀ f d)
    (hlt : a < Nat.cast (R := ℝ) b^d) : 
    Nat.cast ∘ T ∈ O ℝ fun n ↦ Nat.cast (R := ℝ) n^d := by
  apply O_trans self.O_geom
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

theorem O_of_eq (self : UpperMasterRec T a b n₀ f d)
    (heq : ↑a = Nat.cast (R := ℝ) b^d) : 
    Nat.cast ∘ T ∈ O ℝ fun n ↦ Real.logb b (Nat.cast (R := ℝ) n) * ↑n^d := by
  apply O_trans self.O_geom
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
        apply le_trans ((mul_le_mul_iff_left₀ _).2 
                        (Nat.floor_le _)) (le_refl _)
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

theorem O_of_gt (self : UpperMasterRec T a b n₀ f d)
    (hgt : ↑a > Nat.cast (R := ℝ) b^d) : 
    Nat.cast ∘ T ∈ O ℝ fun n ↦ Nat.cast (R := ℝ) n^Real.logb b a := by
  apply O_trans self.O_geom
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
      apply le_trans ((mul_le_mul_iff_left₀ _).2 (geom_le n hn))
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

end UpperMasterRec


namespace LowerMasterRec


private lemma formula_subst_once {k n : ℕ} {C : ℝ}
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
        mul_comm C, mul_assoc _ C, ← mul_add, ← Real.div_rpow, 
        mul_le_mul_iff_right₀]
    exact hrec

    all_goals norm_cast
    . apply pow_pos
      exact ha
    . apply zero_le
    . apply pow_nonneg
      apply zero_le
  }

private theorem formula_subst {C : ℝ} (ha : a > 0) (hb : b > 1) 
    (hn₀ : n₀ < b) (hC : C > 0) (hd : d ≥ 1)
    (hrec : ∀ n ≥ n₀, T n ≥ a * T (n / b) + 
                            C * (Nat.cast (R := ℝ) n)^d) :
    ∀ {k : ℕ → ℕ}, ∀ {n : ℕ}, k n > 0 → n ≥ b^k n → 
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
    specialize hrec n (by linarith)

    apply le_trans' hrec
    apply add_le_add_left
    rw [mul_le_mul_iff_left₀]
    . apply div_le_self
      . linarith
      . apply Real.one_le_rpow <;> linarith
    . apply Real.rpow_pos_of_pos
      norm_cast
      linarith
  . have b_pos : b > 0 := by linarith
    have b_pow_pos : b^(x+1) > 0 := pow_pos b_pos (x+1)

    have n_ge_ind : n ≥ b^(x+1) := by {
      apply le_trans (pow_le_pow_right₀ _ (Nat.le_succ _)) hn
      linarith
    }
    have cast_n_div_b_pow_nonneg : 0 ≤ Nat.cast (R := ℝ) n / ↑b ^ (x+1) := by {
      apply div_nonneg <;> norm_cast <;> linarith
    }

    specialize hx n_ge_ind
    apply flip (formula_subst_once ha) hx
    specialize hrec (n / b^(x+1)) (by {
      apply le_trans (le_of_lt hn₀)
      rw [Nat.le_div_iff_mul_le]
      rw [← pow_succ']
      all_goals assumption
    })

    apply le_trans' hrec
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
    apply add_le_add_left
    rw [div_eq_mul_inv, mul_assoc, ← Real.inv_rpow, mul_le_mul_iff_right₀, 
        ← Real.mul_rpow]
    apply Real.rpow_le_rpow
    . apply mul_nonneg <;> linarith
    . rw [← Nat.ceil_le, Nat.le_div_iff_mul_le b_pow_pos, 
          ← Nat.cast_le (α := ℝ), Nat.cast_mul]
      apply le_trans ((mul_le_mul_iff_left₀ _).2 (Nat.ceil_le_two_mul _))
      all_goals norm_cast
      . rw [← mul_assoc, mul_assoc, div_mul_cancel₀]
        . linarith
        . norm_cast
          linarith
      . apply le_mul_of_one_le_right
        . linarith
        . rw [one_le_div₀] <;> norm_cast
    all_goals linarith

private lemma k_subst (self : LowerMasterRec T a b n₀ f d) :
    ∃ C > 0, ∀ {k : ℕ → ℕ}, ∀ {n : ℕ}, k n > 0 → n ≥ b^k n →
      ↑(T n) ≥ ↑a^k n * ↑(T (n / b^k n)) + 
               C * GeometricSum (K := ℝ) (↑a / ↑b^d) (k n - 1) * n^d := by
  rcases f_lower_poly with ⟨C, C_pos, f_poly⟩
  have rec_apply : ∀ n ≥ n₀, T n ≥ ↑a * ↑(T (n / b)) + 
                                  C * Nat.cast (R := ℝ) n^d := by {
    intro n hn
    apply flip add_le_of_add_le_left (f_poly n hn)
    norm_cast
    apply self.T_lower_rec n
    linarith [self.n₀_lt_b]
  }

  use C / 2^d
  apply And.intro (by {
    apply div_pos C_pos
    apply Real.rpow_pos_of_pos
    exact two_pos
  })

  intro k n hk hn
  have subst_rec := formula_subst self.a_pos self.one_lt_b self.n₀_lt_b C_pos 
                                  self.one_le_d rec_apply hk hn
  linarith
where
  f_lower_poly : ∃ C > 0, ∀ n ≥ n₀, f n ≥ C * Nat.cast (R := ℝ) n^d := by {
    obtain ⟨C, C_pos, N, f_poly⟩ := 
      exists_pos_smul_asymp_ge_iff_Ω.2 self.f_lower_poly

    if hN : N ≤ n₀ then {
      use C
      apply And.intro C_pos
      intro n hn
      specialize f_poly n (by linarith)
      exact f_poly
    }
    else {
      simp at hN
      generalize g_def : (fun n : Fin (N - n₀) ↦ n + n₀) = g
      have g_inj : Function.Injective g := by {
        unfold Function.Injective
        intro x y hg
        rw [← g_def] at hg 
        simp at hg
        rw [Fin.val_eq_val] at hg
        exact hg
      }
      have g_image_eq : Set.range g = {x | x < N ∧ x ≥ n₀} := by {
        rw [← g_def]
        ext x
        constructor
        . intro h
          simp at h
          rcases h with ⟨y, hy⟩
          simp
          constructor
          . rw [← hy]
            have y_le := Nat.le_sub_one_of_lt (Fin.is_lt y)
            apply lt_of_le_of_lt (add_le_add_right y_le _)
            omega
          . linarith
        . intro h
          simp at h
          rcases h with ⟨x_le_N, x_ge_n₀⟩
          simp
          use Fin.mk (x - n₀) (by {
            apply Nat.sub_lt_sub_right <;> assumption
          })
          simp
          omega
      }
      have domain_finite : {x | x < N ∧ x ≥ n₀}.Finite := by {
        rw [← Set.finite_coe_iff, ← g_image_eq]
        apply Nat.finite_of_card_ne_zero
        rw [Nat.card_range_of_injective g_inj, 
            Nat.card_eq_of_equiv_fin (Equiv.refl _)]
        apply Nat.sub_ne_zero_of_lt
        exact hN
      }
      have domain_nonempty : {x | x < N ∧ x ≥ n₀}.Nonempty := by {
        rw [Set.nonempty_def]
        simp
        use n₀
      }

      have f_image_finite : (f '' {x | x < N ∧ x ≥ n₀}).Finite :=
        Set.Finite.image f domain_finite
      have f_image_nonempty : f_image_finite.toFinset.Nonempty := by {
        simp
        exact domain_nonempty
      }

      obtain ⟨m, m_in_image, min_m⟩ := 
        f_image_finite.toFinset.exists_minimal f_image_nonempty

      rw [Set.Finite.mem_toFinset, Set.mem_image] at m_in_image
      rcases m_in_image with ⟨x, x_in_domain, fx_eq⟩
      simp at x_in_domain
      rcases x_in_domain with ⟨x_lt_N, n₀_le_x⟩

      use C ⊓ ↑m / ↑N^d
      apply And.intro (by {
        apply lt_min C_pos
        apply div_pos
        . rw [← fx_eq]
          norm_cast
          apply self.f_pos
          linarith
        . apply Real.rpow_pos_of_pos
          norm_cast
          linarith
      })

      intro n hn
      rw [min_mul_of_nonneg, mul_comm (_ / _), mul_div, 
          mul_comm (Nat.cast (R := ℝ) n^d), ← mul_div, ge_iff_le]
      . if hn_N : n < N then {
          apply le_trans (min_le_right _ _)
          apply le_trans (mul_le_of_le_one_right _ _)
          . norm_cast
            simp at min_m
            if h_fn : f n ≤ m then {
              exact min_m n hn_N hn (Eq.refl (f n)) h_fn
            }
            else {
              simp at h_fn
              linarith
            }
          . linarith
          . rw [div_le_one₀]
            . apply Real.rpow_le_rpow <;> norm_cast
                                      <;> linarith [self.one_le_d]
            . apply Real.rpow_pos_of_pos
              norm_cast
              linarith [self.one_lt_n₀]
        }
        else {
          apply le_trans (min_le_left _ _)
          simp at hn_N
          exact f_poly n hn_N
        }
      . apply Real.rpow_nonneg
        linarith
    }
  }

lemma Ω_geom (self : LowerMasterRec T a b n₀ f d) :
    Nat.cast ∘ T ∈ Ω ℝ fun n : ℕ ↦ GeometricSum (K := ℝ) (↑a / ↑b^d) 
                                      (⌊Real.logb ↑b ↑n⌋₊ - 1) *
                                    Nat.cast (R := ℝ) n^d := by
  rcases self.k_subst with ⟨C, C_pos, subst_master⟩

  generalize k_def : (fun n : ℕ ↦ ⌊Real.logb ↑b ↑n⌋₊) = k
  have k_pos {n : ℕ} (hn : n ≥ b) : 0 < k n := by {
    rw [← k_def]
    rw [Nat.floor_pos, ← Real.logb_self_eq_one (b := ↑b), 
        Real.logb_le_logb] <;> norm_cast
    all_goals linarith [self.one_lt_b]
  }

  have subst_rec : ∀ n ≥ b, 
      ↑(T n) ≥ ↑a^(k n) * ↑(T (n / b ^ (k n))) + 
               C * GeometricSum (K := ℝ) (↑a / ↑b ^ d) (k n - 1) *
               Nat.cast (R := ℝ) n ^ d := by {
    intro n hn

    apply le_trans (le_refl _) (subst_master (k_pos hn) _)
    rw [← k_def, ge_iff_le, ← Nat.cast_le (α := ℝ), Nat.cast_le]
    simp
    rw [Real.natFloor_logb_natCast]
    apply Nat.pow_log_le_self
    linarith [self.b_pos]
  }

  apply Ω_trans (Ω_of_asymp_ge (asymp_ge_of_ge_of_forall_ge subst_rec))
  rw [← exists_pos_smul_asymp_ge_iff_Ω]
  use C
  apply And.intro C_pos
  use 1
  intro n n_ge_one
  apply le_add_of_le_add_right (b := 0)
  . simp
    rw [← k_def, mul_assoc, mul_le_mul_iff_right₀ C_pos, mul_le_mul_iff_left₀]
    apply Real.rpow_pos_of_pos
    norm_cast
  . norm_cast
    apply mul_nonneg
    . apply pow_nonneg
      linarith
    . linarith

lemma Ω_pow_d (self : LowerMasterRec T a b n₀ f d) :
    Nat.cast ∘ T ∈ Ω ℝ fun n ↦ Nat.cast (R := ℝ) n^d := by
  rw [← exists_pos_smul_asymp_ge_iff_Ω]
  rcases self.f_lower_poly with ⟨C, C_pos, N, f_poly⟩

  use C
  apply And.intro C_pos
  apply asymp_ge_of_ge_of_forall_ge (N := N ⊔ n₀)

  intro n hn
  have n_ge_N : n ≥ N := by linarith [le_max_left N n₀]
  have n_ge_n₀ : n ≥ n₀ := by linarith [le_max_right N n₀]
  specialize f_poly n (by linarith)

  simp
  apply le_trans' (Nat.cast_le.2 (self.T_lower_rec n n_ge_n₀))
  push_cast
  apply le_add_of_le_add_right (b := 0)
  . simp
    exact f_poly
  . apply mul_nonneg <;> linarith

theorem Ω_of_eq (self : LowerMasterRec T a b n₀ f d)  
    (heq : a = Nat.cast (R := ℝ) b^d) :
    Nat.cast ∘ T ∈ Ω ℝ fun n ↦ Real.logb b (Nat.cast (R := ℝ) n) * ↑n^d := by
  apply Ω_trans self.Ω_geom
  rw [← exists_pos_smul_asymp_ge_iff_Ω]

  use 1 / 2
  apply And.intro (by {
    apply mul_pos <;> linarith
  }) 
  apply asymp_ge_of_ge_of_forall_ge (N := b^2)
  intro n hn

  have c_sq_pos : 0 < b ^ 2 := pow_pos self.b_pos 2
  have n_pos : 0 < n := by linarith
  have n_sq_pos : 0 < n ^ 2 := by {
    apply pow_pos
    linarith
  }
  have n_pow_d_pos : 0 < Nat.cast (R := ℝ) n ^ d := by {
    apply Real.rpow_pos_of_pos
    norm_cast
  }
  have b_pow_d_pos : 0 < Nat.cast (R := ℝ) b ^ d := by {
    apply Real.rpow_pos_of_pos
    norm_cast
    exact self.b_pos
  }
  have natLog_n_pos : 0 < Nat.log b n := by {
    apply Nat.log_pos self.one_lt_b
    rw [← pow_one b]
    apply le_trans (pow_le_pow_right₀ _ one_le_two) hn
    linarith [self.one_lt_b]
  }
  have b_pow_logb_nonneg : 
      0 ≤ Nat.cast (R := ℝ) b ^ (Real.logb ↑b ↑n - 1) := by {
    apply Real.rpow_nonneg
    linarith
  }

  rw [heq, div_self, GeometricSum.base_eq_one]
  norm_cast
  rw [Nat.sub_one_add_one]
  simp
  rw [← mul_assoc, mul_le_mul_iff_left₀]

  apply le_trans ((mul_le_mul_iff_right₀ _).2 (Nat.le_ceil _))
  rw [inv_mul_le_iff₀]
  norm_cast
  rw [← Nat.le_pow_iff_clog_le, mul_comm, pow_mul,
      ← Real.natFloor_logb_natCast]
  rw [← Nat.cast_le (α := ℝ), Nat.cast_pow, Nat.cast_pow,
      ← Real.rpow_natCast (n := ⌊_⌋₊)]
  apply le_trans' (pow_le_pow_left₀ _ 
                  (Real.rpow_le_rpow_of_exponent_le _ 
                  (le_of_lt (Nat.sub_one_lt_floor _))) _)
  rw [Real.rpow_sub, Real.rpow_logb]
  simp
  rw [div_pow]
  have hn' : Nat.cast (R := ℝ) n ≥ ↑b^2 := by norm_cast
  apply le_trans' ((div_le_div_iff_of_pos_left _ _ _).2 hn')
  rw [div_eq_mul_inv, pow_two, mul_assoc, mul_inv_cancel₀, mul_one]

  all_goals (norm_cast <;> linarith [self.one_lt_b])

theorem Ω_of_gt (self : LowerMasterRec T a b n₀ f d)  
    (hgt : ↑a > Nat.cast (R := ℝ) b^d) :
    Nat.cast ∘ T ∈ Ω ℝ fun n ↦ Nat.cast (R := ℝ) n ^ Real.logb ↑b ↑a := by
  apply Ω_trans self.Ω_geom
  rw [← exists_pos_smul_asymp_ge_iff_Ω]
  use (Nat.cast (R := ℝ) a / ↑b^d - 1)⁻¹ * (Nat.cast (R := ℝ) a / ↑b^d)⁻¹ * 2⁻¹
  have b_pow_pos : 0 < Nat.cast (R := ℝ) b^d := by {
    apply Real.rpow_pos_of_pos
    norm_cast
    exact self.b_pos
  }
  have one_lt_a_div_b_pow : 1 < Nat.cast (R := ℝ) a / ↑b^d := by {
    rw [one_lt_div] <;> assumption
  }
  apply And.intro (by {
    simp
    apply mul_pos
    . rw [inv_pos]
      simp [one_lt_a_div_b_pow]
    . rw [div_eq_mul_inv]
      apply mul_pos <;> norm_cast
      simp
      exact self.a_pos
  })
  generalize K_def : 
    ⌈(Nat.cast (R := ℝ) a / ↑b^d * 2)^((Real.logb ↑b ↑a + -d)⁻¹)⌉₊ = K
  apply asymp_ge_of_ge_of_forall_ge (N := K + b + 1)

  intro n hn

  have n_ge_K : n ≥ K := by linarith
  have n_ge_b_succ : n ≥ b + 1 := by {
    rw [add_assoc] at hn
    apply le_trans (Nat.le_add_left _ _) at hn
    exact hn
  }
  have n_gt_one : n > 1 := by linarith [self.b_pos]
  have n_pow_le : Nat.cast (R := ℝ) n^d < ↑n^Real.logb ↑b ↑a := by {
    apply Real.rpow_lt_rpow_of_exponent_lt <;> norm_cast
    rw [← Real.logb_rpow (b := ↑b) (x := d)] <;> norm_cast
    apply Real.logb_lt_logb <;> norm_cast
    . exact self.one_lt_b
    . exact self.b_pos
    . linarith [self.one_lt_b]
  }

  rw [GeometricSum.base_ne_one, Nat.sub_one_add_one, mul_comm, mul_div, 
      div_eq_mul_inv, mul_comm]
  simp
  rw [mul_assoc, mul_assoc, mul_le_mul_iff_right₀, ← Real.rpow_natCast,
      ← div_le_iff₀']
  have pow_logb_swap : 
      Nat.cast (R := ℝ) a^Real.logb ↑b ↑n = ↑n^Real.logb ↑b ↑a := by {
    rw [← Real.rpow_logb (b := ↑b) (x := ↑a), ← Real.rpow_mul, mul_comm,
        Real.rpow_mul, Real.rpow_logb, Real.rpow_logb] <;> norm_cast
    all_goals linarith [self.one_lt_b, self.a_pos]
  }
  apply le_trans' (sub_le_sub_right 
                  (Real.rpow_le_rpow_of_exponent_le _ 
                  (le_of_lt (Nat.sub_one_lt_floor _))) _)
  rw [Real.rpow_sub, Real.rpow_one, mul_comm, ← div_mul, mul_comm_div, 
      Real.div_rpow, pow_logb_swap, ← Real.rpow_mul, mul_comm d, 
      Real.rpow_mul, Real.rpow_logb]

  rw [mul_assoc, ← mul_comm (_/_), ← mul_comm (_/_), ← mul_assoc, ← mul_div,
      le_sub_iff_add_le, mul_assoc]
  apply le_trans (add_one_le_two_mul _)
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀, one_mul]

  all_goals norm_cast
  all_goals try linarith [self.one_lt_b]
  . rw [le_inv_mul_iff₀, ← inv_mul_le_iff₀, 
        div_eq_mul_inv (Nat.cast (R := ℝ) n^_), ← Real.rpow_neg, 
        ← Real.rpow_add, ← Real.rpow_inv_le_iff_of_pos]
    simp
    apply le_trans (Nat.le_ceil _)
    rw [K_def]
    all_goals norm_cast
    all_goals try linarith
    . simp
      linarith
    . simp
      rw [Real.lt_logb_iff_rpow_lt] <;> norm_cast
      . exact self.one_lt_b
      . exact self.a_pos
    . apply div_pos <;> norm_cast
      exact self.a_pos
  . apply Real.rpow_pos_of_pos
    norm_cast
    linarith
  . simp [one_lt_a_div_b_pow]
  . apply ne_zero_of_lt (b := 0)
    apply Nat.log_pos <;> linarith [self.one_lt_b]

end LowerMasterRec


namespace MasterRec


theorem Θ_of_lt (self : MasterRec T a b n₀ f d)  
    (hlt : ↑a < Nat.cast (R := ℝ) b^d) :
    Nat.cast ∘ T ∈ Θ ℝ fun n ↦ Nat.cast (R := ℝ) n^d := by
  rw [← O_Ω_iff_Θ]
  constructor
  . exact self.toUpperMasterRec.O_of_lt hlt
  . exact self.toLowerMasterRec.Ω_pow_d

theorem Θ_of_eq (self : MasterRec T a b n₀ f d)  
    (heq : ↑a = Nat.cast (R := ℝ) b^d) :
    Nat.cast ∘ T ∈ Θ ℝ fun n ↦ Real.logb ↑b (Nat.cast (R := ℝ) n) * ↑n^d := by
  rw [← O_Ω_iff_Θ]
  constructor
  . exact self.toUpperMasterRec.O_of_eq heq
  . exact self.toLowerMasterRec.Ω_of_eq heq

theorem Θ_of_gt (self : MasterRec T a b n₀ f d)  
    (hgt : ↑a > Nat.cast (R := ℝ) b^d) :
    Nat.cast ∘ T ∈ Θ ℝ fun n ↦ Nat.cast (R := ℝ) n^Real.logb ↑b ↑a := by
  rw [← O_Ω_iff_Θ]
  constructor
  . exact self.toUpperMasterRec.O_of_gt hgt
  . exact self.toLowerMasterRec.Ω_of_gt hgt

end MasterRec


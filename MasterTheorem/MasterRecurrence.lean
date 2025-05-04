import Mathlib

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv


theorem le_const_mul_of_asymp_bounded_above {f g : ℕ → ℕ}
    (h : AsympBoundedAbove ℕ f g) (hg : ∀ n ≥ 1, g n ≥ 1) (N : ℕ) : 
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

theorem le_const_mul_iff_asymp_bounded_above {f g : ℕ → ℕ} (hg : ∀ n ≥ 1, g n ≥ 1) 
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

private lemma formula_subst_once {T : ℕ → ℕ} {a b d C k : ℕ} (n : ℕ) (ha : a > 0)
    (hC : C > 0) (hd : d > 0) (hrec : T (n / b^k) ≤ a * T (n / b^(k+1)) + C * (n / b^k)^d)
    (hformula : T n ≤ a^k * T (n / b^k) + (GeometricSum C (a / (b^d)) (k-1)) * n^d) :
    T n ≤ a^(k+1) * T (n / b^(k+1)) + (GeometricSum C (a / (b^d)) k) * n^d := by
  if hk : k = 0 then {
    rw [hk, GeometricSum.def_zero, zero_add, pow_one, pow_one, ← Nat.cast_mul,
        ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_le]
    rw [hk, pow_zero, Nat.div_one, zero_add, pow_one] at hrec 
    exact hrec
  }
  else {
    rw [← @Nat.cast_le ℚ, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow] at hrec
    rw [pow_succ, mul_assoc, ← Nat.sub_one_add_one hk, ← GeometricSum.def_succ,
        Nat.sub_one_add_one hk, add_mul, ← add_assoc, div_pow, ← pow_mul, 
        mul_assoc (Nat.cast C), div_mul_eq_mul_div, mul_comm ((Nat.cast a)^k) ((Nat.cast n)^d),
        ← div_mul_eq_mul_div, mul_comm d k, pow_mul, ← div_pow, mul_comm _ ((Nat.cast a)^k),
        ← mul_assoc (Nat.cast C), mul_comm (Nat.cast C), mul_assoc, ← mul_add]

    apply le_add_of_le_add_right hformula
    rw [mul_le_mul_left (pow_pos (Nat.cast_pos.2 ha) k)]
    apply le_add_of_le_add_left hrec
    rw [mul_le_mul_left (Nat.cast_pos.2 hC), pow_le_pow_iff_left₀ (Nat.cast_nonneg _)]
    . rw [← Nat.cast_pow]
      exact Nat.cast_div_le
    . exact div_nonneg (Nat.cast_nonneg n) (pow_nonneg (Nat.cast_nonneg b) k)
    . exact Nat.ne_zero_iff_zero_lt.2 hd
  }

private theorem formula_subst {T : ℕ → ℕ} {a b d C n₀ : ℕ} (k n : ℕ) (ha : a > 0)
    (hb : b > 1) (hn : n ≥ n₀ * b^k) (hC : C > 0) (hd : d > 0)
    (hrec : ∀ m : ℕ, m ≥ n₀ → T m ≤ a * T (m / b) + C * m^d) :
    T n ≤ a^k * T (n / b^k) + (GeometricSum C (a / b^d) (k-1)) * n^d := by
  induction' k with x hx
  . rw [← Nat.cast_pow, pow_zero, Nat.zero_sub, pow_zero, 
        Nat.div_one, GeometricSum.def_zero, Nat.cast_one, one_mul]
    rw [pow_zero, mul_one] at hn
    apply le_add_of_le_of_nonneg (le_refl _)
    apply mul_nonneg <;> simp
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
    apply formula_subst_once n ha hC hd
    . specialize hrec (n / b^x) n₀_le_x_div_b_pow_x
      rw [Nat.div_div_eq_div_mul, ← pow_succ] at hrec
      exact hrec
    . exact hx


variable {T f : ℕ → ℕ} {a b d n₀ : ℕ}

lemma n₀_pos (self: MasterRecurrence T a b n₀ f) : n₀ > 0 := lt_trans one_pos self.one_lt_n₀ 

lemma b_pos (self: MasterRecurrence T a b n₀ f) : b > 0 := lt_trans one_pos self.one_lt_b 

private lemma add_poly (self : MasterRecurrence T a b n₀ f) (hd : d > 0) : 
    ∀ n > 1, (n + b)^d ≤ 2^(d-1) * b^d * n^d := by
  intro n hn
  rw [← Nat.sub_one_add_one (ne_of_gt hd), Nat.sub_one_add_one (ne_of_gt hd)]
  apply le_trans (add_pow_le (zero_le n) (le_of_lt self.b_pos) d)
  rw [mul_assoc, mul_le_mul_left (pow_pos two_pos (d-1))]
  have d_ne_zero : d ≠ 0 := Nat.ne_zero_iff_zero_lt.2 hd 
  apply add_le_mul' <;> apply Nat.succ_le_of_lt
  . exact one_lt_pow₀ hn d_ne_zero
  . exact one_lt_pow₀ self.one_lt_b d_ne_zero 

private lemma f_of_add_b_poly {C : ℕ} (self : MasterRecurrence T a b n₀ f) (hd : d > 0) 
    (hC : C > 0) (hf_poly : ∀ n > 0, f n ≤ C * n^d) : 
    ∀ n > 1, f (n + b) ≤ C * 2^(d-1) * b^d * n^d := by
  intro n hn
  apply le_trans (hf_poly (n + b) (le_add_of_le_of_nonneg (le_of_lt hn) (zero_le b)))
  rw [mul_assoc, mul_assoc, mul_le_mul_left hC, ← mul_assoc]
  exact self.add_poly hd n hn


def self_subst {C : ℕ} (self : MasterRecurrence T a b n₀ f) (k : ℕ)
    (hk : k > 0) (hd : d > 0) (hC : C > 0) (hf_poly : ∀ n > 0, f n ≤ C * n^d) : 
    MasterRecurrence (fun n ↦ T (n + b)) (a^k) (b^k) (n₀ * b^k)
    (fun n ↦ ⌈GeometricSum (↑C * 2^(d-1) * ↑b^d) (a/b^d) (k - 1)⌉.toNat * n^d) :=
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
                ⌈GeometricSum (C * 2^(d-1) * b^d) (↑a/↑b^d) (k-1)⌉.toNat * n^d by {
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

      have rec_apply : ∀ m ≥ n₀, S m ≤ a * S (m / b) + C * 2^(d-1) * b^d * m ^ d := by {
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

          apply flip le_add_of_le_add_left 
            (self.f_of_add_b_poly hd hC hf_poly m m_gt_one) at ceilDiv_apply
          exact ceilDiv_apply
      }
      
      rw [← @Nat.cast_le ℚ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, 
          Nat.cast_mul, Nat.cast_pow, Int.ceil_toNat]

      have const_pos : 0 < C * 2^(d-1) * b^d :=
        mul_pos (mul_pos hC (pow_pos two_pos (d-1))) (pow_pos self.b_pos d)
      have geom_le_ceil : GeometricSum (↑C * 2^(d-1) * ↑b^d) (↑a / ↑b ^ d) (k - 1) * n^d ≤ 
                          ⌈GeometricSum (↑C * 2^(d-1) * ↑b^d) (↑a / ↑b ^ d) (k - 1)⌉₊ * n^d := by {
        have right_pos : 0 < (@Nat.cast ℚ _ (C * 2 ^ (d-1) * b^d)) * ↑n^d :=
          mul_pos (Nat.cast_pos.2 const_pos) (pow_pos (Nat.cast_pos.2 n_pos) d)
        rw [mul_le_mul_right (pow_pos (Nat.cast_pos.2 n_pos) d)]
        apply Nat.le_ceil
      }
      rw [S_apply, S_apply]
      apply flip le_add_of_le_add_left geom_le_ceil
      rw [← Nat.cast_ofNat, ← Nat.cast_pow 2, ← Nat.cast_mul, 
          ← Nat.cast_pow b, ← Nat.cast_mul, Nat.cast_pow b]
      exact formula_subst k n self.a_pos self.one_lt_b hn const_pos hd rec_apply
    }
  }


end MasterRecurrence


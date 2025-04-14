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

private theorem func_le_mul_func_of_lt (f : ℕ → ℕ) {g : ℕ → ℕ} (N : ℕ) (hg : g ≥ 1) : ∃ C > 0, ∀ n < N, f n ≤ C * g n := by
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
    . intro n n_lt_succ
      rw [add_mul]
      if hn_m : n < m then {
        apply le_add_of_le_of_nonneg (hm n hn_m)
        apply mul_nonneg <;> apply Nat.zero_le
      }
      else {
        simp at hn_m
        have n_eq_m : n = m := eq_of_le_of_le (Nat.le_of_lt_add_one n_lt_succ) hn_m
        apply le_add_of_nonneg_of_le (mul_nonneg (le_of_lt C_pos) (zero_le (g n)))
        rw [← mul_one (f n), ← n_eq_m]
        exact Nat.mul_le_mul_left (f n) (hg n)
      }

private theorem func_le_const_mul_func_of_asymp_bounded_above {f g : ℕ → ℕ} (h : AsympBoundedAbove ℕ f g) (hg : g ≥ 1) : ∃ C > 0, ∀ n, f n ≤ C * g n := by
  rcases h with ⟨C₀, C₀_pos, N, hbound⟩
  rcases Nat.func_le_mul_func_of_lt f N hg with ⟨C₁, C₁_pos, hlt⟩
  use C₀ + C₁
  constructor
  . exact add_pos_of_pos_of_nonneg C₀_pos (zero_le C₁)
  . intro n
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
  /- T is monotone -/
  T_monotone : Monotone T
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

private def supremum (T : ℕ → ℕ) (n : ℕ) : Σ' M, (∀ k ≤ n, T k ≤ M) ∧ (∃ m ≤ n, T m = M) :=
  match n with
    | 0 => by {
        use T 0
        constructor
        . intro k hk
          apply Nat.eq_zero_of_le_zero at hk
          rw [hk]
        . use 0
      }
    | Nat.succ n => by {
        rcases supremum T n with ⟨M₀, hn, hm⟩
        use T (n+1) ⊔ M₀
        constructor
        . intro k hk
          if k_eq_n_succ : k ≠ n.succ then {
            have k_lt_n_succ := Nat.lt_of_le_of_ne hk k_eq_n_succ
            have k_le_n := Nat.le_of_lt_succ k_lt_n_succ
            specialize hn k k_le_n
            apply le_trans hn
            apply le_max_right
          }
          else {
            simp at k_eq_n_succ
            rw [k_eq_n_succ]
            apply le_max_left
          }
        . rcases hm with ⟨m, hm1, hm2⟩
          if hM₀ : M₀ ≤ T (n + 1) then {
            use n + 1
            constructor
            . exact le_refl n.succ
            . symm
              exact max_eq_left hM₀
          }
          else {
            simp at hM₀
            use m
            constructor
            . exact le_trans hm1 (Nat.le_succ n)
            . rw [hm2]
              symm
              exact max_eq_right (le_of_lt hM₀)
          }
      }


private def monotonize (T : ℕ → ℕ) : Σ' U, T ≤ U ∧ Monotone U := by
  use fun n ↦ (supremum T n).1
  constructor
  . intro n
    simp
    exact (supremum T n).2.1 n (le_refl n)
  . unfold Monotone
    intro n m hle
    simp
    rcases (supremum T n).2 with ⟨hn, n', n'_le_n, hn'⟩
    rcases (supremum T m).2 with ⟨hm, m', m'_le_m, hm'⟩
    rw [← hm', ← hn']
    specialize hm n' (le_trans n'_le_n hle)
    rw [← hm'] at hm
    exact hm


variable {T f : ℕ → ℕ} {a b : ℕ}

lemma b_pos (self: MasterRecurrence T a b f) : b > 0 := lt_trans one_pos self.one_lt_b 
 
def repeat_subst (self: MasterRecurrence T a b f) (k : ℕ) (hk : k > 0) : 
    MasterRecurrence (fun n ↦ T (n + b)) (a^k) (b^k) (fun n ↦ (GeometricSum 1 (a/b^self.d) (k - 1)).ceil.toNat * f (n + b)) :=
  {
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

      suffices T (n + b) ≤ a ^ k * T (n / b ^ k + b) + (GeometricSum 1 (↑a / ↑b ^ self.d) (k - 1)).ceil.toNat * f (n + b) by {
        apply le_add_of_le_add_right this
        apply Nat.mul_le_mul_left
        apply self.T_monotone
        simp
        rw [← Nat.floorDiv_eq_div]
        exact floorDiv_le_ceilDiv
      }

      have rec_apply := self.T_rec (n + b) (le_add_right (le_of_mul_le_of_one_le_left hn (pow_pos self.b_pos k)))
      have rec_div : a * T ((n + b) ⌈/⌉ b) ≤ a * T ((n + b) / b + 1) := by {
        apply Nat.mul_le_mul_left
        apply self.T_monotone
        exact Nat.ceilDiv_le_div_succ self.b_pos
      }

      apply flip le_add_of_le_add_right rec_div at rec_apply
      rw [Nat.add_div self.b_pos, Nat.div_self self.b_pos] at rec_apply
      split_ifs at rec_apply with hrec_mod <;> simp at hrec_mod
      . contrapose hrec_mod
        intro hmod
        have hcontra := Nat.mod_lt n self.b_pos
        exact not_le_of_lt hcontra hmod 
      . simp at rec_apply
        rw [add_assoc, one_add_one_eq_two] at rec_apply
        have rec_T_le_n_add_b : a * T (n / b + 2) ≤ a * T (n / b + b) := by {
          apply Nat.mul_le_mul_left
          apply self.T_monotone
          exact add_le_add (le_refl (n / b)) self.one_lt_b
        }
        apply flip le_add_of_le_add_right rec_T_le_n_add_b at rec_apply
        
        generalize S_def : (fun n ↦ T (n + b)) = S
        have S_apply : ∀ (n : ℕ), T (n + b) = S n := by {
          intro n
          rw [← S_def]
        }
        generalize g_def : (fun n ↦ f (n + b)) = g
        have g_apply : ∀ (n : ℕ), f (n + b) = g n := by {
          intro n
          rw [← g_def]
        }
        rw [S_apply, S_apply, g_apply] at rec_apply
        rw [S_apply, S_apply, g_apply]

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
      . have add_b_poly : (fun n ↦ (n + b)^self.d) ∈ O ℕ fun n ↦ n^self.d := by {
          unfold O AsympBoundedAbove AsympLE AsympProperty
          simp
          sorry
        }

        suffices f_of_add_b_poly : (fun n ↦ f (n + b)) ∈ O ℕ fun n ↦ (n + b)^self.d by {
          exact O_trans ℕ f_of_add_b_poly add_b_poly
        }

        unfold O
        simp
        rcases self.f_poly with ⟨C, C_pos, N, hle⟩
        use C
        constructor
        . exact C_pos
        . simp
          simp at hle
          use N
          intro n n_le_N
          exact hle (n + b) (le_add_of_le_of_nonneg n_le_N (zero_le b))
    }
  }


end MasterRecurrence


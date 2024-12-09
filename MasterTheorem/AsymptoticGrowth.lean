import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Order.Defs
import Mathlib.Order.Basic
import Mathlib.Order.MinMax

def AsymptoticallyNonZero {R₁ R₂ : Type} [LinearOrderedCommRing R₁] [LinearOrderedRing R₂] (f : R₁ → R₂) :=
  ∃ N, ∀ n > N, f n ≠ 0

variable {R F : Type} [LinearOrderedCommRing R] [LinearOrderedField F]

def AsymptoticallyBoundedBelowBy (f g : R → F) := 
  ∃ k > 0, ∃ N, ∀ n > N, |f n| ≥ k * |g n|

def AsymptoticallyBoundedAboveBy (f g : R → F) := 
  ∃ k > 0, ∃ N, ∀ n > N, |f n| ≤ k * |g n|

def AsymptoticallyDominates (f g : R → F) := 
  ∀ k > 0, ∃ N, ∀ n > N, |f n| ≥ k * |g n|

def AsymptoticallyDominatedBy (f g : R → F) := 
  ∀ k > 0, ∃ N, ∀ n > N, |f n| ≤ k * |g n|

def AsymptoticallyBoundedBy (f g : R → F) :=
  ∃ k₁ > 0, ∃ k₂ > 0, ∃ N, ∀ n > N, k₁ * |g n| ≤ |f n| ∧ |f n| ≤ k₂ * |g n|

theorem asymp_dominated_implies_bounded_above (f g : R → F) (h : AsymptoticallyDominatedBy f g) : AsymptoticallyBoundedAboveBy f g := by
  unfold AsymptoticallyBoundedAboveBy
  unfold AsymptoticallyDominatedBy at h
  specialize h 1 (by linarith)
  use 1
  constructor
  . linarith
  . exact h

theorem asymp_dominates_implies_bounded_below (f g : R → F) (h : AsymptoticallyDominates f g) : AsymptoticallyBoundedBelowBy f g := by
  specialize h 1 (by linarith)
  use 1
  constructor
  . linarith
  . exact h

theorem asymp_bounded_above_and_below_implies_bounded (f g : R → F) (ha : AsymptoticallyBoundedBelowBy f g) (hb : AsymptoticallyBoundedAboveBy f g) : AsymptoticallyBoundedBy f g := by
  unfold AsymptoticallyBoundedBelowBy at ha
  unfold AsymptoticallyBoundedAboveBy at hb
  unfold AsymptoticallyBoundedBy
  rcases ha with ⟨k₁, k₁_pos, N₁, ha⟩ 
  rcases hb with ⟨k₂, k₂_pos, N₂, hb⟩ 
  use k₁
  constructor 
  . exact k₁_pos
  . use k₂
    constructor
    . exact k₂_pos
    . use max N₁ N₂
      intro n n_gt_N
      specialize ha n (lt_of_le_of_lt (le_max_left N₁ N₂) n_gt_N)
      specialize hb n (lt_of_le_of_lt (le_max_right N₁ N₂) n_gt_N)
      constructor
      . exact ha
      . exact hb

-- If f is asymptotically bounded by a function g that is nonzero for large inputs, then it is not dominated by g.
theorem asymp_bounded_implies_not_dominated (f g : R → F) (hg : AsymptoticallyNonZero g) (hb : AsymptoticallyBoundedBy f g) : ¬AsymptoticallyDominatedBy f g := by
  intro hd
  -- unfold definitions to make it clearer
  unfold AsymptoticallyBoundedBy at hb
  unfold AsymptoticallyDominatedBy at hd
  unfold AsymptoticallyNonZero at hg

  -- unwrap the existential quantifiers
  rcases hb with ⟨k₁, k₁_pos, k₂, k₂_pos, N₁, hb⟩
  rcases hg with ⟨N₂, hg⟩

  -- set k to a useful value and get the N out
  specialize hd (k₁ / 2) (by linarith)
  rcases hd with ⟨N₃, hd⟩

  -- define an N that is large enough
  generalize N_eq_N_max : max N₁ (max N₂ N₃) = N
  have N_ge_N₁ : N ≥ N₁ := by {
    rw [← N_eq_N_max]
    apply le_max_left
  }
  have N_ge_N₂ : N ≥ N₂ := by {
    rw [← N_eq_N_max, max_left_comm]
    apply le_max_left
  }
  have N_ge_N₃ : N ≥ N₃ := by {
    rw [← N_eq_N_max, ← max_comm, max_assoc, max_left_comm]
    apply le_max_left
  }

  -- use the created N on hypotheses
  specialize hb (N + 1) (by linarith)
  /- specialize ha (N + 1) (by linarith) -/
  specialize hd (N + 1) (by linarith)
  specialize hg (N + 1) (by linarith)

  -- get the absolute-value version of hg
  have hg_abs : |g (N + 1)| ≠ 0 := abs_ne_zero.2 hg
  -- split the conjunction
  rcases hb with ⟨ha, hb⟩
  -- use an alias for convenience
  generalize hG : |g (N + 1)| = G
  rw [hG] at ha hb hd hg_abs

  -- it is not entirely obvious that G is positive
  have G_nonneg : G ≥ 0 := by {
    rw [← hG]
    linarith [abs_nonneg (g (N + 1))]
  }
  symm at hg_abs
  have G_pos : G > 0 := Ne.lt_of_le hg_abs G_nonneg

  -- create a conflicting pair of inequalities and finish the proof
  have k_G_le_half : k₁ * G ≤ (k₁ * G) / 2 := by linarith
  have half_kG_lt_kG : (k₁ * G) / 2 < k₁ * G := half_lt_self (mul_pos k₁_pos G_pos)
  linarith

theorem asymp_bounded_implies_not_dominates (f g : R → F) (hg : AsymptoticallyNonZero g) (hb : AsymptoticallyBoundedBy f g) : ¬AsymptoticallyDominates f g := by
  intro hd
  -- unfold definitions to make it clearer
  unfold AsymptoticallyBoundedBy at hb
  unfold AsymptoticallyDominates at hd
  unfold AsymptoticallyNonZero at hg

  rcases hg with ⟨N₁, hg⟩
  rcases hb with ⟨k₁, k₁_pos, k₂, k₂_pos, N₂, hb⟩

  -- use a favorable value for k
  specialize hd (k₂ + 1) (by linarith)
  rcases hd with ⟨N₃, hd⟩

  -- define an N that is large enough
  generalize N_eq_N_max : max N₁ (max N₂ N₃) = N
  have N_ge_N₁ : N ≥ N₁ := by {
    rw [← N_eq_N_max]
    apply le_max_left
  }
  have N_ge_N₂ : N ≥ N₂ := by {
    rw [← N_eq_N_max, max_left_comm]
    apply le_max_left
  }
  have N_ge_N₃ : N ≥ N₃ := by {
    rw [← N_eq_N_max, ← max_comm, max_assoc, max_left_comm]
    apply le_max_left
  }

  specialize hg (N + 1) (by linarith)
  specialize hb (N + 1) (by linarith)
  specialize hd (N + 1) (by linarith)

  -- get the absolute-value version of hg
  have hg_abs : |g (N + 1)| ≠ 0 := abs_ne_zero.2 hg
  -- split the conjunction
  rcases hb with ⟨ha, hb⟩
  -- use an alias for convenience
  generalize hG : |g (N + 1)| = G
  rw [hG] at ha hb hd hg_abs

  -- it is not entirely obvious that G is positive
  have G_nonneg : G ≥ 0 := by {
    rw [← hG]
    linarith [abs_nonneg (g (N + 1))]
  }
  symm at hg_abs
  have G_pos : G > 0 := Ne.lt_of_le hg_abs G_nonneg
  linarith

theorem not_asymp_dominates_and_dominated (f g : R → F) (hg: AsymptoticallyNonZero g): ¬(AsymptoticallyDominates f g ∧ AsymptoticallyDominatedBy f g) := by
  intro h 
  rcases h with ⟨ha, hb⟩
  unfold AsymptoticallyDominates at ha
  unfold AsymptoticallyDominatedBy at hb
  unfold AsymptoticallyNonZero at hg

  specialize ha 2 (by linarith)
  specialize hb 1 (by linarith)
  rcases ha with ⟨N₁, ha⟩
  rcases hb with ⟨N₂, hb⟩
  rcases hg with ⟨N₃, hg⟩

  generalize hN : max N₁ (max N₂ N₃) = N
  have N_ge_N₁ : N ≥ N₁ := by {
    rw [← hN]
    apply le_max_left
  }
  have N_ge_N₂ : N ≥ N₂ := by {
    rw [← hN, max_comm, max_assoc]
    apply le_max_left
  }
  have N_ge_N₃ : N ≥ N₃ := by {
    rw [← hN, ← max_comm, max_assoc, max_left_comm]
    apply le_max_left
  }

  specialize ha (N + 1) (by linarith)
  specialize hb (N + 1) (by linarith)
  specialize hg (N + 1) (by linarith)
   
  -- get the absolute-value version of hg
  have hg_abs : |g (N + 1)| ≠ 0 := abs_ne_zero.2 hg
  -- use an alias for convenience
  generalize hG : |g (N + 1)| = G
  rw [hG] at ha hb hg_abs

  have G_nonneg : G ≥ 0 := by {
    rw [← hG]
    linarith [abs_nonneg (g (N + 1))]
  }
  symm at hg_abs
  have G_pos : G > 0 := Ne.lt_of_le hg_abs G_nonneg
  linarith
  
  

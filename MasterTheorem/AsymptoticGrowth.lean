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

variable {f g : R → F}

private lemma le_three_max_left {L : Type} [LinearOrder L] (a b c : L) : a ≤ a ⊔ b ⊔ c := by
  rw [max_assoc]
  apply le_max_left 

private lemma le_three_max_middle {L : Type} [LinearOrder L] (a b c : L) : b ≤ a ⊔ b ⊔ c := by
  rw [max_assoc, ← max_comm, max_assoc]
  apply le_max_left

private lemma le_three_max_right {L : Type} [LinearOrder L] (a b c : L) : c ≤ a ⊔ b ⊔ c := by
  rw [max_comm]
  apply le_max_left

theorem asymp_dominated_implies_bounded_above (h : AsymptoticallyDominatedBy f g) : AsymptoticallyBoundedAboveBy f g := by
  unfold AsymptoticallyBoundedAboveBy
  unfold AsymptoticallyDominatedBy at h
  specialize h 1 (by linarith)
  use 1
  constructor
  . linarith
  . exact h

theorem asymp_dominates_implies_bounded_below (h : AsymptoticallyDominates f g) : AsymptoticallyBoundedBelowBy f g := by
  specialize h 1 (by linarith)
  use 1
  constructor
  . linarith
  . exact h

lemma asymp_bounded_above_and_below_implies_bounded (ha : AsymptoticallyBoundedAboveBy f g) (hb : AsymptoticallyBoundedBelowBy f g) : AsymptoticallyBoundedBy f g := by
  rcases ha with ⟨k₁, k₁_pos, N₁, ha⟩ 
  rcases hb with ⟨k₂, k₂_pos, N₂, hb⟩ 
  use k₂
  constructor 
  . assumption
  . use k₁
    constructor
    . assumption
    . use max N₁ N₂
      intro n n_gt_N
      constructor
      . exact hb n (lt_of_le_of_lt (le_max_right N₁ N₂) n_gt_N)
      . exact ha n (lt_of_le_of_lt (le_max_left N₁ N₂) n_gt_N)

lemma asymp_bounded_implies_bounded_above_and_below (h : AsymptoticallyBoundedBy f g) : AsymptoticallyBoundedAboveBy f g ∧ AsymptoticallyBoundedBelowBy f g := by
  rcases h with ⟨k₁, k₁_pos, k₂, k₂_pos, N, h⟩
  constructor
  . use k₂
    constructor
    . assumption
    . use N
      intro n hn
      exact And.right (h n hn)
  . use k₁
    constructor
    . assumption
    . use N
      intro n hn
      exact And.left (h n hn)

theorem asymp_bounded_above_and_below_equiv_bounded : AsymptoticallyBoundedAboveBy f g ∧ AsymptoticallyBoundedBelowBy f g ↔ AsymptoticallyBoundedBy f g := by
  constructor
  . exact And.elim asymp_bounded_above_and_below_implies_bounded
  . exact asymp_bounded_implies_bounded_above_and_below

theorem not_asymp_bounded_and_dominated (hg : AsymptoticallyNonZero g) : ¬(AsymptoticallyBoundedBy f g ∧ AsymptoticallyDominatedBy f g) := by
  intro h
  rcases h with ⟨hb, hd⟩
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
  generalize hN : N₁ ⊔ N₂ ⊔ N₃ = N

  -- use the created N on hypotheses
  specialize hb (N + 1) (by linarith [le_three_max_left N₁ N₂ N₃])
  specialize hg (N + 1) (by linarith [le_three_max_middle N₁ N₂ N₃])
  specialize hd (N + 1) (by linarith [le_three_max_right N₁ N₂ N₃])

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

-- If f is asymptotically bounded by a function g that is nonzero for large inputs, then it is not dominated by g.
lemma asymp_bounded_implies_not_dominated (hg : AsymptoticallyNonZero g) (hb : AsymptoticallyBoundedBy f g) : ¬AsymptoticallyDominatedBy f g := by
  intro hd
  apply not_asymp_bounded_and_dominated hg
  constructor <;> assumption

lemma asymp_dominated_implies_not_bounded (hg : AsymptoticallyNonZero g) (hd : AsymptoticallyDominatedBy f g) : ¬AsymptoticallyBoundedBy f g := by 
  intro hb
  apply not_asymp_bounded_and_dominated hg
  constructor <;> assumption

theorem asymp_dominated_implies_not_bounded_below (hg : AsymptoticallyNonZero g) (hd : AsymptoticallyDominatedBy f g) : ¬AsymptoticallyBoundedBelowBy f g := by 
  intro hbbelow
  apply not_asymp_bounded_and_dominated hg
  constructor
  . have hbabove := asymp_dominated_implies_bounded_above hd
    exact asymp_bounded_above_and_below_equiv_bounded.1 (And.intro hbabove hbbelow)
  . assumption    

theorem not_asymp_bounded_and_dominates (hg : AsymptoticallyNonZero g) : ¬(AsymptoticallyBoundedBy f g ∧ AsymptoticallyDominates f g) := by
  intro h
  rcases h with ⟨hb, hd⟩
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
  generalize hN : N₁ ⊔ N₂ ⊔ N₃ = N

  specialize hg (N + 1) (by linarith [le_three_max_left N₁ N₂ N₃])
  specialize hb (N + 1) (by linarith [le_three_max_middle N₁ N₂ N₃])
  specialize hd (N + 1) (by linarith [le_three_max_right N₁ N₂ N₃])

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

lemma asymp_bounded_implies_not_dominates (hg : AsymptoticallyNonZero g) (hb : AsymptoticallyBoundedBy f g) : ¬AsymptoticallyDominates f g := by
  intro hb
  apply not_asymp_bounded_and_dominates hg
  constructor <;> assumption

lemma asymp_dominates_implies_not_bounded (hg : AsymptoticallyNonZero g) (hd : AsymptoticallyDominates f g) : ¬AsymptoticallyBoundedBy f g := by
  intro hd
  apply not_asymp_bounded_and_dominates hg
  constructor <;> assumption

theorem asymp_dominates_implies_not_bounded_above (hg : AsymptoticallyNonZero g) (hd : AsymptoticallyDominates f g) : ¬AsymptoticallyBoundedAboveBy f g := by 
  intro hbabove
  apply not_asymp_bounded_and_dominates hg
  constructor
  . have hbbelow := asymp_dominates_implies_bounded_below hd
    exact asymp_bounded_above_and_below_equiv_bounded.1 (And.intro hbabove hbbelow)
  . assumption

theorem not_asymp_dominates_and_dominated (hg: AsymptoticallyNonZero g): ¬(AsymptoticallyDominates f g ∧ AsymptoticallyDominatedBy f g) := by
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

  specialize ha (N + 1) (by linarith [le_three_max_left N₁ N₂ N₃])
  specialize hb (N + 1) (by linarith [le_three_max_middle N₁ N₂ N₃])
  specialize hg (N + 1) (by linarith [le_three_max_right N₁ N₂ N₃])
   
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



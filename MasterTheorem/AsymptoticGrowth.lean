import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Order.Defs
import Mathlib.Order.Basic

open LE

variable {L R : Type} [L_instLinOrd : LinearOrder L] [R_instLinOrdCommRing : LinearOrderedCommRing R]

def AsymptoticallyBoundedBelowBy (f g : L → R) := 
  ∃ k > 0, ∃ N, ∀ n > N, |f n| ≥ k * |g n|

def AsymptoticallyBoundedAboveBy (f g : L → R) := 
  ∃ k > 0, ∃ N, ∀ n > N, |f n| ≤ k * |g n|

def AsymptoticallyDominates (f g : L → R) := 
  ∀ k > 0, ∃ N, ∀ n > N, |f n| ≥ k * |g n|

def AsymptoticallyDominatedBy (f g : L → R) := 
  ∀ k > 0, ∃ N, ∀ n > N, |f n| ≤ k * |g n|

def AsymptoticallyBoundedBy (f g : L → R) :=
  ∃ k₁ > 0, ∃ k₂ > 0, ∃ N, ∀ n > N, k₁ * |g n| ≤ |f n| ∧ |f n| ≤ k₂ * |g n|

theorem asymp_dominated_implies_bounded_above (f g : L → R) (h : AsymptoticallyDominatedBy f g) : AsymptoticallyBoundedAboveBy f g := by
  unfold AsymptoticallyBoundedAboveBy
  unfold AsymptoticallyDominatedBy at h
  specialize h 1 (by linarith)
  use 1
  constructor
  . linarith

theorem asymp_dominates_implies_bounded_below (f g : L → R) (h : AsymptoticallyDominates f g) : AsymptoticallyBoundedBelowBy f g := by
  specialize h 1 (by linarith)
  use 1
  constructor
  . linarith

theorem asymp_bounded_above_and_below_implies_bounded (f g : L → R) (ha : AsymptoticallyBoundedBelowBy f g) (hb : AsymptoticallyBoundedAboveBy f g) : AsymptoticallyBoundedBy f g := by
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

theorem asymp_bounded_and_bounded_above_implies_not_dominated (f g : L → R) (h : AsymptoticallyBoundedBy f g) (ha : AsymptoticallyBoundedAboveBy f g) : ¬AsymptoticallyDominatedBy f g := by
  sorry

theorem asymp_bounded_and_bounded_below_implies_not_dominates (f g : L → R) (h : AsymptoticallyBoundedBy f g) (ha : AsymptoticallyBoundedBelowBy f g) : ¬AsymptoticallyDominates f g := by
  sorry

theorem not_asymp_dominates_and_dominated (f g : L → R) (h : AsymptoticallyDominates f g) (ha : AsymptoticallyDominatedBy f g) : False := by
  sorry 

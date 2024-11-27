import Mathlib.Algebra.Order.Ring.Abs

variable {L R : Type} [LinearOrder L] [LinearOrderedCommRing R]

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
  sorry

theorem asymp_dominates_implies_bounded_below (f g : L → R) (h : AsymptoticallyDominates f g) : AsymptoticallyBoundedBelowBy f g := by
  sorry

theorem asymp_bounded_above_and_below_implies_bounded (f g : L → R) (ha : AsymptoticallyBoundedAboveBy f g) (hb : AsymptoticallyBoundedBelowBy f g) : AsymptoticallyBoundedBy f g := by
  sorry

theorem asymp_bounded_and_bounded_above_implies_not_dominated (f g : L → R) (h : AsymptoticallyBoundedBy f g) (ha : AsymptoticallyBoundedAboveBy f g) : ¬AsymptoticallyDominatedBy f g := by
  sorry

theorem asymp_bounded_and_bounded_below_implies_not_dominates (f g : L → R) (h : AsymptoticallyBoundedBy f g) (ha : AsymptoticallyBoundedBelowBy f g) : ¬AsymptoticallyDominates f g := by
  sorry

theorem not_asymp_dominates_and_dominated (f g : L → R) (h : AsymptoticallyDominates f g) (ha : AsymptoticallyDominatedBy f g) : False := by
  sorry 

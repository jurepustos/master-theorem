import Mathlib.Algebra.Order.Ring.Abs

def AsymptoticallyBoundedBelowBy {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (f g : L → R) := 
  ∃ k > 0, ∃ N, ∀ n > N, |f n| ≥ k * |g n|

def AsymptoticallyBoundedAboveBy {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (f g : L → R) := 
  ∃ k > 0, ∃ N, ∀ n > N, |f n| ≤ k * |g n|

def AsymptoticallyDominates {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (f g : L → R) := 
  ∀ k > 0, ∃ N, ∀ n > N, |f n| ≥ k * |g n|

def AsymptoticallyDominatedBy {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (f g : L → R) := 
  ∀ k > 0, ∃ N, ∀ n > N, |f n| ≤ k * |g n|

def AsymptoticallyBoundedBy {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (f g : L → R) :=
  ∃ k₁ > 0, ∃ k₂ > 0, ∃ N, ∀ n > N, k₁ * |g n| ≤ |f n| ∧ |f n| ≤ k₂ * |g n|

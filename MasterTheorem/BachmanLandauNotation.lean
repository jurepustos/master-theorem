import Mathlib.Algebra.Order.Ring.Abs

import MasterTheorem.AsymptoticGrowth

def O {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (g : L → R) := 
  { f : L → R | AsymptoticallyBoundedAboveBy f g }

def Ω {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (g : L → R) := 
  { f : L → R | AsymptoticallyBoundedBelowBy f g }

def Θ {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (g : L → R) := 
  { f : L → R | AsymptoticallyBoundedBy f g }

def o {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (g : L → R) := 
  { f : L → R | AsymptoticallyDominatedBy f g }

def ω {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (g : L → R) := 
  { f : L → R | AsymptoticallyDominates f g }

theorem o_implies_O {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (f g : L → R) (h : f ∈ o g) : f ∈ O g := by
  sorry

theorem ω_implies_Ω {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (f g : L → R) (h : f ∈ ω g) : f ∈ Ω g := by
  sorry

theorem O_and_Ω_implies_Θ {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (f g : L → R) (hO : f ∈ O g) (hΩ : f ∈ Ω g) : f ∈ Θ g := by
  sorry

theorem Θ_and_O_implies_not_o {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (f g : L → R) (hΘ : f ∈ Θ g) (hO : f ∈ O g) : ¬f ∈ o g := by
  sorry

theorem Θ_and_Ω_implies_not_ω {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (f g : L → R) (hΘ : f ∈ Θ g) (hΩ : f ∈ Ω g) : ¬f ∈ ω g := by
  sorry

theorem not_o_and_ω {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (f g : L → R) (ho : f ∈ o g) (hω : f ∈ ω g) : False := by
  sorry

import Mathlib.Algebra.Order.Ring.Abs

import MasterTheorem.AsymptoticGrowth

variable {L R : Type} [LinearOrder L] [LinearOrderedCommRing R]

def O (g : L → R) := 
  { f : L → R | AsymptoticallyBoundedAboveBy f g }

def Ω (g : L → R) := 
  { f : L → R | AsymptoticallyBoundedBelowBy f g }

def Θ (g : L → R) := 
  { f : L → R | AsymptoticallyBoundedBy f g }

def o (g : L → R) := 
  { f : L → R | AsymptoticallyDominatedBy f g }

def ω (g : L → R) := 
  { f : L → R | AsymptoticallyDominates f g }

theorem o_implies_O (f g : L → R) (h : f ∈ o g) : f ∈ O g := by
  sorry

theorem ω_implies_Ω (f g : L → R) (h : f ∈ ω g) : f ∈ Ω g := by
  sorry

theorem O_and_Ω_implies_Θ (f g : L → R) (hO : f ∈ O g) (hΩ : f ∈ Ω g) : f ∈ Θ g := by
  sorry

theorem Θ_implies_not_o (f g : L → R) (hΘ : f ∈ Θ g) : ¬f ∈ o g := by
  sorry

theorem Θ_implies_not_ω (f g : L → R) (hΘ : f ∈ Θ g) : ¬f ∈ ω g := by
  sorry

theorem not_o_and_ω (f g : L → R) (ho : f ∈ o g) (hω : f ∈ ω g) : False := by
  sorry

section LinearOrder
section o

instance (f : L → R) : Preorder (o f) :=
  sorry

instance (f : L → R) : PartialOrder (o f) :=
  sorry

instance (f : L → R) : Min (o f) :=
  sorry

instance (f : L → R) : Max (o f) :=
  sorry

instance (f : L → R) : Ord (o f) :=
  sorry

instance (f : L → R) : LinearOrder (o f) :=
  sorry

end o

section O

instance (f : L → R) : Preorder (O f) :=
  sorry

instance (f : L → R) : PartialOrder (O f) :=
  sorry

instance (f : L → R) : Min (O f) :=
  sorry

instance (f : L → R) : Max (O f) :=
  sorry

instance (f : L → R) : Ord (O f) :=
  sorry

instance (f : L → R) : LinearOrder (O f) :=
  sorry

end O

section Ω

instance (f : L → R) : Preorder (Ω f) :=
  sorry

instance (f : L → R) : PartialOrder (Ω f) :=
  sorry

instance (f : L → R) : Min (Ω f) :=
  sorry

instance (f : L → R) : Max (Ω f) :=
  sorry

instance (f : L → R) : Ord (Ω f) :=
  sorry

instance (f : L → R) : LinearOrder (Ω f) :=
  sorry

end Ω

section ω

instance (f : L → R) : Preorder (ω f) :=
  sorry

instance (f : L → R) : PartialOrder (ω f) :=
  sorry

instance (f : L → R) : Min (ω f) :=
  sorry

instance (f : L → R) : Max (ω f) :=
  sorry

instance (f : L → R) : Ord (ω f) :=
  sorry

instance (f : L → R) : LinearOrder (ω f) :=
  sorry

end ω

section Θ

instance (f : L → R) : Preorder (Θ f) :=
  sorry

instance (f : L → R) : PartialOrder (Θ f) :=
  sorry

instance (f : L → R) : Min (Θ f) :=
  sorry

instance (f : L → R) : Max (Θ f) :=
  sorry

instance (f : L → R) : Ord (Θ f) :=
  sorry

instance (f : L → R) : LinearOrder (Θ f) :=
  sorry

end Θ
end LinearOrder

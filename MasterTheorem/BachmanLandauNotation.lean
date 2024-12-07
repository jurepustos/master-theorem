import Mathlib.Algebra.Order.Ring.Abs

import MasterTheorem.AsymptoticGrowth

variable {R F : Type} [LinearOrderedCommRing R] [LinearOrderedField F]

def O (g : R → F) := 
  { f : R → F | AsymptoticallyBoundedAboveBy f g }

def Ω (g : R → F) := 
  { f : R → F | AsymptoticallyBoundedBelowBy f g }

def Θ (g : R → F) := 
  { f : R → F | AsymptoticallyBoundedBy f g }

def o (g : R → F) := 
  { f : R → F | AsymptoticallyDominatedBy f g }

def ω (g : R → F) := 
  { f : R → F | AsymptoticallyDominates f g }

theorem o_implies_O (f g : R → F) (h : f ∈ o g) : f ∈ O g := by
  sorry

theorem ω_implies_Ω (f g : R → F) (h : f ∈ ω g) : f ∈ Ω g := by
  sorry

theorem O_and_Ω_implies_Θ (f g : R → F) (hO : f ∈ O g) (hΩ : f ∈ Ω g) : f ∈ Θ g := by
  sorry

theorem Θ_implies_not_o (f g : R → F) (hΘ : f ∈ Θ g) : ¬f ∈ o g := by
  sorry

theorem Θ_implies_not_ω (f g : R → F) (hΘ : f ∈ Θ g) : ¬f ∈ ω g := by
  sorry

theorem not_o_and_ω (f g : R → F) (ho : f ∈ o g) (hω : f ∈ ω g) : False := by
  sorry

section LinearOrder
section o

instance (f : R → F) : Preorder (o f) :=
  sorry

instance (f : R → F) : PartialOrder (o f) :=
  sorry

instance (f : R → F) : Min (o f) :=
  sorry

instance (f : R → F) : Max (o f) :=
  sorry

instance (f : R → F) : Ord (o f) :=
  sorry

instance (f : R → F) : LinearOrder (o f) :=
  sorry

end o

section O

instance (f : R → F) : Preorder (O f) :=
  sorry

instance (f : R → F) : PartialOrder (O f) :=
  sorry

instance (f : R → F) : Min (O f) :=
  sorry

instance (f : R → F) : Max (O f) :=
  sorry

instance (f : R → F) : Ord (O f) :=
  sorry

instance (f : R → F) : LinearOrder (O f) :=
  sorry

end O

section Ω

instance (f : R → F) : Preorder (Ω f) :=
  sorry

instance (f : R → F) : PartialOrder (Ω f) :=
  sorry

instance (f : R → F) : Min (Ω f) :=
  sorry

instance (f : R → F) : Max (Ω f) :=
  sorry

instance (f : R → F) : Ord (Ω f) :=
  sorry

instance (f : R → F) : LinearOrder (Ω f) :=
  sorry

end Ω

section ω

instance (f : R → F) : Preorder (ω f) :=
  sorry

instance (f : R → F) : PartialOrder (ω f) :=
  sorry

instance (f : R → F) : Min (ω f) :=
  sorry

instance (f : R → F) : Max (ω f) :=
  sorry

instance (f : R → F) : Ord (ω f) :=
  sorry

instance (f : R → F) : LinearOrder (ω f) :=
  sorry

end ω

section Θ

instance (f : R → F) : Preorder (Θ f) :=
  sorry

instance (f : R → F) : PartialOrder (Θ f) :=
  sorry

instance (f : R → F) : Min (Θ f) :=
  sorry

instance (f : R → F) : Max (Θ f) :=
  sorry

instance (f : R → F) : Ord (Θ f) :=
  sorry

instance (f : R → F) : LinearOrder (Θ f) :=
  sorry

end Θ
end LinearOrder

import Mathlib.Algebra.Order.Ring.Abs

import MasterTheorem.AsymptoticGrowth

variable {R F : Type} [LinearOrderedCommRing R] [LinearOrderedField F]

def O (g : R → F) := 
  { f : R → F | AsymptoticallyNonZero g ∧ AsymptoticallyBoundedAboveBy f g }

def Ω (g : R → F) := 
  { f : R → F | AsymptoticallyNonZero g ∧ AsymptoticallyBoundedBelowBy f g }

def Θ (g : R → F) := 
  { f : R → F | AsymptoticallyNonZero g ∧ AsymptoticallyBoundedBy f g }

def o (g : R → F) := 
  { f : R → F | AsymptoticallyNonZero g ∧ AsymptoticallyDominatedBy f g }

def ω (g : R → F) := 
  { f : R → F | AsymptoticallyNonZero g ∧ AsymptoticallyDominates f g }

section BasicRelations

variable {f g : R → F}

theorem o_implies_O (h : f ∈ o g) : f ∈ O g := by
  unfold o at h
  unfold O
  rcases h with ⟨hg, hd⟩
  constructor
  . assumption
  . exact asymp_dominated_implies_bounded_above hd

theorem ω_implies_Ω (h : f ∈ ω g) : f ∈ Ω g := by
  unfold ω at h
  unfold Ω
  rcases h with ⟨hg, hd⟩
  constructor
  . assumption
  . exact asymp_dominates_implies_bounded_below hd

theorem O_and_Ω_equiv_Θ : f ∈ O g ∧ f ∈ Ω g ↔ f ∈ Θ g := by
  unfold O
  unfold Ω
  unfold Θ
  constructor
  . intro h
    rcases h with ⟨⟨hg, hO⟩, ⟨_, hΩ⟩⟩
    constructor
    . assumption
    . exact asymp_bounded_above_and_below_equiv_bounded.1 (And.intro hO hΩ)
  . intro h
    rcases h with ⟨_, h⟩
    have hbound := asymp_bounded_above_and_below_equiv_bounded.2 h
    constructor <;> constructor
    . assumption
    . exact And.left hbound
    . assumption
    . exact And.right hbound

theorem Θ_implies_not_o (hΘ : f ∈ Θ g) : ¬f ∈ o g := by
  intro ho
  unfold Θ at hΘ
  unfold o at ho
  rcases hΘ with ⟨hg, hΘ⟩
  rcases ho with ⟨_, ho⟩
  exact asymp_bounded_implies_not_dominated hg hΘ ho

theorem Θ_implies_not_ω (hΘ : f ∈ Θ g) : ¬f ∈ ω g := by
  intro hω
  unfold Θ at hΘ
  unfold ω at hω
  rcases hΘ with ⟨hg, hΘ⟩
  rcases hω with ⟨_, hω⟩
  exact asymp_bounded_implies_not_dominates hg hΘ hω

theorem not_o_and_ω : ¬(f ∈ o g ∧ f ∈ ω g) := by
  intro h
  rcases h with ⟨ho, hω⟩
  unfold o at ho
  unfold ω at hω
  rcases ho with ⟨hg, ho⟩
  rcases hω with ⟨_, hω⟩
  apply not_asymp_dominates_and_dominated hg
  constructor <;> assumption

end BasicRelations

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

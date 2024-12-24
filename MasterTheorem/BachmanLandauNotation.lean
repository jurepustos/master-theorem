import MasterTheorem.AsymptoticGrowth
import Mathlib.Data.Set.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Order.Defs
import Mathlib.Order.Basic
import Mathlib.Order.MinMax
import Mathlib.Tactic.Ring

variable {α β γ : Type*} [LE α] [LE β] [LT γ] [Zero γ] [SMul γ β]

def O (g : α → β) := 
  { f : α → β | AsympBoundedAbove γ f g }

def Ω (g : α → β) := 
  { f : α → β | AsympBoundedBelow γ f g }

def Θ (g : α → β) := 
  { f : α → β | AsympBounded γ f g }

def o (g : α → β) := 
  { f : α → β | AsympRightDom γ f g }

def ω (g : α → β) := 
  { f : α → β | AsympLeftDom γ f g }

section BasicRelations

variable {α β γ : Type*} {f g : α → β} 

section PartialOrdered

variable [Preorder α] [Preorder β] [LinearOrderedSemiring γ] [SMul γ β]

theorem o_imp_O (h : f ∈ @o _ _ γ _ _ _ _ _ g) : f ∈ @O _ _ γ _ _ _ _ _ g := by
  have hd : AsympRightDom γ f g := h
  have hbound := asymp_right_dom_imp_bounded_above hd
  rcases hbound with ⟨k, k_pos, hbound⟩
  use k

theorem ω_imp_Ω (h : f ∈ @ω _ _ γ _ _ _ _ _ g) : f ∈ @Ω _ _ γ _ _ _ _ _ g := by
  have hd : AsympLeftDom γ f g := h
  have hbound := asymp_left_dom_imp_bounded_below hd
  rcases hbound with ⟨k, k_pos, hbound⟩
  use k

theorem O_and_Ω_imp_Θ (hO : f ∈ @O _ _ γ _ _ _ _ _ g) (hΩ : f ∈ @Ω _ _ γ _ _ _ _ _ g) : f ∈ @Θ _ _ γ _ _ _ _ _ g := by
  have ha : AsympBoundedAbove γ f g := hO
  have hb : AsympBoundedBelow γ f g := hΩ
  have hbound := asymp_bounded_above_and_below_imp_bounded ha hb
  constructor <;> tauto

theorem Θ_imp_O_and_Ω (hΘ : f ∈ @Θ _ _ γ _ _ _ _ _ g) : f ∈ @O _ _ γ _ _ _ _ _ g ∧ f ∈ @Ω _ _ γ _ _ _ _ _ g := by
  have hbound := asymp_bounded_imp_bounded_above_and_below hΘ
  rcases hbound with ⟨⟨k₁, _⟩, ⟨k₂, _⟩⟩
  constructor
  . use k₁
  . use k₂

theorem O_and_Ω_equiv_Θ : f ∈ @O _ _ γ _ _ _ _ _ g ∧ f ∈ @Ω _ _ γ _ _ _ _ _ g ↔ f ∈ @Θ _ _ γ _ _ _ _ _ g := by
  constructor <;> intro h
  . rcases h with ⟨hO, hΩ⟩
    exact O_and_Ω_imp_Θ hO hΩ
  . exact Θ_imp_O_and_Ω h

end PartialOrdered

section LinearOrdered

variable [LinearOrder α] [PartialOrder β] [AddCommMonoid β] [LinearOrderedField γ] [Module γ β] [SMulPosStrictMono γ β] 

theorem not_Θ_and_o [PosSMulMono γ β] (hg : AsympPos g) : ¬(f ∈ @Θ _ _ γ _ _ _ _ _ g ∧ f ∈ @o _ _ γ _ _ _ _ _ g) := by
  intro hb
  rcases hb with ⟨⟨_, hΩ⟩, ho⟩ 
  have hbound : AsympBoundedBelow γ f g := hΩ
  have hdom : AsympRightDom γ f g := ho
  exact not_asymp_bounded_below_and_right_dom hg (And.intro hbound hdom)

theorem Θ_imp_not_o [PosSMulMono γ β] (hg : AsympPos g) (hΘ : f ∈ @Θ _ _ γ _ _ _ _ _ g) : ¬f ∈ @o _ _ γ _ _ _ _ _ g := by
  intro ho
  exact not_Θ_and_o hg (And.intro hΘ ho)

theorem Ω_imp_not_o [PosSMulMono γ β] (hg : AsympPos g) (hΩ : f ∈ @Ω _ _ γ _ _ _ _ _ g) : ¬(f ∈ @o _ _ γ _ _ _ _ _ g) := by
  intro ho
  have hd : AsympRightDom γ f g := ho
  have hb : AsympBoundedBelow γ f g := hΩ
  exact asymp_bounded_below_imp_not_right_dom hg hb hd

theorem o_imp_not_Θ [PosSMulMono γ β] (hg : AsympPos g) (ho : f ∈ @o _ _ γ _ _ _ _ _ g) : ¬(f ∈ @Θ _ _ γ _ _ _ _ _ g) := by
  intro hΘ
  exact not_Θ_and_o hg (And.intro hΘ ho)

theorem o_imp_not_Ω [PosSMulMono γ β] (hg : AsympPos g) (ho : f ∈ @o _ _ γ _ _ _ _ _ g) : ¬(f ∈ @Ω _ _ γ _ _ _ _ _ g) := by
  intro hΩ
  have hd : AsympRightDom γ f g := ho
  have hb : AsympBoundedBelow γ f g := hΩ
  exact asymp_right_dom_imp_not_bounded_below hg hd hb

theorem not_Θ_and_ω [PosSMulMono γ β] (hg : AsympPos g) : ¬(f ∈ @Θ _ _ γ _ _ _ _ _ g ∧ f ∈ @ω _ _ γ _ _ _ _ _ g) := by
  intro h
  rcases h with ⟨⟨hO, _⟩, hω⟩
  have hb : AsympBoundedAbove γ f g := hO
  have hd : AsympLeftDom γ f g := hω
  exact not_asymp_bounded_above_and_left_dom hg (And.intro hb hd)

theorem Θ_imp_not_ω [PosSMulMono γ β] (hg : AsympPos g)(hΘ : f ∈ @Θ _ _ γ _ _ _ _ _ g) : ¬f ∈ @ω _ _ γ _ _ _ _ _ g := by
  intro hω
  exact not_Θ_and_ω hg (And.intro hΘ hω)

theorem not_o_and_ω [PosSMulStrictMono γ β] (hg : AsympPos g) : ¬(f ∈ @o _ _ γ _ _ _ _ _ g ∧ f ∈ @ω _ _ γ _ _ _ _ _ g) := by
  intro h
  rcases h with ⟨ho, hω⟩
  have ha : AsympRightDom γ f g := ho
  have hb : AsympLeftDom γ f g := hω
  exact not_asymp_left_dom_and_right_dom hg (And.intro hb ha)

end LinearOrdered

end BasicRelations


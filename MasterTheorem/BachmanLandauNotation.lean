import MasterTheorem.AsymptoticGrowth
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Order.Defs
import Mathlib.Order.Basic
import Mathlib.Order.MinMax

section Defs

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

end Defs


section Conversions

variable {α β γ : Type*} {f g : α → β} 

section Simple

variable [Preorder α] [Preorder β] [LinearOrderedSemiring γ] [SMul γ β]

lemma o_imp_O (h : f ∈ @o _ _ γ _ _ _ _ _ g) : f ∈ @O _ _ γ _ _ _ _ _ g := by
  have hd : AsympRightDom γ f g := h
  have hbound := asymp_right_dom_imp_bounded_above hd
  rcases hbound with ⟨k, k_pos, hbound⟩
  use k

lemma ω_imp_Ω (h : f ∈ @ω _ _ γ _ _ _ _ _ g) : f ∈ @Ω _ _ γ _ _ _ _ _ g := by
  have hd : AsympLeftDom γ f g := h
  have hbound := asymp_left_dom_imp_bounded_below hd
  rcases hbound with ⟨k, k_pos, hbound⟩
  use k

lemma O_Ω_imp_Θ (hO : f ∈ @O _ _ γ _ _ _ _ _ g) (hΩ : f ∈ @Ω _ _ γ _ _ _ _ _ g) : f ∈ @Θ _ _ γ _ _ _ _ _ g := by
  have ha : AsympBoundedAbove γ f g := hO
  have hb : AsympBoundedBelow γ f g := hΩ
  have hbound := asymp_bounded_above_below_imp ha hb
  constructor <;> tauto

lemma Θ_imp_O_Ω (hΘ : f ∈ @Θ _ _ γ _ _ _ _ _ g) : f ∈ @O _ _ γ _ _ _ _ _ g ∧ f ∈ @Ω _ _ γ _ _ _ _ _ g := by
  have hbound := asymp_bounded_imp_above_below hΘ
  rcases hbound with ⟨⟨k₁, _⟩, ⟨k₂, _⟩⟩
  constructor 
  . use k₁
  . use k₂

theorem O_and_Ω_iff_Θ : f ∈ @O _ _ γ _ _ _ _ _ g ∧ f ∈ @Ω _ _ γ _ _ _ _ _ g ↔ f ∈ @Θ _ _ γ _ _ _ _ _ g := by
  constructor <;> intro h
  . exact O_Ω_imp_Θ h.1 h.2
  . exact Θ_imp_O_Ω h

end Simple


section Pos

variable [LinearOrder α] [PartialOrder β] [AddCommMonoid β] [LinearOrderedField γ] [Module γ β] [SMulPosStrictMono γ β] 

theorem not_pos_Θ_and_o (hg : AsympPos g) : ¬(f ∈ @Θ _ _ γ _ _ _ _ _ g ∧ f ∈ @o _ _ γ _ _ _ _ _ g) := by
  intro hb
  rcases hb with ⟨⟨_, hΩ⟩, ho⟩ 
  have hbound : AsympBoundedBelow γ f g := hΩ
  have hdom : AsympRightDom γ f g := ho
  exact not_pos_asymp_bounded_below_and_right_dom hg (And.intro hbound hdom)

theorem pos_Θ_imp_not_o [PosSMulMono γ β] (hg : AsympPos g) (hΘ : f ∈ @Θ _ _ γ _ _ _ _ _ g) : ¬f ∈ @o _ _ γ _ _ _ _ _ g := by
  intro ho
  exact not_pos_Θ_and_o hg (And.intro hΘ ho)

theorem pos_Ω_imp_not_o [PosSMulMono γ β] (hg : AsympPos g) (hΩ : f ∈ @Ω _ _ γ _ _ _ _ _ g) : ¬(f ∈ @o _ _ γ _ _ _ _ _ g) := by
  intro ho
  have hd : AsympRightDom γ f g := ho
  have hb : AsympBoundedBelow γ f g := hΩ
  exact pos_asymp_bounded_below_imp_not_right_dom hg hb hd

theorem pos_o_imp_not_Θ [PosSMulMono γ β] (hg : AsympPos g) (ho : f ∈ @o _ _ γ _ _ _ _ _ g) : ¬(f ∈ @Θ _ _ γ _ _ _ _ _ g) := by
  intro hΘ
  exact not_pos_Θ_and_o hg (And.intro hΘ ho)

theorem pos_o_imp_not_Ω [PosSMulMono γ β] (hg : AsympPos g) (ho : f ∈ @o _ _ γ _ _ _ _ _ g) : ¬(f ∈ @Ω _ _ γ _ _ _ _ _ g) := by
  intro hΩ
  have hd : AsympRightDom γ f g := ho
  have hb : AsympBoundedBelow γ f g := hΩ
  exact pos_asymp_right_dom_imp_not_bounded_below hg hd hb

theorem not_pos_Θ_and_ω [PosSMulMono γ β] (hg : AsympPos g) : ¬(f ∈ @Θ _ _ γ _ _ _ _ _ g ∧ f ∈ @ω _ _ γ _ _ _ _ _ g) := by
  intro h
  rcases h with ⟨⟨hO, _⟩, hω⟩
  have hb : AsympBoundedAbove γ f g := hO
  have hd : AsympLeftDom γ f g := hω
  exact not_pos_asymp_bounded_above_and_left_dom hg (And.intro hb hd)

theorem pos_Θ_imp_not_ω [PosSMulMono γ β] (hg : AsympPos g)(hΘ : f ∈ @Θ _ _ γ _ _ _ _ _ g) : ¬f ∈ @ω _ _ γ _ _ _ _ _ g := by
  intro hω
  exact not_pos_Θ_and_ω hg (And.intro hΘ hω)

theorem not_pos_o_and_ω [PosSMulStrictMono γ β] (hg : AsympPos g) : ¬(f ∈ @o _ _ γ _ _ _ _ _ g ∧ f ∈ @ω _ _ γ _ _ _ _ _ g) := by
  intro h
  rcases h with ⟨ho, hω⟩
  have ha : AsympRightDom γ f g := ho
  have hb : AsympLeftDom γ f g := hω
  exact not_pos_asymp_left_dom_and_right_dom hg (And.intro hb ha)

end Pos

end Conversions


section Properties

variable {α β γ : Type*}

section Refl

variable [LinearOrder α] [Preorder β] [PartialOrder γ] [One α] [γ_monoid : MonoidWithZero γ] 
         [MulAction γ β] [ZeroLEOneClass γ] [@NeZero γ γ_monoid.toZero γ_monoid.one] {f : α → β}

theorem Θ_refl : f ∈ @Θ _ _ γ _ _ _ _ _ f := by
  exact asymp_bounded_refl

theorem O_refl : f ∈ @O _ _ γ _ _ _ _ _ f := by
  exact asymp_bounded_above_refl

theorem Ω_refl : f ∈ @Ω _ _ γ _ _ _ _ _ f := by
  exact asymp_bounded_below_refl

end Refl


section SMul

variable {c : γ} {f g : α → β} 

section Pos

variable [LinearOrder α] [Preorder β] [PartialOrder γ] [MonoidWithZero γ] [MulAction γ β] [PosMulStrictMono γ] [PosSMulMono γ β] 

lemma O_pos_smul (hc : c > 0) (h : f ∈ @O _ _ γ _ _ _ _ _ g) : (fun n ↦ c • f n) ∈ @O _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_above_pos_smul hc h

lemma Ω_pos_smul (hc : c > 0) (h : f ∈ @Ω _ _ γ _ _ _ _ _ g) : (fun n ↦ c • f n) ∈ @Ω _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_below_pos_smul hc h

theorem Θ_pos_smul (hc : c > 0) (h : f ∈ @Θ _ _ γ _ _ _ _ _ g) : (fun n ↦ c • f n) ∈ @Θ _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_pos_smul hc h

end Pos


section Neg

variable [Preorder α] [OrderedAddCommGroup β] [OrderedRing γ] [Module γ β] 
         [AddLeftStrictMono γ] [PosMulStrictMono γ] [PosSMulMono γ β] [PosSMulReflectLE γ β] 

lemma O_neg_smul (hc : c < 0) (h : f ∈ @O _ _ γ _ _ _ _ _ g) : (fun n ↦ c • f n) ∈ @Ω _ _ γ _ _ _ _ _ (fun n ↦ - g n) := by
  exact asymp_bounded_above_neg_smul hc h

lemma Ω_neg_smul (hc : c < 0) (h : f ∈ @Ω _ _ γ _ _ _ _ _ g) : (fun n ↦ c • f n) ∈ @O _ _ γ _ _ _ _ _ (fun n ↦ - g n) := by
  exact asymp_bounded_below_neg_smul hc h

theorem Θ_neg_smul (hc : c < 0) (h : f ∈ @Θ _ _ γ _ _ _ _ _ g) : (fun n ↦ c • f n) ∈ @Θ _ _ γ _ _ _ _ _ (fun n ↦ - g n) := by
  exact asymp_bounded_neg_smul hc h

end Neg

end SMul


section Add

variable {α β γ : Type*} [LinearOrder α] [Preorder β] [AddCommMonoid β] [AddLeftMono β] 
         [LinearOrderedSemiring γ] [Module γ β] {f₁ f₂ g : α → β} 

lemma O_add (ha : f₁ ∈ @O _ _ γ _ _ _ _ _ g) (hb : f₂ ∈ @O _ _ γ _ _ _ _ _ g) : (fun n ↦ f₁ n + f₂ n) ∈ @O _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_above_add ha hb

lemma Ω_add (ha : f₁ ∈ @Ω _ _ γ _ _ _ _ _ g) (hb : f₂ ∈ @Ω _ _ γ _ _ _ _ _ g) : (fun n ↦ f₁ n + f₂ n) ∈ @Ω _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_below_add ha hb

theorem Θ_add (ha : f₁ ∈ @Θ _ _ γ _ _ _ _ _ g) (hb : f₂ ∈ @Θ _ _ γ _ _ _ _ _ g) : (fun n ↦ f₁ n + f₂ n) ∈ @Θ _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_add ha hb

lemma Ω_add_pos (hf : AsympPos f₂) (h : f₁ ∈ @Ω _ _ γ _ _ _ _ _ g) : (fun n ↦ f₁ n + f₂ n) ∈ @Ω _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_below_add_pos hf h

lemma O_add_neg (hf : AsympNeg f₂) (h : f₁ ∈ @O _ _ γ _ _ _ _ _ g) : (fun n ↦ f₁ n + f₂ n) ∈ @O _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_above_add_neg hf h

theorem Θ_add_pos_O (hf : AsympPos f₂) (ha : f₁ ∈ @Θ _ _ γ _ _ _ _ _ g) (hb : f₂ ∈ @O _ _ γ _ _ _ _ _ g) : (fun n ↦ f₁ n + f₂ n) ∈ @Θ _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_add_pos_above hf ha hb

theorem Θ_add_neg_Ω (hf : AsympNeg f₂) (ha : f₁ ∈ @Θ _ _ γ _ _ _ _ _ g) (hb : f₂ ∈ @Ω _ _ γ _ _ _ _ _ g) : (fun n ↦ f₁ n + f₂ n) ∈ @Θ _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_add_neg_below hf ha hb

theorem Θ_add_pos_o (hf : AsympPos f₂) (ha : f₁ ∈ @Θ _ _ γ _ _ _ _ _ g) (hb : f₂ ∈ @o _ _ γ _ _ _ _ _ g) : (fun n ↦ f₁ n + f₂ n) ∈ @Θ _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_add_pos_right_dom hf ha hb

theorem Θ_add_neg_ω (hf : AsympNeg f₂) (ha : f₁ ∈ @Θ _ _ γ _ _ _ _ _ g) (hb : f₂ ∈ @ω _ _ γ _ _ _ _ _ g) : (fun n ↦ f₁ n + f₂ n) ∈ @Θ _ _ γ _ _ _ _ _ g := by
  exact asymp_bounded_add_neg_left_dom hf ha hb

end Add

end Properties

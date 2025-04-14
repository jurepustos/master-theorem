import MasterTheorem.AsymptoticGrowth
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Order.Defs
import Mathlib.Order.Basic
import Mathlib.Order.MinMax

variable {α β : Type*} (γ : Type* := by exact β)

section Defs

variable [LE α] [LE β] [LT γ] [Zero γ] [SMul γ β]

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

variable {α β : Type*} (γ : Type* := by exact β) {f g : α → β} 

section Simple

variable [Preorder α] [Preorder β] [LinearOrderedSemiring γ] [SMul γ β]

lemma O_of_o (h : f ∈ o γ g) : f ∈ O γ g := by
  apply asymp_bounded_above_of_right_dom
  apply h

lemma Ω_of_ω (h : f ∈ ω γ g) : f ∈ Ω γ g := by
  apply asymp_bounded_below_of_left_dom
  apply h

lemma O_Ω_Θ_iff : f ∈ O γ g ∧ f ∈ Ω γ g ↔ f ∈ Θ γ g := by
  apply asymp_bounded_iff

end Simple


section Pos

variable [LinearOrder α] [PartialOrder β] [AddCommMonoid β] [LinearOrderedField γ] [Module γ β] [SMulPosStrictMono γ β] 

lemma not_pos_Θ_and_o (hg : AsympPos g) : ¬(f ∈ Θ γ g ∧ f ∈ o γ g) := by
  intro hb
  rcases hb with ⟨⟨_, hΩ⟩, ho⟩ 
  have hbound : AsympBoundedBelow γ f g := hΩ
  have hdom : AsympRightDom γ f g := ho
  exact not_asymp_pos_bounded_below_and_right_dom hg (And.intro hbound hdom)

lemma not_pos_o_of_Θ [PosSMulMono γ β] (hg : AsympPos g) (hΘ : f ∈ Θ γ g) : ¬f ∈ o γ g := by
  intro ho
  exact not_pos_Θ_and_o γ hg (And.intro hΘ ho)

lemma not_pos_Θ_of_o [PosSMulMono γ β] (hg : AsympPos g) (ho : f ∈ o γ g) : ¬(f ∈ Θ γ g) := by
  intro hΘ
  exact not_pos_Θ_and_o γ hg (And.intro hΘ ho)

lemma not_pos_o_of_Ω [PosSMulMono γ β] (hg : AsympPos g) (hΩ : f ∈ Ω γ g) : ¬(f ∈ o γ g) := by
  intro ho
  have hd : AsympRightDom γ f g := ho
  have hb : AsympBoundedBelow γ f g := hΩ
  apply not_asymp_pos_right_dom_of_bounded_below hg hb hd

lemma not_pos_Ω_of_o [PosSMulMono γ β] (hg : AsympPos g) (ho : f ∈ o γ g) : ¬(f ∈ Ω γ g) := by
  intro hΩ
  have hd : AsympRightDom γ f g := ho
  have hb : AsympBoundedBelow γ f g := hΩ
  exact not_asymp_pos_bounded_below_of_right_dom hg hd hb

lemma not_pos_Θ_and_ω [PosSMulMono γ β] (hg : AsympPos g) : ¬(f ∈ Θ γ g ∧ f ∈ ω γ g) := by
  intro h
  rcases h with ⟨⟨hO, _⟩, hω⟩
  have hb : AsympBoundedAbove γ f g := hO
  have hd : AsympLeftDom γ f g := hω
  exact not_asymp_pos_bounded_above_and_left_dom hg (And.intro hb hd)

lemma not_pos_ω_of_Θ [PosSMulMono γ β] (hg : AsympPos g)(hΘ : f ∈ Θ γ g) : ¬f ∈ ω γ g := by
  intro hω
  exact not_pos_Θ_and_ω γ hg (And.intro hΘ hω)

lemma not_pos_Θ_of_ω [PosSMulMono γ β] (hg : AsympPos g)(hω : f ∈ ω γ g) : ¬f ∈ Θ γ g := by
  intro hΘ
  exact not_pos_Θ_and_ω γ hg (And.intro hΘ hω)

lemma not_pos_o_and_ω [PosSMulStrictMono γ β] (hg : AsympPos g) : ¬(f ∈ o γ g ∧ f ∈ ω γ g) := by
  intro h
  rcases h with ⟨ho, hω⟩
  have ha : AsympRightDom γ f g := ho
  have hb : AsympLeftDom γ f g := hω
  exact not_asymp_pos_left_and_right_dom hg (And.intro hb ha)

lemma not_pos_ω_of_o [PosSMulStrictMono γ β] (hg : AsympPos g) (ho : f ∈ o γ g) : ¬f ∈ ω γ g := by
  intro hω
  exact not_pos_o_and_ω γ hg (And.intro ho hω)

lemma not_pos_o_of_ω [PosSMulStrictMono γ β] (hg : AsympPos g) (hω : f ∈ ω γ g) : ¬f ∈ o γ g := by
  intro ho
  exact not_pos_o_and_ω γ hg (And.intro ho hω)

end Pos

end Conversions


section Properties

section Refl

variable [LinearOrder α] [Preorder β] [PartialOrder γ] [One α] [γ_monoid : MonoidWithZero γ] 
         [MulAction γ β] [ZeroLEOneClass γ] [@NeZero γ γ_monoid.toZero γ_monoid.one] {f : α → β}

lemma Θ_refl : f ∈ Θ γ f := by
  exact asymp_bounded_refl γ

lemma O_refl : f ∈ O γ f := by
  exact asymp_bounded_above_refl γ

lemma Ω_refl : f ∈ Ω γ f := by
  exact asymp_bounded_below_refl γ

end Refl


section Trans

variable [LinearOrder α] [Preorder β] {f g h : α → β}

section Bounded

variable [Preorder γ] [MonoidWithZero γ] [MulAction γ β] [PosMulStrictMono γ] [PosSMulMono γ β] 

lemma Θ_trans (ha : f ∈ Θ γ g) (hb : g ∈ Θ γ h) : f ∈ Θ γ h := by
  exact asymp_bounded_trans γ ha hb

lemma O_trans (ha : f ∈ O γ g) (hb : g ∈ O γ h) : f ∈ O γ h := by
  exact asymp_bounded_above_trans γ ha hb

lemma Ω_trans (ha : f ∈ Ω γ g) (hb : g ∈ Ω γ h) : f ∈ Ω γ h := by
  exact asymp_bounded_below_trans γ ha hb

end Bounded


section Dom

variable [PartialOrder γ] [MonoidWithZero γ] [MulAction γ β] [ZeroLEOneClass γ] [NeZero (@One.one γ _)] [PosSMulMono γ β] 

lemma o_trans (ha : f ∈ o γ g) (hb : g ∈ o γ h) : f ∈ o γ h := by
  exact asymp_right_dom_trans γ ha hb

lemma ω_trans (ha : f ∈ ω γ g) (hb : g ∈ ω γ h) : f ∈ ω γ h := by
  exact asymp_left_dom_trans γ ha hb

end Dom

end Trans


section SMul

variable {c : γ} {f g : α → β} 

section Pos

variable [LinearOrder α] [Preorder β] [PartialOrder γ] [MonoidWithZero γ] [MulAction γ β] [PosMulStrictMono γ] [PosSMulMono γ β] 

lemma O_pos_smul (hc : c > 0) (h : f ∈ O γ g) : (fun n ↦ c • f n) ∈ O γ g := by
  exact asymp_bounded_above_pos_smul γ hc h

lemma Ω_pos_smul (hc : c > 0) (h : f ∈ Ω γ g) : (fun n ↦ c • f n) ∈ Ω γ g := by
  exact asymp_bounded_below_pos_smul γ hc h

theorem Θ_pos_smul (hc : c > 0) (h : f ∈ Θ γ g) : (fun n ↦ c • f n) ∈ Θ γ g := by
  exact asymp_bounded_pos_smul γ hc h

end Pos


section Neg

variable [Preorder α] [OrderedAddCommGroup β] [OrderedRing γ] [Module γ β] 
         [AddLeftStrictMono γ] [PosMulStrictMono γ] [PosSMulMono γ β] [PosSMulReflectLE γ β] 

lemma O_neg_smul (hc : c < 0) (h : f ∈ O γ g) : (fun n ↦ c • f n) ∈ Ω γ (fun n ↦ - g n) := by
  exact asymp_bounded_above_neg_smul γ hc h

lemma Ω_neg_smul (hc : c < 0) (h : f ∈ Ω γ g) : (fun n ↦ c • f n) ∈ O γ (fun n ↦ - g n) := by
  exact asymp_bounded_below_neg_smul γ hc h

theorem Θ_neg_smul (hc : c < 0) (h : f ∈ Θ γ g) : (fun n ↦ c • f n) ∈ Θ γ (fun n ↦ - g n) := by
  exact asymp_bounded_neg_smul γ hc h

end Neg

end SMul


section Add

variable [LinearOrder α] [Preorder β] [AddCommMonoid β] [AddLeftMono β] 
         [LinearOrderedSemiring γ] [Module γ β] {f₁ f₂ g : α → β} 

lemma O_add (ha : f₁ ∈ O γ g) (hb : f₂ ∈ O γ g) : (fun n ↦ f₁ n + f₂ n) ∈ O γ g := by
  exact asymp_bounded_above_add γ ha hb

lemma Ω_add (ha : f₁ ∈ Ω γ g) (hb : f₂ ∈ Ω γ g) : (fun n ↦ f₁ n + f₂ n) ∈ Ω γ g := by
  exact asymp_bounded_below_add γ ha hb

theorem Θ_add (ha : f₁ ∈ Θ γ g) (hb : f₂ ∈ Θ γ g) : (fun n ↦ f₁ n + f₂ n) ∈ Θ γ g := by
  exact asymp_bounded_add γ ha hb

lemma Ω_add_pos (hf : AsympPos f₂) (h : f₁ ∈ Ω γ g) : (fun n ↦ f₁ n + f₂ n) ∈ Ω γ g := by
  exact asymp_bounded_below_add_pos γ hf h

lemma O_add_neg (hf : AsympNeg f₂) (h : f₁ ∈ O γ g) : (fun n ↦ f₁ n + f₂ n) ∈ O γ g := by
  exact asymp_bounded_above_add_neg γ hf h

theorem Θ_add_pos_O (hf : AsympPos f₂) (ha : f₁ ∈ Θ γ g) (hb : f₂ ∈ O γ g) : (fun n ↦ f₁ n + f₂ n) ∈ Θ γ g := by
  exact asymp_bounded_add_pos_above γ hf ha hb

theorem Θ_add_neg_Ω (hf : AsympNeg f₂) (ha : f₁ ∈ Θ γ g) (hb : f₂ ∈ Ω γ g) : (fun n ↦ f₁ n + f₂ n) ∈ Θ γ g := by
  exact asymp_bounded_add_neg_below γ hf ha hb

theorem Θ_add_pos_o (hf : AsympPos f₂) (ha : f₁ ∈ Θ γ g) (hb : f₂ ∈ o γ g) : (fun n ↦ f₁ n + f₂ n) ∈ Θ γ g := by
  exact asymp_bounded_add_pos_right_dom γ hf ha hb

theorem Θ_add_neg_ω (hf : AsympNeg f₂) (ha : f₁ ∈ Θ γ g) (hb : f₂ ∈ ω γ g) : (fun n ↦ f₁ n + f₂ n) ∈ Θ γ g := by
  exact asymp_bounded_add_neg_left_dom γ hf ha hb

end Add

end Properties

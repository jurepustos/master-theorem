import MasterTheorem.AsymptoticGrowth
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Order.Basic
import Mathlib.Order.MinMax

variable {α : Type*} {β : Type*}

section Defs

variable (γ : Type*) [LE α] [LE β] [LT γ] [Zero γ] [SMul γ β]

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


variable {γ : Type*}

section Conversions

variable {f g : α → β} 

section Simple

variable [Preorder α] [Preorder β] [Semiring γ] [LinearOrder γ] [SMul γ β]

lemma O_of_o [IsStrictOrderedRing γ] (h : f ∈ o γ g) : f ∈ O γ g := by
  apply asymp_bounded_above_of_right_dom
  apply h

lemma Ω_of_ω [IsStrictOrderedRing γ] (h : f ∈ ω γ g) : f ∈ Ω γ g := by
  apply asymp_bounded_below_of_left_dom
  apply h

lemma O_Ω_Θ_iff : f ∈ O γ g ∧ f ∈ Ω γ g ↔ f ∈ Θ γ g := by
  apply asymp_bounded_iff

end Simple


section Pos

variable [LinearOrder α] [PartialOrder β] [AddCommMonoid β] [Field γ] 
  [LinearOrder γ] [IsStrictOrderedRing γ] [Module γ β] [SMulPosStrictMono γ β] 

lemma not_asymp_pos_Θ_and_o (hg : AsympPos g) : ¬(f ∈ Θ γ g ∧ f ∈ o γ g) := by
  intro hb
  rcases hb with ⟨⟨_, hΩ⟩, ho⟩ 
  have hbound : AsympBoundedBelow γ f g := hΩ
  have hdom : AsympRightDom γ f g := ho
  exact not_asymp_pos_bounded_below_and_right_dom hg (And.intro hbound hdom)

lemma not_asymp_pos_o_of_Θ [PosSMulMono γ β] (hg : AsympPos g) (hΘ : f ∈ Θ γ g) : 
    ¬f ∈ o γ g := by
  intro ho
  exact not_asymp_pos_Θ_and_o hg (And.intro hΘ ho)

lemma not_asymp_pos_Θ_of_o [PosSMulMono γ β] (hg : AsympPos g) (ho : f ∈ o γ g) : 
    ¬(f ∈ Θ γ g) := by
  intro hΘ
  exact not_asymp_pos_Θ_and_o hg (And.intro hΘ ho)

lemma not_asymp_pos_o_of_Ω [PosSMulMono γ β] (hg : AsympPos g) (hΩ : f ∈ Ω γ g) : 
    ¬(f ∈ o γ g) := by
  intro ho
  have hd : AsympRightDom γ f g := ho
  have hb : AsympBoundedBelow γ f g := hΩ
  apply not_asymp_pos_right_dom_of_bounded_below hg hb hd

lemma not_asymp_pos_Ω_of_o [PosSMulMono γ β] (hg : AsympPos g) (ho : f ∈ o γ g) : 
    ¬(f ∈ Ω γ g) := by
  intro hΩ
  replace hd : AsympRightDom γ f g := ho
  replace hb : AsympBoundedBelow γ f g := hΩ
  exact not_asymp_pos_bounded_below_of_right_dom hg hd hb

lemma not_asymp_pos_Θ_and_ω [PosSMulMono γ β] (hg : AsympPos g) : 
    ¬(f ∈ Θ γ g ∧ f ∈ ω γ g) := by
  intro h
  rcases h with ⟨⟨hO, _⟩, hω⟩
  replace hb : AsympBoundedAbove γ f g := hO
  replace hd : AsympLeftDom γ f g := hω
  exact not_asymp_pos_bounded_above_and_left_dom hg (And.intro hb hd)

lemma not_asymp_pos_ω_of_Θ [PosSMulMono γ β] (hg : AsympPos g)
    (hΘ : f ∈ Θ γ g) : ¬f ∈ ω γ g := by
  intro hω
  exact not_asymp_pos_Θ_and_ω hg (And.intro hΘ hω)

lemma not_asymp_pos_Θ_of_ω [PosSMulMono γ β] (hg : AsympPos g)
    (hω : f ∈ ω γ g) : ¬f ∈ Θ γ g := by
  intro hΘ
  exact not_asymp_pos_Θ_and_ω hg (And.intro hΘ hω)

lemma not_asymp_pos_o_and_ω [PosSMulStrictMono γ β] (hg : AsympPos g) : 
    ¬(f ∈ o γ g ∧ f ∈ ω γ g) := by
  intro h
  rcases h with ⟨ho, hω⟩
  replace ha : AsympRightDom γ f g := ho
  replace hb : AsympLeftDom γ f g := hω
  exact not_asymp_pos_left_and_right_dom hg (And.intro hb ha)

lemma not_asymp_pos_ω_of_o [PosSMulStrictMono γ β] (hg : AsympPos g) 
    (ho : f ∈ o γ g) : ¬f ∈ ω γ g := by
  intro hω
  exact not_asymp_pos_o_and_ω hg (And.intro ho hω)

lemma not_asymp_pos_o_of_ω [PosSMulStrictMono γ β] (hg : AsympPos g) 
    (hω : f ∈ ω γ g) : ¬f ∈ o γ g := by
  intro ho
  exact not_asymp_pos_o_and_ω hg (And.intro ho hω)

end Pos

end Conversions


section Properties

section Constructors

variable [LinearOrder α] [Preorder β] [PartialOrder γ]
  [γ_monoid : MonoidWithZero γ] [MulAction γ β] [ZeroLEOneClass γ] 
  [@NeZero γ γ_monoid.toZero γ_monoid.one] {f : α → β}

@[simp]
lemma Θ_refl [One α] : f ∈ Θ γ f := by
  exact asymp_bounded_refl

@[simp]
lemma O_refl [One α] : f ∈ O γ f := by
  exact asymp_bounded_above_refl

@[simp]
lemma Ω_refl [One α] : f ∈ Ω γ f := by
  exact asymp_bounded_below_refl

lemma O_of_asymp_le {g : α → β} (hle : AsympLE f g) :
    f ∈ O γ g := by
  exact asymp_bounded_above_of_asymp_le hle

lemma Ω_of_asymp_ge {g : α → β} (hle : AsympGE f g) :
     f ∈ Ω γ g := by
  exact asymp_bounded_below_of_asymp_ge hle

end Constructors


section Iff

variable [LinearOrder α] [Preorder β] [PartialOrder γ]
  [γ_monoid : MonoidWithZero γ] [MulAction γ β] {f : α → β}

@[simp]
lemma O_iff_asymp_bounded_above {g : α → β} :
    f ∈ O γ g ↔ AsympBoundedAbove γ f g := by
  rfl

@[simp]
lemma Ω_iff_asymp_bounded_below {g : α → β} :
    f ∈ Ω γ g ↔ AsympBoundedBelow γ f g := by
  rfl

@[simp]
lemma Θ_iff_asymp_bounded {g : α → β} :
    f ∈ Θ γ g ↔ AsympBounded γ f g := by
  rfl

@[simp]
lemma o_iff_asymp_right_dom {g : α → β} :
    f ∈ o γ g ↔ AsympRightDom γ f g := by
  rfl

@[simp]
lemma ω_iff_asymp_left_dom {g : α → β} :
    f ∈ ω γ g ↔ AsympLeftDom γ f g := by
  rfl

end Iff


section Trans

variable [LinearOrder α] [Preorder β] {f g h : α → β}

section Bounded

variable [Preorder γ] [MonoidWithZero γ] [MulAction γ β] [PosMulStrictMono γ] 
  [PosSMulMono γ β] 

lemma Θ_trans (ha : f ∈ Θ γ g) (hb : g ∈ Θ γ h) : f ∈ Θ γ h := by
  exact asymp_bounded_trans ha hb

lemma O_trans (ha : f ∈ O γ g) (hb : g ∈ O γ h) : f ∈ O γ h := by
  exact asymp_bounded_above_trans ha hb

lemma Ω_trans (ha : f ∈ Ω γ g) (hb : g ∈ Ω γ h) : f ∈ Ω γ h := by
  exact asymp_bounded_below_trans ha hb

end Bounded


section Dom

variable [PartialOrder γ] [MonoidWithZero γ] [MulAction γ β] [ZeroLEOneClass γ] 
  [NeZero (@One.one γ _)] [PosSMulMono γ β] 

lemma o_trans (ha : f ∈ o γ g) (hb : g ∈ o γ h) : f ∈ o γ h := by
  exact asymp_right_dom_trans ha hb

lemma ω_trans (ha : f ∈ ω γ g) (hb : g ∈ ω γ h) : f ∈ ω γ h := by
  exact asymp_left_dom_trans ha hb

end Dom

end Trans


section SMul

variable {c : γ} {f g : α → β} 

section Pos

variable [LinearOrder α] [Preorder β] [PartialOrder γ] [MonoidWithZero γ] 
  [MulAction γ β] [PosMulStrictMono γ] [PosSMulMono γ β] 

lemma O_pos_smul (hc : c > 0) (h : f ∈ O γ g) : (fun n ↦ c • f n) ∈ O γ g := by
  unfold O at h
  simp at h
  exact asymp_bounded_above_pos_smul hc h

lemma Ω_pos_smul (hc : c > 0) (h : f ∈ Ω γ g) : 
    (fun n ↦ c • f n) ∈ Ω γ g := by
  exact asymp_bounded_below_pos_smul hc h

theorem Θ_pos_smul (hc : c > 0) (h : f ∈ Θ γ g) : 
    (fun n ↦ c • f n) ∈ Θ γ g := by
  exact asymp_bounded_pos_smul hc h

end Pos


section Neg

variable [Preorder α] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] 
  [Ring γ] [PartialOrder γ] [IsOrderedRing γ] [Module γ β] [AddLeftStrictMono γ] 
  [PosMulStrictMono γ] [PosSMulMono γ β]

lemma O_neg_smul (hc : c < 0) (h : f ∈ O γ g) : 
    (fun n ↦ c • f n) ∈ Ω γ (fun n ↦ - g n) := by
  exact asymp_bounded_above_neg_smul hc h

lemma Ω_neg_smul (hc : c < 0) (h : f ∈ Ω γ g) : 
    (fun n ↦ c • f n) ∈ O γ (fun n ↦ - g n) := by
  exact asymp_bounded_below_neg_smul hc h

theorem Θ_neg_smul (hc : c < 0) (h : f ∈ Θ γ g) : 
    (fun n ↦ c • f n) ∈ Θ γ (fun n ↦ - g n) := by
  exact asymp_bounded_neg_smul hc h

end Neg

end SMul


section Add

variable [LinearOrder α] [Preorder β] [AddCommMonoid β] [AddLeftMono β] 
         [Semiring γ] [LinearOrder γ] [Module γ β] {f₁ f₂ g : α → β} 

lemma O_add [IsStrictOrderedRing γ] (ha : f₁ ∈ O γ g) (hb : f₂ ∈ O γ g) : 
    (fun n ↦ f₁ n + f₂ n) ∈ O γ g := by
  exact asymp_bounded_above_add ha hb

lemma Ω_add [IsStrictOrderedRing γ] (ha : f₁ ∈ Ω γ g) (hb : f₂ ∈ Ω γ g) : 
    (fun n ↦ f₁ n + f₂ n) ∈ Ω γ g := by
  exact asymp_bounded_below_add ha hb

theorem Θ_add [IsStrictOrderedRing γ] (ha : f₁ ∈ Θ γ g) (hb : f₂ ∈ Θ γ g) : 
    (fun n ↦ f₁ n + f₂ n) ∈ Θ γ g := by
  exact asymp_bounded_add ha hb

lemma Ω_add_pos (hf : AsympPos f₂) (h : f₁ ∈ Ω γ g) : 
    (fun n ↦ f₁ n + f₂ n) ∈ Ω γ g := by
  exact asymp_bounded_below_add_pos hf h

lemma O_add_neg (hf : AsympNeg f₂) (h : f₁ ∈ O γ g) : 
    (fun n ↦ f₁ n + f₂ n) ∈ O γ g := by
  exact asymp_bounded_above_add_neg hf h

theorem Θ_add_pos_O [IsStrictOrderedRing γ] (hf : AsympPos f₂) 
    (ha : f₁ ∈ Θ γ g) (hb : f₂ ∈ O γ g) : (fun n ↦ f₁ n + f₂ n) ∈ Θ γ g := by
  exact asymp_bounded_add_pos_above hf ha hb

theorem Θ_add_neg_Ω [IsStrictOrderedRing γ] (hf : AsympNeg f₂) 
    (ha : f₁ ∈ Θ γ g) (hb : f₂ ∈ Ω γ g) : (fun n ↦ f₁ n + f₂ n) ∈ Θ γ g := by
  exact asymp_bounded_add_neg_below hf ha hb

theorem Θ_add_pos_o [IsStrictOrderedRing γ] (hf : AsympPos f₂) 
    (ha : f₁ ∈ Θ γ g) (hb : f₂ ∈ o γ g) : (fun n ↦ f₁ n + f₂ n) ∈ Θ γ g := by
  exact asymp_bounded_add_pos_right_dom hf ha hb

theorem Θ_add_neg_ω [IsStrictOrderedRing γ] (hf : AsympNeg f₂) 
    (ha : f₁ ∈ Θ γ g) (hb : f₂ ∈ ω γ g) : (fun n ↦ f₁ n + f₂ n) ∈ Θ γ g := by
  exact asymp_bounded_add_neg_left_dom hf ha hb

end Add


section Mul

variable [Semiring β] [Ring γ] [MulAction γ β] [IsScalarTower γ β β] 
  [IsScalarTower γ γ β] [SMulCommClass γ β β] {f₁ f₂ g₁ g₂ : α → β} 

variable [LinearOrder α] [Preorder β] [MulPosMono β] [PosMulMono β] 
  [Preorder γ] [PosMulStrictMono γ]

theorem O_nonneg_mul (hf₁ : AsympNonneg f₁) 
    (hf₂ : AsympNonneg f₂) (ha : AsympBoundedAbove γ f₁ g₁) 
    (hb : AsympBoundedAbove γ f₂ g₂) : 
    AsympBoundedAbove γ (f₁ * f₂) (g₁ * g₂) := by
  exact asymp_bounded_above_nonneg_mul hf₁ hf₂ ha hb

theorem Ω_nonpos_mul [ExistsAddOfLE β] [AddRightMono β] 
    [AddRightReflectLE β] (hf₁ : AsympNonpos f₁) (hf₂ : AsympNonpos f₂) 
    (ha : AsympBoundedBelow γ f₁ g₁) (hb : AsympBoundedBelow γ f₂ g₂) : 
    AsympBoundedAbove γ (f₁ * f₂) (g₁ * g₂) := by
  exact asymp_bounded_below_nonpos_mul hf₁ hf₂ ha hb

end Mul

end Properties

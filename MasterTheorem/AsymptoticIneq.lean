import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Action
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Order.MinMax

import MasterTheorem.Aux

section Defs

def AsympProperty {α : Type*} [LE α] (p : α → Prop) :=
  ∃ N, ∀ n ≥ N, p n

def AsympNonZero {α β : Type*} [LE α] [Zero β] (f : α → β) :=
  AsympProperty (fun n ↦ f n ≠ 0)

def AsympPos {α β : Type*} [LE α] [LT β] [Zero β] (f : α → β) :=
  AsympProperty (fun n ↦ f n > 0)

def AsympNeg {α β : Type*} [LE α] [LT β] [Zero β] (f : α → β) :=
  AsympProperty (fun n ↦ f n < 0)

def AsympNonneg {α β : Type*} [LE α] [LE β] [Zero β] (f : α → β) :=
  AsympProperty (fun n ↦ f n ≥ 0)

def AsympNonpos {α β : Type*} [LE α] [LE β] [Zero β] (f : α → β) :=
  AsympProperty (fun n ↦ f n ≤ 0)

variable {α β : Type*} [LE α] [LE β]

def AsympLE (f g : α → β) :=
  AsympProperty (fun n ↦ f n ≤ g n)

def AsympGE (f g : α → β) :=
  AsympProperty (fun n ↦ f n ≥ g n)

end Defs


section AsympPosNeg

variable {α β : Type*} [LE α] [AddGroup β] {f : α → β} 

lemma asymp_neg_of_pos [LT β] [AddLeftStrictMono β] (h : AsympPos f) : 
    AsympNeg (-f) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact h

lemma asymp_pos_of_neg [LT β] [AddLeftStrictMono β] (h : AsympNeg f) : 
    AsympPos (-f) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact h

lemma asymp_nonneg_of_nonpos [LE β] [AddLeftMono β] (h : AsympNonpos f) : 
    AsympNonneg (-f) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact h

lemma asymp_nonpos_of_nonneg [LE β] [AddLeftMono β] (h : AsympNonneg f) : 
    AsympNonpos (-f) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact h

lemma asymp_nonpos_of_neg [Preorder β] [AddLeftMono β] (h : AsympNeg f) : 
    AsympNonpos f := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  exact le_of_lt h

lemma asymp_nonneg_of_pos [Preorder β] [AddLeftMono β] (h : AsympPos f) : 
    AsympNonneg f := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  exact le_of_lt h

end AsympPosNeg


section AsympLEGE

variable {α β : Type*}

section Refl

variable [LE α] [Preorder β] {f : α → β}

@[simp]
lemma asymp_le_refl [Inhabited α] : AsympLE f f := by
  use default
  intro n hn
  exact le_refl _

@[simp]
lemma asymp_ge_refl [Inhabited α] : AsympGE f f := by
  exact asymp_le_refl

lemma asymp_le_of_le_of_forall_ge {g : α → β} {N : α} (hle : ∀ n ≥ N, f n ≤ g n) : 
    AsympLE f g := by {
  use N
}

lemma asymp_ge_of_ge_of_forall_ge {g : α → β} {N : α} (hle : ∀ n ≥ N, f n ≥ g n) : 
    AsympGE f g := by {
  use N
}

end Refl


section Equivalence

variable [Preorder α] [LE β] {f g : α → β} 

lemma asymp_le_of_ge (h : AsympGE f g) : AsympLE g f := by
  rcases h with ⟨N, h⟩
  use N

lemma asymp_ge_of_le (h : AsympLE f g) : AsympGE g f := by
  exact asymp_le_of_ge h

theorem asymp_le_ge_iff : AsympLE f g ↔ AsympGE g f := by
  constructor <;> intro h
  . exact asymp_ge_of_le h
  . exact asymp_le_of_ge h

end Equivalence


section Trans

variable [LinearOrder α] [Preorder β] {f g h : α → β}

lemma asymp_le_trans (ha : AsympLE f g) (hb : AsympLE g h) : AsympLE f h := by
  rcases ha with ⟨N₁, ha⟩
  rcases hb with ⟨N₂, hb⟩
  use N₁ ⊔ N₂
  intro n hn
  specialize ha n (le_trans (le_max_left N₁ N₂) hn)
  specialize hb n (le_trans (le_max_right N₁ N₂) hn)
  exact le_trans ha hb

lemma asymp_ge_trans (ha : AsympGE f g) (hb : AsympGE g h) : AsympGE f h := by
  rw [← asymp_le_ge_iff] at *
  exact asymp_le_trans hb ha

end Trans


section PosNeg

variable [LinearOrder α] [Preorder β] [Zero β] {f g : α → β}

lemma asymp_pos_of_pos_le (hf : AsympPos f) (h : AsympLE f g) : AsympPos g := by
  rcases hf with ⟨N₁, hf⟩
  rcases h with ⟨N₂, h⟩
  use N₁ ⊔ N₂
  intro n hn
  specialize hf n (le_trans (le_max_left N₁ N₂) hn)
  specialize h n (le_trans (le_max_right N₁ N₂) hn)
  exact lt_of_lt_of_le hf h

lemma asymp_neg_of_le_neg (hg : AsympNeg g) (h : AsympLE f g) : AsympNeg f := by
  rcases hg with ⟨N₁, hg⟩
  rcases h with ⟨N₂, h⟩
  use N₁ ⊔ N₂
  intro n hn
  specialize hg n (le_trans (le_max_left N₁ N₂) hn)
  specialize h n (le_trans (le_max_right N₁ N₂) hn)
  exact lt_of_le_of_lt h hg

lemma asymp_neg_of_neg_ge (hf : AsympNeg f) (h : AsympGE f g) : AsympNeg g := by
  rw [← asymp_le_ge_iff] at h
  exact asymp_neg_of_le_neg hf h

lemma asymp_pos_of_ge_pos (hg : AsympPos g) (h : AsympGE f g) : AsympPos f := by
  rw [← asymp_le_ge_iff] at h
  exact asymp_pos_of_pos_le hg h

end PosNeg


section Add

variable [LinearOrder α] [Preorder β] {f₁ f₂ : α → β} 

lemma asymp_le_add [Add β] [AddLeftMono β] [AddRightMono β] {g₁ g₂ : α → β} 
    (ha : AsympLE f₁ g₁) (hb : AsympLE f₂ g₂) : 
    AsympLE (f₁ + f₂) (g₁ + g₂) := by
  rcases ha with ⟨N₁, ha⟩
  rcases hb with ⟨N₂, hb⟩
  use N₁ ⊔ N₂
  intro n hn
  simp
  specialize ha n (le_trans (le_max_left _ _) hn)
  specialize hb n (le_trans (le_max_right _ _) hn)
  exact add_le_add ha hb

lemma asymp_ge_add [Add β] [AddLeftMono β] [AddRightMono β] {g₁ g₂ : α → β} 
    (ha : AsympGE f₁ g₁) (hb : AsympGE f₂ g₂) : 
    AsympGE (f₁ + f₂) (g₁ + g₂) := by
  rw [← asymp_le_ge_iff] at *
  exact asymp_le_add ha hb

lemma asymp_ge_add_pos [AddMonoid β] [AddLeftMono β] [AddRightMono β] 
    {g : α → β} (hf : AsympPos f₂) (h : AsympGE f₁ g) : 
    AsympGE (f₁ + f₂) g := by
  rcases h with ⟨N₁, h⟩
  rcases hf with ⟨N₂, hf₂⟩
  use N₁ ⊔ N₂
  intro n hn
  simp
  specialize h n (le_trans (le_max_left  _ _) hn)
  specialize hf₂ n (le_trans (le_max_right _ _) hn)
  have sum := add_le_add h (le_of_lt hf₂)
  simp at sum
  exact sum

lemma asymp_le_add_neg [AddMonoid β] [AddLeftMono β] [AddRightMono β] 
    {g : α → β} (hf : AsympNeg f₂) (h : AsympLE f₁ g) : 
    AsympLE (f₁ + f₂) g := by
  rcases h with ⟨N₁, h⟩
  rcases hf with ⟨N₂, hf₂⟩
  use N₁ ⊔ N₂
  intro n hn
  simp
  specialize h n (le_trans (le_max_left  _ _) hn)
  specialize hf₂ n (le_trans (le_max_right _ _) hn)
  have sum := add_le_add h (le_of_lt hf₂)
  simp at sum
  exact sum

end Add


section SMul

variable {γ : Type*} {f g : α → β} [Preorder α] 

section Pos

variable {c : γ} [Preorder β] [Preorder γ] [MonoidWithZero γ] [MulAction γ β] 
  [PosSMulMono γ β] 
  
lemma asymp_le_nonneg_smul (hc : c ≥ 0) (h : AsympLE f g) : 
    AsympLE (c • f) (c • g) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  simp
  specialize h n hn
  exact smul_le_smul_of_nonneg_left h hc

lemma asymp_le_pos_smul (hc : c > 0) (h : AsympLE f g) :
    AsympLE (c • f) (c • g) := asymp_le_nonneg_smul (le_of_lt hc) h

lemma asymp_ge_nonneg_smul (hc : c ≥ 0) (h : AsympGE f g) : 
    AsympGE (c • f) (c • g) := by
  rw [← asymp_le_ge_iff]
  exact asymp_le_nonneg_smul hc h

lemma asymp_ge_pos_smul (hc : c > 0) (h : AsympGE f g) :
    AsympGE (c • f) (c • g) := asymp_ge_nonneg_smul (le_of_lt hc) h

end Pos


section Neg

variable {c : γ} [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] 
    [Ring γ] [PartialOrder γ] [IsOrderedRing γ] [Module γ β] [PosSMulMono γ β] 

theorem asymp_le_nonpos_smul (hc : c ≤ 0) (h : AsympLE f g) : 
    AsympGE (fun n ↦ c • f n) (fun n ↦ c • g n) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact smul_le_smul_of_nonpos_left h hc

lemma asymp_le_neg_smul (hc : c < 0) (h : AsympLE f g) :
    AsympGE (c • f) (c • g) := asymp_le_nonpos_smul (le_of_lt hc) h

theorem asymp_ge_nonpos_smul (hc : c ≤ 0) (h : AsympGE f g) : 
    AsympLE (fun n ↦ c • f n) (fun n ↦ c • g n) := by
  rw [asymp_le_ge_iff]
  exact asymp_le_nonpos_smul hc h

lemma asymp_ge_neg_smul (hc : c < 0) (h : AsympGE f g) :
    AsympLE (c • f) (c • g) := asymp_ge_nonpos_smul (le_of_lt hc) h

end Neg

end SMul


section Mul

variable [LinearOrder α] [Preorder β]

theorem asymp_le_nonneg_mul [MonoidWithZero β] [MulPosMono β] [PosMulMono β] 
    {f₁ f₂ g₁ g₂ : α → β} (hf₁ : AsympNonneg f₁) (hf₂ : AsympNonneg f₂) 
    (ha : AsympLE f₁ g₁) (hb : AsympLE f₂ g₂) : 
    AsympLE (f₁ * f₂) (g₁ * g₂) := by 
  rcases ha with ⟨N₁, ha⟩
  rcases hb with ⟨N₂, hb⟩
  rcases hf₁ with ⟨N₃, hf₁⟩
  rcases hf₂ with ⟨N₄, hf₂⟩
  use N₁ ⊔ N₂ ⊔ N₃ ⊔ N₄
  intro n hn
  specialize ha n (le_trans (le_four_max_fst _ _ _ _) hn)
  specialize hb n (le_trans (le_four_max_snd _ _ _ _) hn)
  specialize hf₁ n (le_trans (le_four_max_thrd _ _ _ _) hn)
  specialize hf₂ n (le_trans (le_four_max_frth _ _ _ _) hn)
  exact mul_le_mul ha hb hf₂ (le_trans hf₁ ha)

theorem asymp_ge_nonpos_mul [Semiring β] [ExistsAddOfLE β] [AddRightMono β] 
    [AddRightReflectLE β] [MulPosMono β] [PosMulMono β] {f₁ f₂ g₁ g₂ : α → β} 
    (hf₁ : AsympNonpos f₁) (hf₂ : AsympNonpos f₂) (ha : AsympGE f₁ g₁) 
    (hb : AsympGE f₂ g₂) : AsympLE (f₁ * f₂) (g₁ * g₂) := by 
  rcases ha with ⟨N₁, ha⟩
  rcases hb with ⟨N₂, hb⟩
  rcases hf₁ with ⟨N₃, hf₁⟩
  rcases hf₂ with ⟨N₄, hf₂⟩
  use N₁ ⊔ N₂ ⊔ N₃ ⊔ N₄
  intro n hn
  specialize ha n (le_trans (le_four_max_fst _ _ _ _) hn)
  specialize hb n (le_trans (le_four_max_snd _ _ _ _) hn)
  specialize hf₁ n (le_trans (le_four_max_thrd _ _ _ _) hn)
  specialize hf₂ n (le_trans (le_four_max_frth _ _ _ _) hn)
  have hg₁ : g₁ n ≤ 0 := le_trans ha hf₁
  have hg₂ : g₂ n ≤ 0 := le_trans hb hf₂

  simp
  simp at ha hb
  exact mul_le_mul_of_nonpos_of_nonpos ha hb hg₁ hf₂

end Mul

end AsympLEGE

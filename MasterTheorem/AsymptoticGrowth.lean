import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Action
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Order.Defs
import Mathlib.Order.Basic
import Mathlib.Order.MinMax

section Defs

private def AsympProperty {α : Type*} [LE α] (p : α → Prop) :=
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

variable {α β : Type*} [LE α] [LE β] (γ : Type*) [LT γ] [Zero γ] [SMul γ β]  

def AsympLE (f g : α → β) :=
  AsympProperty (fun n ↦ f n ≤ g n)

def AsympGE (f g : α → β) :=
  AsympProperty (fun n ↦ f n ≥ g n)

def AsympBoundedAbove (f g : α → β) := 
  ∃ k : γ, k > 0 ∧ AsympLE f (fun n ↦ k • g n)

def AsympBoundedBelow (f g : α → β) :=
  ∃ k : γ, k > 0 ∧ AsympGE f (fun n ↦ k • g n)

def AsympBounded (f g : α → β) :=
  AsympBoundedAbove γ f g ∧ AsympBoundedBelow γ f g

def AsympRightDom (f g : α → β) :=
  ∀ k : γ, k > 0 → AsympLE f (fun n ↦ k • g n)

def AsympLeftDom (f g : α → β) :=
  ∀ k : γ, k > 0 → AsympGE f (fun n ↦ k • g n)

end Defs


section ThreeMax

variable {α : Type*} [LinearOrder α]

private lemma le_three_max_left (a b c : α) : a ≤ a ⊔ b ⊔ c := by
  rw [max_assoc]
  apply le_max_left 

private lemma le_three_max_middle (a b c : α) : b ≤ a ⊔ b ⊔ c := by
  rw [max_assoc, ← max_comm, max_assoc]
  apply le_max_left

private lemma le_three_max_right (a b c : α) : c ≤ a ⊔ b ⊔ c := by
  rw [max_comm]
  apply le_max_left

end ThreeMax


section FourMax

variable {α : Type*} [LinearOrder α]

private lemma le_four_max_fst (a b c d : α) : a ≤ a ⊔ b ⊔ c ⊔ d := by
  rw [max_assoc]
  apply le_three_max_left 

private lemma le_four_max_snd (a b c d : α) : b ≤ a ⊔ b ⊔ c ⊔ d := by
  rw [max_assoc, max_assoc, max_comm]
  apply le_three_max_left

private lemma le_four_max_thrd (a b c d : α) : c ≤ a ⊔ b ⊔ c ⊔ d := by
  rw [max_assoc, max_comm]
  apply le_three_max_left

private lemma le_four_max_frth (a b c d : α) : d ≤ a ⊔ b ⊔ c ⊔ d := by
  rw [max_comm]
  apply le_max_left

end FourMax


section AsympPosNeg

variable {α β : Type*} [LE α] [AddGroup β] {f : α → β} 

lemma asymp_neg_of_pos [LT β] [AddLeftStrictMono β] (h : AsympPos f) : AsympNeg (-f) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact h

lemma asymp_pos_of_neg [LT β] [AddLeftStrictMono β] (h : AsympNeg f) : AsympPos (-f) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact h

lemma asymp_nonneg_of_nonpos [LE β] [AddLeftMono β] (h : AsympNonpos f) : AsympNonneg (-f) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact h

lemma asymp_nonpos_of_nonneg [LE β] [AddLeftMono β] (h : AsympNonneg f) : AsympNonpos (-f) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact h

lemma asymp_nonpos_of_neg [Preorder β] [AddLeftMono β] (h : AsympNeg f) : AsympNonpos f := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  exact le_of_lt h

lemma asymp_nonneg_of_pos [Preorder β] [AddLeftMono β] (h : AsympPos f) : AsympNonneg f := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  exact le_of_lt h

end AsympPosNeg


section AsympLEGE

variable {α β : Type*}

section Refl

variable [LE α] [Inhabited α] [Preorder β] {f : α → β}

lemma asymp_le_refl : AsympLE f f := by
  use default
  intro n hn
  exact le_refl _

lemma asymp_ge_refl : AsympGE f f := by
  exact asymp_le_refl

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


section Add

variable [LinearOrder α] [Preorder β] {f₁ f₂ : α → β} 

lemma asymp_le_add [Add β] [AddLeftMono β] [AddRightMono β] {g₁ g₂ : α → β} (ha : AsympLE f₁ g₁) (hb : AsympLE f₂ g₂) : AsympLE (f₁ + f₂) (g₁ + g₂) := by
  rcases ha with ⟨N₁, ha⟩
  rcases hb with ⟨N₂, hb⟩
  use N₁ ⊔ N₂
  intro n hn
  simp
  specialize ha n (le_trans (le_max_left _ _) hn)
  specialize hb n (le_trans (le_max_right _ _) hn)
  exact add_le_add ha hb

lemma asymp_ge_add [Add β] [AddLeftMono β] [AddRightMono β] {g₁ g₂ : α → β} (ha : AsympGE f₁ g₁) (hb : AsympGE f₂ g₂) : AsympGE (f₁ + f₂) (g₁ + g₂) := by
  rw [← asymp_le_ge_iff] at *
  exact asymp_le_add ha hb

lemma asymp_ge_add_pos [AddMonoid β] [AddLeftMono β] [AddRightMono β] {g : α → β} (hf : AsympPos f₂) (h : AsympGE f₁ g) : AsympGE (f₁ + f₂) g := by
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

lemma asymp_le_add_neg [AddMonoid β] [AddLeftMono β] [AddRightMono β] {g : α → β} (hf : AsympNeg f₂) (h : AsympLE f₁ g) : AsympLE (f₁ + f₂) g := by
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

variable {c : γ} [Preorder β] [Preorder γ] [MonoidWithZero γ] [MulAction γ β] [PosSMulMono γ β] 
  
lemma asymp_le_pos_smul (hc : c > 0) (h : AsympLE f g) : AsympLE (c • f) (c • g) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  simp
  specialize h n hn
  exact smul_le_smul_of_nonneg_left h (le_of_lt hc)

lemma asymp_ge_pos_smul (hc : c > 0) (h : AsympGE f g) : AsympGE (c • f) (c • g) := by
  rw [← asymp_le_ge_iff]
  exact asymp_le_pos_smul hc h

end Pos


section Neg

variable {c : γ} [OrderedAddCommGroup β] [OrderedRing γ] [Module γ β] [PosSMulMono γ β] [PosSMulReflectLE γ β] 

theorem asymp_le_neg_smul (hc : c < 0) (h : AsympLE f g) : AsympGE (fun n ↦ c • f n) (fun n ↦ c • g n) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact (smul_le_smul_iff_of_neg_left hc).2 h

theorem asymp_ge_neg_smul (hc : c < 0) (h : AsympGE f g) : AsympLE (fun n ↦ c • f n) (fun n ↦ c • g n) := by
  rw [asymp_le_ge_iff]
  exact asymp_le_neg_smul hc h

end Neg

end SMul


section Mul

variable [LinearOrder α] [Preorder β]

lemma asymp_le_nonneg_mul_nonneg [MonoidWithZero β] [MulPosMono β] [PosMulMono β] {f₁ f₂ g₁ g₂ : α → β} (hf₁ : AsympNonneg f₁) (hf₂ : AsympNonneg f₂) (ha : AsympLE f₁ g₁) (hb : AsympLE f₂ g₂) : AsympLE (f₁ * f₂) (g₁ * g₂) := by 
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

end Mul

end AsympLEGE


section Conversions

variable {α β γ : Type*} {f g : α → β}

section Simple

variable [Preorder α] [Preorder β] [LinearOrderedSemiring γ] [SMul γ β]

lemma asymp_right_dom_imp_bounded_above (h : AsympRightDom γ f g) : AsympBoundedAbove γ f g := by
  specialize h 1 
  use 1
  constructor
  . exact one_pos
  . exact h one_pos

lemma asymp_left_dom_imp_bounded_below (h : AsympLeftDom γ f g) : AsympBoundedBelow γ f g := by
  specialize h 1
  use 1
  constructor
  . exact one_pos
  . exact h one_pos

lemma asymp_bounded_above_below_imp (ha : AsympBoundedAbove γ f g) (hb : AsympBoundedBelow γ f g) : AsympBounded γ f g := by
  rcases ha with ⟨k₁, k₁_pos, N₁, ha⟩ 
  rcases hb with ⟨k₂, k₂_pos, N₂, hb⟩ 
  constructor
  . use k₁
    constructor 
    . assumption
    . use N₁
  . use k₂
    constructor
    . assumption
    . use N₂

lemma asymp_bounded_imp_above_below (h : AsympBounded γ f g) : AsympBoundedAbove γ f g ∧ AsympBoundedBelow γ f g := by
  rcases h with ⟨⟨k₁, k₁_pos, N₁, ha⟩, ⟨k₂, k₁_pos, N₂, hb⟩⟩
  constructor
  . use k₁
    constructor
    . assumption
    . use N₁
  . use k₂
    constructor
    . assumption
    . use N₂

theorem asymp_bounded_above_below_iff : AsympBoundedAbove γ f g ∧ AsympBoundedBelow γ f g ↔ AsympBounded γ f g := by
  constructor
  . exact And.elim asymp_bounded_above_below_imp
  . exact asymp_bounded_imp_above_below

end Simple


section Pos

variable [LinearOrder α] [PartialOrder β] [AddCommMonoid β] [LinearOrderedField γ] [Module γ β] [SMulPosStrictMono γ β] 

theorem not_pos_asymp_bounded_below_and_right_dom (hg : AsympPos g) : ¬(AsympBoundedBelow γ f g ∧ AsympRightDom γ f g) := by
  intro h
  rcases h with ⟨hb, hd⟩

  -- unwrap the existential quantifiers
  rcases hb with ⟨k₁, k₁_pos, N₁, hb⟩
  rcases hg with ⟨N₂, hg⟩

  -- set k to a useful value and get the N out
  generalize hk₂ : k₁ / 2 = k₂
  have k₂_pos : k₂ > 0 := by linarith
  specialize hd k₂ k₂_pos
  rcases hd with ⟨N₃, hd⟩

  -- define an N that is large enough
  generalize hN : N₁ ⊔ N₂ ⊔ N₃ = N

  -- use the created N on hypotheses
  specialize hb N
  specialize hg N
  specialize hd N
  rw [← hN] at hb hd hg
  specialize hb (le_three_max_left N₁ N₂ N₃)
  specialize hg (le_three_max_middle N₁ N₂ N₃)
  specialize hd (le_three_max_right N₁ N₂ N₃)
  rw [hN] at hb hd hg
  rw [← hk₂] at *

  simp at hb hd

  -- create a conflicting pair of inequalities and finish the proof
  have contra1 := le_trans hb hd
  have contra2 : (k₁ / 2) • g N < k₁ • g N := smul_lt_smul_of_pos_right (by linarith) hg
  exact not_le_of_gt contra2 contra1

-- If f is asymptotically bounded by a function g that is nonzero for large inputs, then it is not right_dom by g.
theorem pos_asymp_bounded_below_imp_not_right_dom (hg : AsympPos g) (hb : AsympBoundedBelow γ f g) : ¬AsympRightDom γ f g := by
  intro hd
  exact not_pos_asymp_bounded_below_and_right_dom hg (And.intro hb hd)

theorem pos_asymp_right_dom_imp_not_bounded_below (hg : AsympPos g) (hd : AsympRightDom γ f g) : ¬AsympBoundedBelow γ f g := by 
  intro hb
  exact not_pos_asymp_bounded_below_and_right_dom hg (And.intro hb hd)

theorem not_pos_asymp_bounded_above_and_left_dom (hg : AsympPos g) : ¬(AsympBoundedAbove γ f g ∧ AsympLeftDom γ f g) := by
  intro h
  rcases h with ⟨hb, hd⟩
  rcases hg with ⟨N₁, hg⟩
  rcases hb with ⟨k₁, k₁_pos, N₂, ha⟩

  -- use a favorable value for k
  generalize hk₂ : k₁ + 1 = k₂
  have k₂_pos : k₂ > 0 := by linarith
  specialize hd k₂ k₂_pos
  rcases hd with ⟨N₃, hd⟩
  rw [← hk₂] at k₂_pos hd

  -- define an N that is large enough
  generalize hN : N₁ ⊔ N₂ ⊔ N₃ = N

  specialize ha N
  specialize hg N
  specialize hd N
  rw [← hN] at ha hd hg
  specialize hg (le_three_max_left N₁ N₂ N₃)
  specialize ha (le_three_max_middle N₁ N₂ N₃)
  specialize hd (le_three_max_right N₁ N₂ N₃)
  rw [hN] at ha hd hg
  simp at ha hd

  simp at *
  have contra1 := le_trans hd ha
  have contra2 : k₁ • g N < (k₁ + 1) • g N := smul_lt_smul_of_pos_right (by linarith) hg
  exact not_le_of_gt contra2 contra1

theorem pos_asymp_bounded_above_imp_not_left_dom (hg : AsympPos g) (hb : AsympBoundedAbove γ f g) : ¬AsympLeftDom γ f g := by
  intro hd
  exact not_pos_asymp_bounded_above_and_left_dom hg (And.intro hb hd)

theorem pos_asymp_left_dom_imp_not_bounded_above (hg : AsympPos g) (hd : AsympLeftDom γ f g) : ¬AsympBoundedAbove γ f g := by
  revert hd
  contrapose
  simp
  exact pos_asymp_bounded_above_imp_not_left_dom hg

theorem not_pos_asymp_left_dom_and_right_dom (hg: AsympPos g): ¬(AsympLeftDom γ f g ∧ AsympRightDom γ f g) := by
  intro h 
  rcases h with ⟨ha, hb⟩

  specialize ha 2 two_pos
  specialize hb 1 one_pos
  rcases ha with ⟨N₁, ha⟩
  rcases hb with ⟨N₂, hb⟩
  rcases hg with ⟨N₃, hg⟩

  generalize hN : N₁ ⊔ N₂ ⊔ N₃ = N

  specialize ha N
  specialize hb N
  specialize hg N
  rw [← hN] at ha hb hg
  specialize ha (le_three_max_left N₁ N₂ N₃)
  specialize hb (le_three_max_middle N₁ N₂ N₃)
  specialize hg (le_three_max_right N₁ N₂ N₃)
  rw [hN] at ha hb hg

  simp at ha hb hg
  have contra1 : g N < (@OfNat.ofNat γ 2 _) • g N := (lt_smul_iff_one_lt_left hg).2 one_lt_two
  have contra2 := le_trans ha hb
  exact not_le_of_gt contra1 contra2

end Pos

end Conversions


section Properties

variable {α β γ : Type*}

section Refl

variable [LinearOrder α] [Preorder β] [PartialOrder γ] [One α] [γ_monoid : MonoidWithZero γ] 
         [MulAction γ β] [ZeroLEOneClass γ] [@NeZero γ γ_monoid.toZero γ_monoid.one] {f : α → β}

lemma asymp_bounded_refl : AsympBounded γ f f := by
  constructor <;>
  . use 1
    constructor
    . exact one_pos
    . use 1
      intro _ _
      simp

lemma asymp_bounded_above_refl : AsympBoundedAbove γ f f := by
  exact asymp_bounded_refl.1

lemma asymp_bounded_below_refl : AsympBoundedBelow γ f f := by
  exact asymp_bounded_refl.2

end Refl


section SMul

variable {c : γ} {f g : α → β} 

section Pos

variable [LinearOrder α] [Preorder β] [PartialOrder γ] [MonoidWithZero γ] [MulAction γ β] [PosMulStrictMono γ] [PosSMulMono γ β] 

lemma asymp_bounded_above_pos_smul (hc : c > 0) (h : AsympBoundedAbove γ f g) : AsympBoundedAbove γ (fun n ↦ c • f n) g := by
  rcases h with ⟨k, k_pos, h⟩ 
  use c * k
  constructor
  . exact mul_pos hc k_pos
  . simp [mul_smul]
    exact asymp_le_pos_smul hc h

lemma asymp_bounded_below_pos_smul (hc : c > 0) (h : AsympBoundedBelow γ f g) : AsympBoundedBelow γ (fun n ↦ c • f n) g := by
  rcases h with ⟨k, k_pos, h⟩ 
  use c * k
  constructor
  . exact mul_pos hc k_pos
  . rw [← asymp_le_ge_iff]
    rw [← asymp_le_ge_iff] at h
    simp [mul_smul]
    exact asymp_le_pos_smul hc h

theorem asymp_bounded_pos_smul (hc : c > 0) (h : AsympBounded γ f g) : AsympBounded γ (fun n ↦ c • f n) g := by
  rcases h with ⟨ha, hb⟩
  constructor
  . exact asymp_bounded_above_pos_smul hc ha
  . exact asymp_bounded_below_pos_smul hc hb

end Pos


section Neg

variable [Preorder α] [OrderedAddCommGroup β] [OrderedRing γ] [Module γ β] 
         [AddLeftStrictMono γ] [PosMulStrictMono γ] [PosSMulMono γ β] [PosSMulReflectLE γ β] 

lemma asymp_bounded_above_neg_smul (hc : c < 0) (h : AsympBoundedAbove γ f g) : AsympBoundedBelow γ (fun n ↦ c • f n) (fun n ↦ - g n) := by
  rcases h with ⟨k, k_pos, h⟩  
  use -c * k
  constructor
  . exact mul_pos (neg_pos_of_neg hc) k_pos
  . rw [← asymp_le_ge_iff]
    simp [mul_smul]
    suffices AsympGE (fun n ↦ c • f n) (fun n ↦ c • k • g n) by {
      rcases this with ⟨N, h⟩
      use N
    }
    exact asymp_le_neg_smul hc h

lemma asymp_bounded_below_neg_smul (hc : c < 0) (h : AsympBoundedBelow γ f g) : AsympBoundedAbove γ (fun n ↦ c • f n) (fun n ↦ - g n) := by
  rcases h with ⟨k, k_pos, h⟩  
  use -c * k
  constructor
  . exact mul_pos (neg_pos_of_neg hc) k_pos
  . simp [mul_smul]
    rw [asymp_le_ge_iff]
    suffices AsympLE (fun n ↦ c • f n) (fun n ↦ c • k • g n) by {
      rcases this with ⟨N, h⟩
      use N
    }
    exact asymp_ge_neg_smul hc h

theorem asymp_bounded_neg_smul (hc : c < 0) (h : AsympBounded γ f g) : AsympBounded γ (fun n ↦ c • f n) (fun n ↦ - g n) := by
  rcases h with ⟨ha, hb⟩
  constructor 
  . exact asymp_bounded_below_neg_smul hc hb
  . exact asymp_bounded_above_neg_smul hc ha

end Neg

end SMul


section Add

variable {α β γ : Type*} [LinearOrder α] [Preorder β] [AddCommMonoid β] [AddLeftMono β] 
         [LinearOrderedSemiring γ] [Module γ β] {f₁ f₂ g : α → β} 

lemma asymp_bounded_above_add (ha : AsympBoundedAbove γ f₁ g) (hb : AsympBoundedAbove γ f₂ g) : AsympBoundedAbove γ (f₁ + f₂) g := by
  rcases ha with ⟨k₁, k₁_pos, ha⟩
  rcases hb with ⟨k₂, k₂_pos, hb⟩
  use k₁ + k₂
  constructor
  . use lt_add_of_lt_of_pos k₁_pos k₂_pos
  . simp [add_smul]
    exact asymp_le_add ha hb

lemma asymp_bounded_below_add (ha : AsympBoundedBelow γ f₁ g) (hb : AsympBoundedBelow γ f₂ g) : AsympBoundedBelow γ (f₁ + f₂) g := by
  rcases ha with ⟨k₁, k₁_pos, ha⟩
  rcases hb with ⟨k₂, k₂_pos, hb⟩
  use k₁ + k₂
  constructor
  . use lt_add_of_lt_of_pos k₁_pos k₂_pos
  . simp [add_smul]
    exact asymp_ge_add ha hb

theorem asymp_bounded_add (ha : AsympBounded γ f₁ g) (hb : AsympBounded γ f₂ g) : AsympBounded γ (f₁ + f₂) g := by
  rcases ha with ⟨ha₁, ha₂⟩
  rcases hb with ⟨hb₁, hb₂⟩
  constructor
  . exact asymp_bounded_above_add ha₁ hb₁
  . exact asymp_bounded_below_add ha₂ hb₂

lemma asymp_bounded_below_add_pos (hf : AsympPos f₂) (h : AsympBoundedBelow γ f₁ g) : AsympBoundedBelow γ (f₁ + f₂) g := by
  rcases h with ⟨k, k_pos, h⟩
  use k
  constructor
  . exact k_pos
  . exact asymp_ge_add_pos hf h

lemma asymp_bounded_above_add_neg (hf : AsympNeg f₂) (h : AsympBoundedAbove γ f₁ g) : AsympBoundedAbove γ (f₁ + f₂) g := by
  rcases h with ⟨k, k_pos, h⟩
  use k
  constructor
  . exact k_pos
  . exact asymp_le_add_neg hf h

theorem asymp_bounded_add_pos_above (hf : AsympPos f₂) (ha : AsympBounded γ f₁ g) (hb : AsympBoundedAbove γ f₂ g) : AsympBounded γ (f₁ + f₂) g := by
  rcases ha with ⟨ha₁, ha₂⟩
  constructor
  . exact asymp_bounded_above_add ha₁ hb
  . exact asymp_bounded_below_add_pos hf ha₂

theorem asymp_bounded_add_neg_below (hf : AsympNeg f₂) (ha : AsympBounded γ f₁ g) (hb : AsympBoundedBelow γ f₂ g) : AsympBounded γ (f₁ + f₂) g := by
  rcases ha with ⟨ha₁, ha₂⟩
  constructor
  . exact asymp_bounded_above_add_neg hf ha₁
  . exact asymp_bounded_below_add ha₂ hb

theorem asymp_bounded_add_pos_right_dom (hf : AsympPos f₂) (ha : AsympBounded γ f₁ g) (hb : AsympRightDom γ f₂ g) : AsympBounded γ (f₁ + f₂) g :=
  asymp_bounded_add_pos_above hf ha (asymp_right_dom_imp_bounded_above hb)

theorem asymp_bounded_add_neg_left_dom (hf : AsympNeg f₂) (ha : AsympBounded γ f₁ g) (hb : AsympLeftDom γ f₂ g) : AsympBounded γ (f₁ + f₂) g :=
  asymp_bounded_add_neg_below hf ha (asymp_left_dom_imp_bounded_below hb)

end Add

end Properties

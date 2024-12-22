import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Action
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Order.Defs
import Mathlib.Order.Basic
import Mathlib.Order.MinMax
import Mathlib.Tactic.LinearCombination

section Definitions

def AsympNonZero {α β : Type*} [LE α] [Zero β] (f : α → β) :=
  ∃ N, ∀ n ≥ N, f n ≠ 0

def AsympPos {α β : Type*} [LE α] [LT β] [Zero β] (f : α → β) :=
  ∃ N, ∀ n ≥ N, f n > 0

def AsympNeg {α β : Type*} [LE α] [LT β] [Zero β] (f : α → β) :=
  ∃ N, ∀ n ≥ N, f n < 0

variable {α β : Type*} [LE α] [LE β] (γ : Type*) [LT γ] [Zero γ] [SMul γ β]  

def EventuallyLessThan (f g : α → β) :=
  ∃ N, ∀ n ≥ N, f n ≤ g n

def EventuallyGreaterThan (f g : α → β) :=
  ∃ N, ∀ n ≥ N, f n ≥ g n

def AsympBoundedAbove (f g : α → β) := 
  ∃ k : γ, k > 0 ∧ EventuallyLessThan f (fun n ↦ k • g n)

def AsympBoundedBelow (f g : α → β) :=
  ∃ k : γ, k > 0 ∧ EventuallyGreaterThan f (fun n ↦ k • g n)

def AsympBounded (f g : α → β) :=
  AsympBoundedAbove γ f g ∧ AsympBoundedBelow γ f g

def AsympRightDom (f g : α → β) :=
  ∀ k : γ, k > 0 → EventuallyLessThan f (fun n ↦ k • g n)

def AsympLeftDom (f g : α → β) :=
  ∀ k : γ, k > 0 → EventuallyGreaterThan f (fun n ↦ k • g n)

end Definitions

section Max

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

end Max

section BasicRelations

variable {α β γ : Type*} {f g : α → β}

section PartialOrdered

variable [Preorder α] [Preorder β] [LinearOrderedSemiring γ] [SMul γ β]

lemma asymp_right_dom_imp_bounded_above (h : AsympRightDom γ f g) : AsympBoundedAbove γ f g := by
  unfold AsympBoundedAbove
  unfold AsympRightDom at h
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

lemma asymp_bounded_above_and_below_imp_bounded (ha : AsympBoundedAbove γ f g) (hb : AsympBoundedBelow γ f g) : AsympBounded γ f g := by
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

lemma asymp_bounded_imp_bounded_above_and_below (h : AsympBounded γ f g) : AsympBoundedAbove γ f g ∧ AsympBoundedBelow γ f g := by
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

theorem asymp_bounded_above_and_below_equiv_bounded : AsympBoundedAbove γ f g ∧ AsympBoundedBelow γ f g ↔ AsympBounded γ f g := by
  constructor
  . exact And.elim asymp_bounded_above_and_below_imp_bounded
  . exact asymp_bounded_imp_bounded_above_and_below

end PartialOrdered

section LinearOrdered

variable [LinearOrder α] [PartialOrder β] [AddCommMonoid β] [LinearOrderedField γ] [Module γ β] [SMulPosStrictMono γ β] 

theorem not_asymp_bounded_below_and_right_dom (hg : AsympPos g) : ¬(AsympBoundedBelow γ f g ∧ AsympRightDom γ f g) := by
  intro h
  rcases h with ⟨hb, hd⟩

  -- unwrap the existential quantifiers
  rcases hb with ⟨k₁, k₁_pos, N₁, hb⟩
  rcases hg with ⟨N₂, hg⟩

  -- set k to a useful value and get the N out
  generalize hk₂ : k₁ / 2 = k₂
  have k₂_pos : k₂ > 0 := by linarith
  unfold AsympRightDom at hd
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
lemma asymp_bounded_below_imp_not_right_dom (hg : AsympPos g) (hb : AsympBoundedBelow γ f g) : ¬AsympRightDom γ f g := by
  intro hd
  exact not_asymp_bounded_below_and_right_dom hg (And.intro hb hd)

lemma asymp_right_dom_imp_not_bounded_below (hg : AsympPos g) (hd : AsympRightDom γ f g) : ¬AsympBoundedBelow γ f g := by 
  intro hb
  exact not_asymp_bounded_below_and_right_dom hg (And.intro hb hd)

theorem not_asymp_bounded_above_and_left_dom (hg : AsympPos g) : ¬(AsympBoundedAbove γ f g ∧ AsympLeftDom γ f g) := by
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

lemma asymp_bounded_above_imp_not_left_dom (hg : AsympPos g) (hb : AsympBoundedAbove γ f g) : ¬AsympLeftDom γ f g := by
  intro hd
  exact not_asymp_bounded_above_and_left_dom hg (And.intro hb hd)

lemma asymp_left_dom_imp_not_bounded_above (hg : AsympPos g) (hd : AsympLeftDom γ f g) : ¬AsympBoundedAbove γ f g := by
  revert hd
  contrapose
  simp
  exact asymp_bounded_above_imp_not_left_dom hg

theorem not_asymp_left_dom_and_right_dom (hg: AsympPos g): ¬(AsympLeftDom γ f g ∧ AsympRightDom γ f g) := by
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

end LinearOrdered

end BasicRelations

section Properties

section AsympBounded

variable {α β γ : Type*} {f g : α → β} [PartialOrder α] [Preorder β] [PartialOrder γ] 
         [γ_monoid : MonoidWithZero γ] [MulAction γ β] 

theorem asymp_bounded_refl [One α] [ZeroLEOneClass γ] [@NeZero γ γ_monoid.toZero γ_monoid.one] : AsympBounded γ f f := by
  constructor <;>
  . use 1
    constructor
    . exact one_pos
    . use 1
      intro _ _
      simp

theorem asymp_bounded_pos_mul [PosSMulMono γ β] [PosMulStrictMono γ] {c : γ} (hc : c > 0) (h : AsympBounded γ f g) : AsympBounded γ (fun n ↦ c • f n) g := by
  rcases h with ⟨⟨k₁, k₁_pos, N₁, ha⟩, ⟨k₂, k₂_pos, N₂, hb⟩⟩
  constructor
  . use c * k₁
    constructor
    . exact mul_pos hc k₁_pos
    . use N₁
      intro n hn
      simp
      specialize ha n hn
      simp at ha
      rw [mul_smul]
      exact smul_le_smul_of_nonneg_left ha (le_of_lt hc)
  . use c * k₂
    constructor
    . exact mul_pos hc k₂_pos
    . use N₂
      intro n hn
      simp
      specialize hb n hn
      simp at hb
      rw [mul_smul] 
      exact smul_le_smul_of_nonneg_left hb (le_of_lt hc)

theorem asymp_bounded_neg_mul [Neg β] [Neg γ] [PosSMulMono γ β] [PosMulStrictMono γ] {c : γ} (hc : c < 0) (h : AsympBounded γ f g) : AsympBounded γ (fun n ↦ c • f n) (fun n ↦ - g n) := by
  rcases h with ⟨⟨k₁, k₁_pos, N₁, ha⟩, ⟨k₂, k₂_pos, N₂, hb⟩⟩
  constructor <;> sorry

section TwoFunctions

variable {α β γ : Type*} [LinearOrder α] [Preorder β] [AddCommMonoid β] [AddLeftMono β] 
         [LinearOrderedSemiring γ] [AddLeftStrictMono γ] [Module γ β] {f₁ f₂ g : α → β} 

theorem asymp_bounded_add_bounded (ha : AsympBounded γ f₁ g) (hb : AsympBounded γ f₂ g) : AsympBounded γ (fun n ↦ f₁ n + f₂ n) g := by
  rcases ha with ⟨⟨k₁, k₁_pos, N₁, ha₁⟩, ⟨k₂, k₂_pos, N₂, ha₂⟩⟩
  rcases hb with ⟨⟨k₃, k₃_pos, N₃, hb₁⟩, ⟨k₄, k₄_pos, N₄, hb₂⟩⟩
  constructor
  . use k₁ + k₃
    constructor
    . use lt_add_of_lt_of_pos k₁_pos k₃_pos
    . use N₁ ⊔ N₃
      intro n hn
      simp
      specialize ha₁ n (le_trans (le_max_left N₁ N₃) hn)
      specialize hb₁ n (le_trans (le_max_right N₁ N₃) hn)
      simp at ha₁ hb₁
      rw [add_smul]
      exact add_le_add ha₁ hb₁
  . use k₂ + k₄
    constructor
    . use lt_add_of_lt_of_pos k₂_pos k₄_pos
    . use N₂ ⊔ N₄ 
      intro n hn
      simp
      specialize ha₂ n (le_trans (le_max_left N₂ N₄) hn)
      specialize hb₂ n (le_trans (le_max_right N₂ N₄) hn)
      simp at ha₂ hb₂
      rw [add_smul]
      exact add_le_add ha₂ hb₂

theorem asymp_bounded_add_pos_bounded_above (ha : AsympBounded γ f₁ g) (hf : AsympPos f₂) (hb : AsympBoundedAbove γ f₂ g) : AsympBounded γ (fun n ↦ f₁ n + f₂ n) g := by
  rcases ha with ⟨⟨k₁, k₁_pos, N₁, ha₁⟩, ⟨k₂, k₂_pos, N₂, ha₂⟩⟩
  rcases hb with ⟨k₃, k₃_pos, N₃, hb⟩
  constructor
  . use k₁ + k₃
    constructor
    . use lt_add_of_lt_of_pos k₁_pos k₃_pos
    . use N₁ ⊔ N₃
      intro n hn
      simp
      specialize ha₁ n (le_trans (le_max_left N₁ N₃) hn)
      specialize hb n (le_trans (le_max_right N₁ N₃) hn)
      simp at ha₁ hb
      rw [add_smul]
      exact add_le_add ha₁ hb
  . use k₂
    constructor
    . exact k₂_pos
    . rcases hf with ⟨N₄, hf₂⟩
      use N₂ ⊔ N₃ ⊔ N₄
      intro n hn
      simp
      specialize ha₂ n (le_trans (le_three_max_left _ _ _) hn)
      specialize hb n (le_trans (le_three_max_middle _ _ _) hn)
      specialize hf₂ n (le_trans (le_three_max_right _ _ _) hn)
      simp at ha₂ hb
      have sum := add_le_add ha₂ (le_of_lt hf₂)
      simp at sum
      exact sum

theorem asymp_bounded_add_neg_bounded_below (ha : AsympBounded γ f₁ g) (hf : AsympNeg f₂) (hb : AsympBoundedBelow γ f₂ g) : AsympBounded γ (fun n ↦ f₁ n + f₂ n) g := by
  rcases ha with ⟨⟨k₁, k₁_pos, N₁, ha₁⟩, ⟨k₂, k₂_pos, N₂, ha₂⟩⟩
  rcases hb with ⟨k₃, k₃_pos, N₃, hb⟩
  constructor
  . use k₁
    constructor
    . exact k₁_pos
    . rcases hf with ⟨N₄, hf₂⟩
      use N₁ ⊔ N₃ ⊔ N₄
      intro n hn
      simp
      specialize ha₁ n (le_trans (le_three_max_left _ _ _) hn)
      specialize hb n (le_trans (le_three_max_middle _ _ _) hn)
      specialize hf₂ n (le_trans (le_three_max_right _ _ _) hn)
      simp at ha₁ hb
      have sum := add_le_add ha₁ (le_of_lt hf₂)
      simp at sum
      exact sum
  . use k₂ + k₃
    constructor
    . use lt_add_of_lt_of_pos k₂_pos k₃_pos
    . use N₂ ⊔ N₃
      intro n hn
      simp
      specialize ha₂ n (le_trans (le_max_left _ _) hn)
      specialize hb n (le_trans (le_max_right _ _) hn)
      simp at ha₂ hb
      rw [add_smul]
      exact add_le_add ha₂ hb

theorem asymp_bounded_add_pos_right_dom (ha : AsympBounded γ f₁ g) (hf : AsympPos f₂) (hb : AsympRightDom γ f₂ g) : AsympBounded γ (fun n ↦ f₁ n + f₂ n) g :=
  asymp_bounded_add_pos_bounded_above ha hf (asymp_right_dom_imp_bounded_above hb)

theorem asymp_bounded_add_neg_left_dom (ha : AsympBounded γ f₁ g) (hf : AsympNeg f₂) (hb : AsympLeftDom γ f₂ g) : AsympBounded γ (fun n ↦ f₁ n + f₂ n) g :=
  asymp_bounded_add_neg_bounded_below ha hf (asymp_left_dom_imp_bounded_below hb)

end TwoFunctions

end AsympBounded

end Properties

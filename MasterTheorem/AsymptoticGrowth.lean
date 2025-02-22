import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Action
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Order.Defs
import Mathlib.Order.MinMax

import MasterTheorem.AsymptoticIneq
import MasterTheorem.Aux

variable {α β : Type*} (γ : Type* := by exact β)

section Defs

variable [LE α] [LE β] [LT γ] [Zero γ] [SMul γ β]

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


section Conversions

variable {α β γ : Type*} {f g : α → β}

section Simple

variable [Preorder α] [Preorder β] [LinearOrderedSemiring γ] [SMul γ β]

lemma asymp_bounded_above_of_right_dom (h : AsympRightDom γ f g) : AsympBoundedAbove γ f g := by
  specialize h 1 
  use 1
  constructor
  . exact one_pos
  . exact h one_pos

lemma asymp_bounded_below_of_left_dom (h : AsympLeftDom γ f g) : AsympBoundedBelow γ f g := by
  specialize h 1
  use 1
  constructor
  . exact one_pos
  . exact h one_pos

lemma asymp_bounded_iff : AsympBoundedAbove γ f g ∧ AsympBoundedBelow γ f g ↔ AsympBounded γ f g := by
  constructor <;> (
    intro h
    rcases h with ⟨ha, hb⟩
  )
  . exact And.intro ha hb
  . constructor
    . exact ha
    . exact hb

end Simple

section Pos

variable [LinearOrder α] [PartialOrder β] [AddCommMonoid β] [LinearOrderedField γ] [Module γ β] [SMulPosStrictMono γ β] 

lemma not_asymp_pos_bounded_below_and_right_dom (hg : AsympPos g) : ¬(AsympBoundedBelow γ f g ∧ AsympRightDom γ f g) := by
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
lemma not_asymp_pos_right_dom_of_bounded_below (hg : AsympPos g) (hb : AsympBoundedBelow γ f g) : ¬AsympRightDom γ f g := by
  intro hd
  exact not_asymp_pos_bounded_below_and_right_dom hg (And.intro hb hd)

lemma not_asymp_pos_bounded_below_of_right_dom (hg : AsympPos g) (hd : AsympRightDom γ f g) : ¬AsympBoundedBelow γ f g := by 
  intro hb
  exact not_asymp_pos_bounded_below_and_right_dom hg (And.intro hb hd)

lemma not_asymp_pos_bounded_above_and_left_dom (hg : AsympPos g) : ¬(AsympBoundedAbove γ f g ∧ AsympLeftDom γ f g) := by
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

lemma not_asymp_left_dom_of_bounded_above_pos (hg : AsympPos g) (hb : AsympBoundedAbove γ f g) : ¬AsympLeftDom γ f g := by
  intro hd
  exact not_asymp_pos_bounded_above_and_left_dom hg (And.intro hb hd)

lemma not_asymp_bounded_above_of_left_dom_pos (hg : AsympPos g) (hd : AsympLeftDom γ f g) : ¬AsympBoundedAbove γ f g := by
  revert hd
  contrapose
  simp
  exact not_asymp_left_dom_of_bounded_above_pos hg

lemma not_asymp_pos_left_and_right_dom (hg: AsympPos g): ¬(AsympLeftDom γ f g ∧ AsympRightDom γ f g) := by
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

lemma not_asymp_pos_left_dom_of_right_dom (hg : AsympPos g) (h : AsympRightDom γ f g) : ¬AsympLeftDom γ f g := by
  intro h1
  exact not_asymp_pos_left_and_right_dom hg (And.intro h1 h)

lemma not_asymp_pos_right_dom_of_left_dom (hg : AsympPos g) (h : AsympLeftDom γ f g) : ¬AsympRightDom γ f g := by
  intro h1
  exact not_asymp_pos_left_and_right_dom hg (And.intro h h1)

end Pos

end Conversions


section Properties

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
  exact (asymp_bounded_refl γ).1

lemma asymp_bounded_below_refl : AsympBoundedBelow γ f f := by
  exact (asymp_bounded_refl γ).2

end Refl


section Trans

variable [LinearOrder α] [Preorder β] {f g h : α → β}

section Bounded

variable [Preorder γ] [MonoidWithZero γ] [MulAction γ β] [PosMulStrictMono γ] [PosSMulMono γ β] 

lemma asymp_bounded_above_trans (ha : AsympBoundedAbove γ f g) (hb : AsympBoundedAbove γ g h) : AsympBoundedAbove γ f h := by
  rcases ha with ⟨k₁, k₁_pos, ha⟩
  rcases hb with ⟨k₂, k₂_pos, hb⟩
  use k₁ * k₂
  constructor
  . exact mul_pos k₁_pos k₂_pos
  . apply asymp_le_pos_smul k₁_pos at hb
    simp [mul_smul]
    exact asymp_le_trans ha hb

lemma asymp_bounded_below_trans (ha : AsympBoundedBelow γ f g) (hb : AsympBoundedBelow γ g h) : AsympBoundedBelow γ f h := by
  rcases ha with ⟨k₁, k₁_pos, ha⟩
  rcases hb with ⟨k₂, k₂_pos, hb⟩
  use k₁ * k₂
  constructor
  . exact mul_pos k₁_pos k₂_pos
  . apply asymp_ge_pos_smul k₁_pos at hb
    simp [mul_smul]
    exact asymp_ge_trans ha hb

lemma asymp_bounded_trans (ha : AsympBounded γ f g) (hb : AsympBounded γ g h) : AsympBounded γ f h := by
  constructor
  . exact asymp_bounded_above_trans γ ha.1 hb.1
  . exact asymp_bounded_below_trans γ ha.2 hb.2

end Bounded


section Dom

variable [PartialOrder γ] [MonoidWithZero γ] [MulAction γ β] [ZeroLEOneClass γ] [NeZero (@One.one γ _)] [PosSMulMono γ β] 

lemma asymp_left_dom_trans (ha : AsympLeftDom γ f g) (hb : AsympLeftDom γ g h) : AsympLeftDom γ f h := by
  intro k k_pos
  specialize ha k k_pos
  specialize hb 1 one_pos
  simp at hb
  apply asymp_ge_pos_smul k_pos at hb
  exact asymp_ge_trans ha hb

lemma asymp_right_dom_trans (ha : AsympRightDom γ f g) (hb : AsympRightDom γ g h) : AsympRightDom γ f h := by
  intro k k_pos
  specialize ha k k_pos
  specialize hb 1 one_pos
  simp at hb
  apply asymp_le_pos_smul k_pos at hb
  exact asymp_le_trans ha hb

end Dom

end Trans


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
  . simp [mul_smul]
    exact asymp_ge_pos_smul hc h

theorem asymp_bounded_pos_smul (hc : c > 0) (h : AsympBounded γ f g) : AsympBounded γ (fun n ↦ c • f n) g := by
  rcases h with ⟨ha, hb⟩
  constructor
  . exact asymp_bounded_above_pos_smul γ hc ha
  . exact asymp_bounded_below_pos_smul γ hc hb

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
  . exact asymp_bounded_below_neg_smul γ hc hb
  . exact asymp_bounded_above_neg_smul γ hc ha

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
  asymp_bounded_add_pos_above hf ha (asymp_bounded_above_of_right_dom hb)

theorem asymp_bounded_add_neg_left_dom (hf : AsympNeg f₂) (ha : AsympBounded γ f₁ g) (hb : AsympLeftDom γ f₂ g) : AsympBounded γ (f₁ + f₂) g :=
  asymp_bounded_add_neg_below hf ha (asymp_bounded_below_of_left_dom hb)

end Add


section Mul

variable [Semiring β] [Ring γ] [MulAction γ β] [IsScalarTower γ β β] [IsScalarTower γ γ β] 
         [SMulCommClass γ β β] {f₁ f₂ g₁ g₂ : α → β} 

private lemma pi_smul_mul_smul_comm {k₁ k₂ : γ} : k₁ • g₁ * k₂ • g₂ = (k₁ * k₂) • (g₁ * g₂) := by
  ext n
  simp
  apply smul_mul_smul_comm

variable [LinearOrder α] [Preorder β] [MulPosMono β] [PosMulMono β] [Preorder γ] [PosMulStrictMono γ]

lemma asymp_bounded_above_nonneg_mul (hf₁ : AsympNonneg f₁) (hf₂ : AsympNonneg f₂) (ha : AsympBoundedAbove γ f₁ g₁) (hb : AsympBoundedAbove γ f₂ g₂) : AsympBoundedAbove γ (f₁ * f₂) (g₁ * g₂) := by
  rcases ha with ⟨k₁, k₁_pos, ha⟩
  rcases hb with ⟨k₂, k₂_pos, hb⟩
  use k₁ * k₂
  constructor
  . exact mul_pos k₁_pos k₂_pos
  . suffices AsympLE (f₁ * f₂) (k₁ • g₁ * k₂ • g₂) by {
      rw [pi_smul_mul_smul_comm γ] at this 
      exact this
    } 
    exact asymp_le_nonneg_mul hf₁ hf₂ ha hb

lemma asymp_bounded_below_nonpos_mul [ExistsAddOfLE β] [AddRightMono β] [AddRightReflectLE β] (hf₁ : AsympNonpos f₁) (hf₂ : AsympNonpos f₂) (ha : AsympBoundedBelow γ f₁ g₁) (hb : AsympBoundedBelow γ f₂ g₂) : AsympBoundedAbove γ (f₁ * f₂) (g₁ * g₂) := by
  rcases ha with ⟨k₁, k₁_pos, ha⟩
  rcases hb with ⟨k₂, k₂_pos, hb⟩
  use k₁ * k₂
  constructor
  . exact mul_pos k₁_pos k₂_pos
  . suffices AsympLE (f₁ * f₂) (k₁ • g₁ * k₂ • g₂) by {
      rw [pi_smul_mul_smul_comm γ] at this 
      exact this
    } 
    exact asymp_ge_nonpos_mul hf₁ hf₂ ha hb

end Mul

end Properties

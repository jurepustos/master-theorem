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

private def AsympProperty {α : Type*} [LE α] (p : α → Prop) :=
  ∃ N, ∀ n ≥ N, p n

def AsympNonZero {α β : Type*} [LE α] [Zero β] (f : α → β) :=
  AsympProperty (fun n ↦ f n ≠ 0)

def AsympPos {α β : Type*} [LE α] [LT β] [Zero β] (f : α → β) :=
  AsympProperty (fun n ↦ f n > 0)

def AsympNeg {α β : Type*} [LE α] [LT β] [Zero β] (f : α → β) :=
  AsympProperty (fun n ↦ f n < 0)

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

end Definitions

section AsympBasic

variable {α β : Type*} [Preorder α]

lemma asymp_le_refl [One α] [Preorder β] {f : α → β} : AsympLE f f := by
  use 1
  intro n hn
  exact le_refl _

lemma asymp_ge_refl [One α] [Preorder β] {f : α → β} : AsympGE f f := by
  exact asymp_le_refl

lemma asymp_le_of_asymp_ge [LE β] {f g : α → β} (h : AsympGE f g) : AsympLE g f := by
  rcases h with ⟨N, h⟩
  use N

lemma asymp_ge_of_asymp_le [LE β] {f g : α → β} (h : AsympLE f g) : AsympGE g f := by
  exact asymp_le_of_asymp_ge h

lemma asymp_le_asymp_ge_iff [LE β] {f g : α → β} : AsympLE f g ↔ AsympGE g f := by
  constructor <;> intro h
  . exact asymp_ge_of_asymp_le h
  . exact asymp_le_of_asymp_ge h

lemma asymp_neg_of_asymp_pos {f : α → β} [LT β] [AddGroup β] [AddLeftStrictMono β] (h : AsympPos f) : AsympNeg (fun n ↦ -f n) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact h

lemma asymp_pos_of_asymp_neg {f : α → β} [LT β] [AddGroup β] [AddLeftStrictMono β] (h : AsympNeg f) : AsympPos (fun n ↦ -f n) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact h
  
lemma asymp_le_pos_mul {γ : Type*} {c : γ} {f g : α → β} [Preorder β] [Preorder γ] [MonoidWithZero γ] [MulAction γ β] [PosSMulMono γ β] (hc : c > 0) (h : AsympLE f g) : AsympLE (fun n ↦ c • f n) (fun n ↦ c • g n) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  simp
  specialize h n hn
  exact smul_le_smul_of_nonneg_left h (le_of_lt hc)

lemma asymp_ge_pos_mul {γ : Type*} {c : γ} {f g : α → β} [Preorder β] [Preorder γ] [MonoidWithZero γ] [MulAction γ β] [PosSMulMono γ β] (hc : c > 0) (h : AsympGE f g) : AsympGE (fun n ↦ c • f n) (fun n ↦ c • g n) := by
  apply asymp_ge_of_asymp_le
  exact asymp_le_pos_mul hc h

lemma asymp_le_neg_mul {γ : Type*} {c : γ} {f g : α → β} [OrderedAddCommGroup β] [OrderedRing γ] [Module γ β] [PosSMulMono γ β] [PosSMulReflectLE γ β] (hc : c < 0) (h : AsympLE f g) : AsympGE (fun n ↦ c • f n) (fun n ↦ c • g n) := by
  rcases h with ⟨N, h⟩
  use N
  intro n hn
  specialize h n hn
  simp
  exact (smul_le_smul_iff_of_neg_left hc).2 h

lemma asymp_ge_neg_mul {γ : Type*} {c : γ} {f g : α → β} [OrderedAddCommGroup β] [OrderedRing γ] [Module γ β] [PosSMulMono γ β] [PosSMulReflectLE γ β] (hc : c < 0) (h : AsympGE f g) : AsympLE (fun n ↦ c • f n) (fun n ↦ c • g n) := by
  apply asymp_le_of_asymp_ge
  exact asymp_le_neg_mul hc h

lemma asymp_le_mul_smul {γ : Type*} {a b : γ} {f g : α → β} [Preorder β] [Preorder γ] [MonoidWithZero γ] [MulAction γ β] [PosSMulMono γ β] : AsympLE f (fun n ↦ (a * b) • g n) ↔ AsympLE f (fun n ↦ a • b • g n) := by
  constructor <;> (
    intro h
    rcases h with ⟨N, h⟩
    use N
    intro n hn
    specialize h n hn
    simp
    simp at h
  )
  . rw [← mul_smul]
    assumption
  . rw [mul_smul]
    assumption

lemma mul_smul_asymp_le {γ : Type*} {a b : γ} {f g : α → β} [Preorder β] [Preorder γ] [MonoidWithZero γ] [MulAction γ β] [PosSMulMono γ β] : AsympLE (fun n ↦ (a * b) • f n) g ↔ AsympLE (fun n ↦ a • b • f n) g := by
  constructor <;> (
    intro h
    rcases h with ⟨N, h⟩
    use N
    intro n hn
    specialize h n hn
    simp
    simp at h)
  . rw [← mul_smul]
    assumption
  . rw [mul_smul]
    assumption

end AsympBasic

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

variable {α β γ : Type*} {f g : α → β} 

section Refl

variable [LinearOrder α] [Preorder β] [PartialOrder γ] [One α] [γ_monoid : MonoidWithZero γ] [MulAction γ β] [ZeroLEOneClass γ] [@NeZero γ γ_monoid.toZero γ_monoid.one]

theorem asymp_bounded_refl : AsympBounded γ f f := by
  constructor <;>
  . use 1
    constructor
    . exact one_pos
    . use 1
      intro _ _
      simp

theorem asymp_bounded_above_refl : AsympBoundedAbove γ f f := by
  exact asymp_bounded_refl.1

theorem asymp_bounded_below_refl : AsympBoundedBelow γ f f := by
  exact asymp_bounded_refl.2

end Refl

section Mul

variable {c : γ} 

section Pos

variable [LinearOrder α] [Preorder β] [PartialOrder γ] [MonoidWithZero γ] [MulAction γ β] [PosMulStrictMono γ] [PosSMulMono γ β] 

theorem asymp_bounded_above_pos_mul (hc : c > 0) (h : AsympBoundedAbove γ f g) : AsympBoundedAbove γ (fun n ↦ c • f n) g := by
  rcases h with ⟨k, k_pos, h⟩ 
  use c * k
  constructor
  . exact mul_pos hc k_pos
  . rw [asymp_le_mul_smul]
    exact asymp_le_pos_mul hc h

theorem asymp_bounded_below_pos_mul (hc : c > 0) (h : AsympBoundedBelow γ f g) : AsympBoundedBelow γ (fun n ↦ c • f n) g := by
  rcases h with ⟨k, k_pos, h⟩ 
  use c * k
  constructor
  . exact mul_pos hc k_pos
  . rw [← asymp_le_asymp_ge_iff]
    rw [← asymp_le_asymp_ge_iff] at h
    rw [mul_smul_asymp_le]
    exact asymp_le_pos_mul hc h

theorem asymp_bounded_pos_mul (hc : c > 0) (h : AsympBounded γ f g) : AsympBounded γ (fun n ↦ c • f n) g := by
  rcases h with ⟨ha, hb⟩
  constructor
  . exact asymp_bounded_above_pos_mul hc ha
  . exact asymp_bounded_below_pos_mul hc hb

end Pos

section Neg

variable [Preorder α] [OrderedAddCommGroup β] [OrderedRing γ] [Module γ β] 
         [AddLeftStrictMono γ] [PosMulStrictMono γ] [PosSMulMono γ β] [PosSMulReflectLE γ β] 

theorem asymp_bounded_above_neg_mul (hc : c < 0) (h : AsympBoundedAbove γ f g) : AsympBoundedBelow γ (fun n ↦ c • f n) (fun n ↦ - g n) := by
  rcases h with ⟨k, k_pos, h⟩  
  use -c * k
  constructor
  . exact mul_pos (neg_pos_of_neg hc) k_pos
  . rw [← asymp_le_asymp_ge_iff, mul_smul_asymp_le]
    suffices AsympGE (fun n ↦ c • f n) (fun n ↦ c • k • g n) by {
      rcases this with ⟨N, h⟩
      use N
      intro n hn
      specialize h n hn
      simp
      simp at h
      exact h
    }
    exact asymp_le_neg_mul hc h

theorem asymp_bounded_below_neg_mul (hc : c < 0) (h : AsympBoundedBelow γ f g) : AsympBoundedAbove γ (fun n ↦ c • f n) (fun n ↦ - g n) := by
  rcases h with ⟨k, k_pos, h⟩  
  use -c * k
  constructor
  . exact mul_pos (neg_pos_of_neg hc) k_pos
  . rw [asymp_le_mul_smul, asymp_le_asymp_ge_iff]
    suffices AsympLE (fun n ↦ c • f n) (fun n ↦ c • k • g n) by {
      rcases this with ⟨N, h⟩
      use N
      intro n hn
      specialize h n hn
      simp
      simp at h
      exact h
    }
    exact asymp_ge_neg_mul hc h

theorem asymp_bounded_neg_mul (hc : c < 0) (h : AsympBounded γ f g) : AsympBounded γ (fun n ↦ c • f n) (fun n ↦ - g n) := by
  rcases h with ⟨ha, hb⟩
  constructor 
  . exact asymp_bounded_below_neg_mul hc hb
  . exact asymp_bounded_above_neg_mul hc ha

end Neg

end Mul

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

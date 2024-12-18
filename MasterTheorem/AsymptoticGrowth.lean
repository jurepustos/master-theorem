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

def AsympPositive {α β : Type*} [LE α] [LT β] [Zero β] (f : α → β) :=
  ∃ N, ∀ n ≥ N, f n > 0

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

def AsympDominated (f g : α → β) :=
  ∀ k : γ, k > 0 → EventuallyLessThan f (fun n ↦ k • g n)

def AsympDominates (f g : α → β) :=
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

lemma asymp_dominated_imp_bounded_above (h : AsympDominated γ f g) : AsympBoundedAbove γ f g := by
  unfold AsympBoundedAbove
  unfold AsympDominated at h
  specialize h 1 
  use 1
  constructor
  . exact one_pos
  . exact h one_pos

lemma asymp_dominates_imp_bounded_below (h : AsympDominates γ f g) : AsympBoundedBelow γ f g := by
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

theorem not_asymp_bounded_and_dominated (hg : AsympPositive g) : ¬(AsympBounded γ f g ∧ AsympDominated γ f g) := by
  intro h
  rcases h with ⟨hb, hd⟩

  -- unwrap the existential quantifiers
  rcases hb with ⟨_, ⟨k₁, k₁_pos, N₁, hb⟩⟩
  rcases hg with ⟨N₂, hg⟩

  -- set k to a useful value and get the N out
  generalize hk₂ : k₁ / 2 = k₂
  have k₂_pos : k₂ > 0 := by linarith
  unfold AsympDominated at hd
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

-- If f is asymptotically bounded by a function g that is nonzero for large inputs, then it is not dominated by g.
lemma asymp_bounded_imp_not_dominated (hg : AsympPositive g) (hb : AsympBounded γ f g) : ¬AsympDominated γ f g := by
  intro hd
  exact not_asymp_bounded_and_dominated hg (And.intro hb hd)

lemma asymp_bounded_below_imp_not_dominated (hg : AsympPositive g) (h : AsympBoundedBelow γ f g) : ¬AsympDominated γ f g := by
  intro hd
  have ha := asymp_dominated_imp_bounded_above hd
  have hb := asymp_bounded_above_and_below_imp_bounded ha h
  exact not_asymp_bounded_and_dominated hg (And.intro hb hd)

lemma asymp_dominated_imp_not_bounded (hg : AsympPositive g) (hd : AsympDominated γ f g) : ¬AsympBounded γ f g := by 
  intro hb
  exact not_asymp_bounded_and_dominated hg (And.intro hb hd)

theorem asymp_dominated_imp_not_bounded_below (hg : AsympPositive g) (hd : AsympDominated γ f g) : ¬AsympBoundedBelow γ f g := by 
  intro hb
  have ha := asymp_dominated_imp_bounded_above hd
  have h := asymp_bounded_above_and_below_imp_bounded ha hb
  exact not_asymp_bounded_and_dominated hg (And.intro h hd)

theorem not_asymp_bounded_and_dominates (hg : AsympPositive g) : ¬(AsympBounded γ f g ∧ AsympDominates γ f g) := by
  intro h
  rcases h with ⟨hb, hd⟩
  rcases hg with ⟨N₁, hg⟩
  rcases hb with ⟨⟨k₁, k₁_pos, N₂, ha⟩, _⟩

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

lemma asymp_bounded_imp_not_dominates (hg : AsympPositive g) (hb : AsympBounded γ f g) : ¬AsympDominates γ f g := by
  intro hd
  exact not_asymp_bounded_and_dominates hg (And.intro hb hd)

lemma asymp_dominates_imp_not_bounded (hg : AsympPositive g) (hd : AsympDominates γ f g) : ¬AsympBounded γ f g := by
  revert hd
  contrapose
  simp
  exact asymp_bounded_imp_not_dominates hg

theorem asymp_dominates_imp_not_bounded_above (hg : AsympPositive g) (hd : AsympDominates γ f g) : ¬AsympBoundedAbove γ f g := by 
  intro ha
  have hb := asymp_dominates_imp_bounded_below hd
  have h := asymp_bounded_above_and_below_imp_bounded ha hb
  exact not_asymp_bounded_and_dominates hg (And.intro h hd)

theorem not_asymp_dominates_and_dominated (hg: AsympPositive g): ¬(AsympDominates γ f g ∧ AsympDominated γ f g) := by
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

theorem asymp_bounded_refl {α β γ : Type*} {f : α → β} [Zero α] [α_one : One α] 
                           [PartialOrder α] [ZeroLEOneClass α] [NeZero α_one.1]
                           [Preorder β] [PartialOrder γ] [γ_monoid : MonoidWithZero γ] 
                           [ZeroLEOneClass γ] [@NeZero γ γ_monoid.toZero γ_monoid.one] 
                           [MulAction γ β] : AsympBounded γ f f := by
  constructor <;>
  . use 1
    constructor
    . exact one_pos
    . use 1
      intro _ _
      simp

section TwoFunctions

variable {α β γ : Type*} {f g : α → β} [PartialOrder α] [Zero α] [One α] [Preorder β] [Monoid β]
         [PartialOrder γ] [γ_monoid : MonoidWithZero γ] [ZeroLEOneClass γ] 
         [@NeZero γ γ_monoid.toZero γ_monoid.one] [MulAction γ β] [PosMulStrictMono γ] [PosSMulMono γ β]

theorem asymp_bounded_pos_const_mul {c : γ} (hc : c > 0) (h : AsympBounded γ f g) : AsympBounded γ (fun n ↦ c • f n) g := by
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

theorem asymp_bounded_add_bounded {h : α → β} (hf : AsympBounded γ f g) (hh : AsympBounded γ h g) : AsympBounded γ (fun n ↦ f n + h n) g := by
  sorry

theorem asymp_bounded_add_bounded_above {h : α → β} (hf : AsympBounded γ f g) (hh : AsympBoundedAbove γ h g) : AsympBounded γ (fun n ↦ f n + h n) g := by
  sorry

theorem asymp_bounded_add_dominated {h : α → β} (hf : AsympBounded γ f g) (hh : AsympDominated γ h g) : AsympBounded γ (fun n ↦ f n + h n) g := by
  sorry

theorem asymp_bounded_add_bounded_below {h : α → β} (hf : AsympBounded γ f g) (hh : AsympBoundedBelow γ h g) : AsympBoundedBelow γ (fun n ↦ f n + h n) g := by
  sorry

theorem asymp_bounded_add_dominates {h : α → β} (hf : AsympBounded γ f g) (hh : AsympDominates γ h g) : AsympDominates γ (fun n ↦ f n + h n) g := by
  sorry

end TwoFunctions

end AsympBounded

end Properties

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

def AsympBoundedAbove (f g : α → β) := 
  ∃ k : γ, k > 0 ∧ EventuallyLessThan f (fun n ↦ k • g n)

def AsympBoundedBelow (f g : α → β) :=
  AsympBoundedAbove γ g f

def AsympBounded (f g : α → β) :=
  AsympBoundedAbove γ f g ∧ AsympBoundedBelow γ f g

def AsympDominated (f g : α → β) :=
  ∀ k : γ, k > 0 → EventuallyLessThan f (fun n ↦ k • g n)

def AsympDominates (f g : α → β) :=
  AsympDominated γ g f

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

variable [PartialOrder α] [PartialOrder β] [LinearOrderedSemiring γ] [SMul γ β]

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

variable [LinearOrder α] [LinearOrderedRing β] [γ_linOrdField : LinearOrderedField γ] [Module γ β] 

theorem not_asymp_bounded_and_dominated [PosSMulMono γ β] [SMulPosStrictMono γ β] (hg : AsympPositive g) : ¬(AsympBounded γ f g ∧ AsympDominated γ f g) := by
  intro h
  rcases h with ⟨hb, hd⟩

  -- unwrap the existential quantifiers
  rcases hb with ⟨_, ⟨k₁, k₁_pos, N₁, hb⟩⟩
  rcases hg with ⟨N₂, hg⟩

  -- set k to a useful value and get the N out
  generalize hk₂ : k₁⁻¹ * 2⁻¹ = k₂
  have k₁_inv_pos : k₁⁻¹ > 0 := inv_pos.2 k₁_pos
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

  simp at hb hd
  have hb2 : k₁⁻¹ • g N ≤ f N := by {
    apply (inv_smul_le_iff_of_pos k₁_pos).2 
    exact hb
  }

  have k₂_lt_k₁_inv : k₂ < k₁⁻¹ := by {
    rw [← hk₂, inv_mul_eq_div, inv_div_comm]
    exact half_lt_self_iff.2 k₁_inv_pos
  }
  rw [← hk₂] at k₂_lt_k₁_inv

  -- create a conflicting pair of inequalities and finish the proof
  have contra1 := le_trans hb2 hd
  have contra2 : (k₁⁻¹ * 2⁻¹) • g N < k₁⁻¹ • g N := smul_lt_smul_of_pos_right k₂_lt_k₁_inv hg
  rw [← hk₂] at contra1
  exact not_le_of_gt contra2 contra1

-- If f is asymptotically bounded by a function g that is nonzero for large inputs, then it is not dominated by g.
lemma asymp_bounded_imp_not_dominated [PosSMulMono γ β] [SMulPosStrictMono γ β] (hg : AsympPositive g) (hb : AsympBounded γ f g) : ¬AsympDominated γ f g := by
  intro hd
  exact not_asymp_bounded_and_dominated hg (And.intro hb hd)

lemma asymp_bounded_below_imp_not_dominated [PosSMulMono γ β] [SMulPosStrictMono γ β] (hg : AsympPositive g) (h : AsympBoundedBelow γ f g) : ¬AsympDominated γ f g := by
  intro hd
  have ha := asymp_dominated_imp_bounded_above hd
  have hb := asymp_bounded_above_and_below_imp_bounded ha h
  exact not_asymp_bounded_and_dominated hg (And.intro hb hd)

lemma asymp_dominated_imp_not_bounded [PosSMulMono γ β] [SMulPosStrictMono γ β] (hg : AsympPositive g) (hd : AsympDominated γ f g) : ¬AsympBounded γ f g := by 
  intro hb
  exact not_asymp_bounded_and_dominated hg (And.intro hb hd)

theorem asymp_dominated_imp_not_bounded_below [PosSMulMono γ β] [SMulPosStrictMono γ β] (hg : AsympPositive g) (hd : AsympDominated γ f g) : ¬AsympBoundedBelow γ f g := by 
  intro hb
  have ha := asymp_dominated_imp_bounded_above hd
  have h := asymp_bounded_above_and_below_imp_bounded ha hb
  exact not_asymp_bounded_and_dominated hg (And.intro h hd)

theorem not_asymp_bounded_and_dominates [PosSMulMono γ β] [SMulPosStrictMono γ β] (hg : AsympPositive g) : ¬(AsympBounded γ f g ∧ AsympDominates γ f g) := by
  intro h
  rcases h with ⟨hb, hd⟩
  rcases hg with ⟨N₁, hg⟩
  rcases hb with ⟨⟨k₁, k₁_pos, N₂, ha⟩, _⟩

  -- use a favorable value for k
  generalize hk₂ : (k₁ + 1)⁻¹ = k₂
  have k₁_inv_pos : k₁⁻¹ > 0 := inv_pos.2 k₁_pos
  have k₂_inv_pos : k₁ + 1 > 0 := by linarith
  have k₂_pos : (k₁ + 1)⁻¹ > 0 := inv_pos.2 k₂_inv_pos
  rw [hk₂] at k₂_pos
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

  have hd2 : (k₁ + 1) • g N ≤ f N := (le_inv_smul_iff_of_pos k₂_inv_pos).1 hd

  simp at *
  have contra1 := le_trans hd2 ha
  have contra2 : k₁ • g N < (k₁ + 1) • g N := smul_lt_smul_of_pos_right (by linarith) hg
  exact not_le_of_gt contra2 contra1

lemma asymp_bounded_imp_not_dominates [PosSMulMono γ β] [SMulPosStrictMono γ β] (hg : AsympPositive g) (hb : AsympBounded γ f g) : ¬AsympDominates γ f g := by
  intro hd
  exact not_asymp_bounded_and_dominates hg (And.intro hb hd)

lemma asymp_dominates_imp_not_bounded [PosSMulMono γ β] [SMulPosStrictMono γ β] (hg : AsympPositive g) (hd : AsympDominates γ f g) : ¬AsympBounded γ f g := by
  revert hd
  contrapose
  simp
  exact asymp_bounded_imp_not_dominates hg

theorem asymp_dominates_imp_not_bounded_above [PosSMulMono γ β] [SMulPosStrictMono γ β] (hg : AsympPositive g) (hd : AsympDominates γ f g) : ¬AsympBoundedAbove γ f g := by 
  intro ha
  have hb := asymp_dominates_imp_bounded_below hd
  have h := asymp_bounded_above_and_below_imp_bounded ha hb
  exact not_asymp_bounded_and_dominates hg (And.intro h hd)

theorem not_asymp_dominates_and_dominated [PosSMulStrictMono γ β] [SMulPosStrictMono γ β] (hg: AsympPositive g): ¬(AsympDominates γ f g ∧ AsympDominated γ f g) := by
  intro h 
  rcases h with ⟨ha, hb⟩

  generalize hk : (γ_linOrdField.natCast 2)⁻¹ = k
  have k_pos : k > 0 := by linarith
  simp at hk
  specialize ha k (by linarith)
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

  simp at *
  have k_lt_one : k < 1 := by linarith
  have gN_gt_half_fN : g N > k • f N := by {
    /- rw [← hk]     -/
    apply (lt_inv_smul_iff_of_pos k_pos).1
    rw [← hk, inv_inv]
    have gN_lt_two_gN := smul_lt_smul_of_pos_right (@one_lt_two γ _ _ _ _ _) hg
    rw [one_smul] at gN_lt_two_gN
    exact lt_of_le_of_lt hb gN_lt_two_gN
  }
  exact not_le_of_gt gN_gt_half_fN ha 

end LinearOrdered

end BasicRelations

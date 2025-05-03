import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Action
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Order.MinMax

section ThreeMax

variable {α : Type*} [LinearOrder α]

lemma le_three_max_left (a b c : α) : a ≤ a ⊔ b ⊔ c := by
  rw [max_assoc]
  apply le_max_left 

lemma le_three_max_middle (a b c : α) : b ≤ a ⊔ b ⊔ c := by
  rw [max_assoc, ← max_comm, max_assoc]
  apply le_max_left

lemma le_three_max_right (a b c : α) : c ≤ a ⊔ b ⊔ c := by
  rw [max_comm]
  apply le_max_left

end ThreeMax


section FourMax

variable {α : Type*} [LinearOrder α]

lemma le_four_max_fst (a b c d : α) : a ≤ a ⊔ b ⊔ c ⊔ d := by
  rw [max_assoc]
  apply le_three_max_left 

lemma le_four_max_snd (a b c d : α) : b ≤ a ⊔ b ⊔ c ⊔ d := by
  rw [max_assoc, max_assoc, max_comm]
  apply le_three_max_left

lemma le_four_max_thrd (a b c d : α) : c ≤ a ⊔ b ⊔ c ⊔ d := by
  rw [max_assoc, max_comm]
  apply le_three_max_left

lemma le_four_max_frth (a b c d : α) : d ≤ a ⊔ b ⊔ c ⊔ d := by
  rw [max_comm]
  apply le_max_left

end FourMax

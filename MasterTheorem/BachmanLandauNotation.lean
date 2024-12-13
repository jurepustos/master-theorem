import Mathlib.Algebra.Order.Ring.Abs

import MasterTheorem.AsymptoticGrowth

variable {R F : Type} [LinearOrderedCommRing R] [LinearOrderedField F]

def O (g : R → F) := 
  { f : R → F | AsympNonZero g ∧ AsympBoundedAbove f g }

def Ω (g : R → F) := 
  { f : R → F | AsympNonZero g ∧ AsympBoundedBelow f g }

def Θ (g : R → F) := 
  { f : R → F | AsympNonZero g ∧ AsympBounded f g }

def o (g : R → F) := 
  { f : R → F | AsympNonZero g ∧ AsympDominated f g }

def ω (g : R → F) := 
  { f : R → F | AsympNonZero g ∧ AsympDominates f g }

section BasicRelations

variable {f g : R → F}

theorem o_imp_O (h : f ∈ o g) : f ∈ O g := by
  rcases h with ⟨hg, hd⟩
  have hbound := asymp_dominated_imp_bounded_above hd
  constructor <;> tauto

theorem ω_imp_Ω (h : f ∈ ω g) : f ∈ Ω g := by
  rcases h with ⟨hg, hd⟩
  have hbound := asymp_dominates_imp_bounded_below hd
  constructor <;> tauto

theorem O_and_Ω_equiv_Θ : f ∈ O g ∧ f ∈ Ω g ↔ f ∈ Θ g := by
  constructor <;> intro h
  . rcases h with ⟨⟨hg, hO⟩, ⟨_, hΩ⟩⟩
    have hbound := asymp_bounded_above_and_below_equiv_bounded.1 (And.intro hO hΩ)
    constructor <;> tauto
  . rcases h with ⟨_, h⟩
    have hbound := asymp_bounded_above_and_below_equiv_bounded.2 h
    constructor <;> constructor <;> tauto

theorem not_Θ_and_o : ¬(f ∈ Θ g ∧ f ∈ o g) := by
  intro h
  rcases h with ⟨⟨hg, hΘ⟩, ⟨_, ho⟩⟩ 
  exact not_asymp_bounded_and_dominated hg (And.intro hΘ ho)

theorem not_Θ_and_ω : ¬(f ∈ Θ g ∧ f ∈ ω g) := by
  intro h
  rcases h with ⟨⟨hg, hΘ⟩, ⟨_, hω⟩⟩ 
  exact not_asymp_bounded_and_dominates hg (And.intro hΘ hω)

theorem Θ_imp_not_o (hΘ : f ∈ Θ g) : ¬f ∈ o g := by
  intro ho
  exact not_Θ_and_o (And.intro hΘ ho)

theorem Θ_imp_not_ω (hΘ : f ∈ Θ g) : ¬f ∈ ω g := by
  intro hω
  exact not_Θ_and_ω (And.intro hΘ hω)

theorem not_o_and_ω : ¬(f ∈ o g ∧ f ∈ ω g) := by
  intro h
  rcases h with ⟨⟨hg, ho⟩, ⟨_, hω⟩⟩
  exact not_asymp_dominates_and_dominated hg (And.intro hω ho)

end BasicRelations


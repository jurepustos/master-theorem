import Mathlib

import MasterTheorem.BachmanLandauNotation
import MasterTheorem.AsymptoticGrowth
import MasterTheorem.GeometricSum
import MasterTheorem.CeilDiv
import MasterTheorem.MasterRecurrence

namespace MasterRecurrence

variable {T f : ℕ → ℕ} {a b d : ℕ}

theorem O_of_poly_of_scale_lt_base_pow (self : MasterRecurrence T a b f) (hd : d > 0) 
    (hf_poly : f ∈ O ℕ fun n ↦ n^d) (hlt : a < b^d) : T ∈ O ℕ fun n ↦ n^d := by
  sorry


end MasterRecurrence

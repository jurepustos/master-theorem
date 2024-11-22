import Mathlib.Algebra.Order.Ring.Abs

import MasterTheorem.AsymptoticGrowth

def O {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (g : L → R) := 
  { f : L → R | AsymptoticallyBoundedAboveBy f g }

def Ω {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (g : L → R) := 
  { f : L → R | AsymptoticallyBoundedBelowBy f g }

def Θ {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (g : L → R) := 
  { f : L → R | AsymptoticallyBoundedBy f g }

def o {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (g : L → R) := 
  { f : L → R | AsymptoticallyDominatedBy f g }

def ω {L R : Type} [LinearOrder L] [LinearOrderedCommRing R] (g : L → R) := 
  { f : L → R | AsymptoticallyDominates f g }

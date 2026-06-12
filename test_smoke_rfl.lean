import OrbgrandAi

open OrbgrandAi.Section06

example (z : Fin 6 -> Complex) (i : Fin 4) (j : Fin 2) :
    regressorMatrix4x2 z i j
      = z ⟨i.val + j.val,
           Nat.lt_succ_of_lt
             (Nat.add_lt_add_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt))⟩ := rfl

-- Sanity: concrete index reduces
example (z : Fin 6 -> Complex) :
    regressorMatrix4x2 z 3 1 = z 4 := rfl

-- Correct way to do recursion in term mode with pattern matching
example : ∀ n : Nat, n + 0 = n := 
  fun n => 
    let rec go : ∀ m : Nat, m + 0 = m
      | 0 => rfl
      | m + 1 => 
          let ih := go m
          by simp [Nat.add_zero, ih]
    go n

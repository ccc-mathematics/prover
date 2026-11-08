-- 用歸納型別證明 0 + n = n
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with k ih
  rfl
  exact Eq.congr Nat.succ ih

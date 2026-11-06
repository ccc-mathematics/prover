-- 假言三段論
theorem syllogism (h1 : P -> Q) (h2 : Q -> R) : P -> R := by
  intro hp
  apply h2
  apply h1
  exact hp

theorem ex_not_all : (exists x. P(x)) -> ~(forall x. ~P(x)) := by
  intro h
  intro hn
  cases h with x hx
  exact hn x hx

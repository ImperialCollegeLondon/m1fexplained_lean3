import tactic
import data.real.irrational

/-- Between any two different real numbers there is a rational
number and an irrational number. -/
lemma exercise : ∀ {a b : ℝ} (hab : a < b), (∃ (x : ℚ), a < x ∧ ↑x < b) ∧ (∃ (y : ℝ) (hy : irrational y), a < y ∧ y < b) := begin
  sorry
end

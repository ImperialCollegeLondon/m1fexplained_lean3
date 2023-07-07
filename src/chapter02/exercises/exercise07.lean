import tactic
import data.real.irrational

namespace chapter02.exercise07

def positive_integer (x : ℝ) := x ∈ set.range (coe : ℕ → ℝ) ∧ x > 0

/-- There is a positive integer n such that √(n - 2) + √(n + 2) is also a positive integer. -/
lemma exercise : ∃ (n : ℕ), n > 0 ∧ positive_integer (real.sqrt (n - 2) + real.sqrt (n + 2)) :=
begin
  sorry
end

end chapter02.exercise07

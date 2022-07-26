import tactic
import data.real.irrational

def rational (x : ℝ) :=
  ∃ (a b : ℤ), x = a / b

/-- For a, b rational and x irrational, if (x+a)/(x+b) is rational, then a = b. -/
lemma part_a (a : ℚ) (b : ℚ) (x : ℝ) (hx : irrational x) : rational ((x + a) / (x + b)) → a = b :=
begin
  sorry
end

/-- For x, y rational such that (x^2 + x + √2)/(y^2 + y + √2) is rational, either x = y or x + y = -1. -/
lemma part_b (x : ℚ) (y : ℚ) (h : rational ((x^2 + x + real.sqrt 2)/(y^2 + y + real.sqrt 2))) : x = y ∨ x + y = -1 :=
begin
  sorry
end

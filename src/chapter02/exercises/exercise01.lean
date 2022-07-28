import tactic
import data.real.irrational

/-- √3 is irrational. -/
lemma part_a : irrational 3 :=
begin
  sorry
end

/-- There are no rationals r,s such that √3 = r + s √2. -/
lemma part_b : ¬ ∃ (r s : ℚ), real.sqrt 3 = r + s * real.sqrt 2 :=
begin
  sorry
end

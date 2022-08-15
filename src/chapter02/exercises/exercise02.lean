import tactic
import data.real.irrational

def rational (x : ℝ) :=
  ∃ (a b : ℤ), x = a / b

lemma part_a : irrational (real.sqrt 2 + real.sqrt (3/2)) := begin
  sorry
end

lemma part_b : irrational (1 + real.sqrt 2 + real.sqrt (3/2)) := begin
  sorry
end

lemma part_c : rational (2 * real.sqrt 18 - 3 * real.sqrt 8 + real.sqrt 4) := begin
  sorry
end

lemma part_d : irrational (real.sqrt 2 + real.sqrt 3 + real.sqrt 5) :=
begin
  sorry
end

lemma part_e : rational (real.sqrt 2 + real.sqrt 3 - real.sqrt (5 + 2 * real.sqrt 6)) :=
begin
  sorry
end

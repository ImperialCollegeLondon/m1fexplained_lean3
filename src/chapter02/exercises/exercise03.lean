import tactic
import data.real.irrational

def rational (x : ℝ) :=
  ∃ (a b : ℤ), x = a / b

/-- The product of two rational numbers is always rational. -/
lemma part_a : ∀ {a b : ℝ}, rational a → rational b → rational (a * b) :=
begin
  sorry
end

/-- The product of two irrational numbers is not always irrational. -/
lemma part_b : ¬ ∀ {a b : ℝ}, irrational a → irrational b → irrational (a * b) :=
begin
  sorry
end

/-- The product of two irrational numbers is not always rational. -/
lemma part_c : ¬ ∀ {a b : ℝ}, irrational a → irrational b → rational (a * b) :=
begin
  sorry
end

/-- The product of a non-zero rational and an irrational is always irrational. -/
lemma part_d : ∀ {a b : ℝ}, a ≠ 0 → rational a → irrational b → irrational (a * b) :=
begin
  sorry
end

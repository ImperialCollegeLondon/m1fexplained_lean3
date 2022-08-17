import tactic
import data.real.irrational

def rational (x : ℝ) :=
  ∃ (a b : ℤ), x = a / b

/-- The product of two rational numbers is always rational. -/
lemma part_a : ∀ {a b : ℝ}, rational a → rational b → rational (a * b) :=
begin
  intros a b,
  rintro ⟨x1,y1,h1⟩ ⟨x2,y2,h2⟩,
  use [x1*x2, y1*y2],
  simp,
  ring_nf,
  rw [mul_inv, h1, h2],
  ring_nf,
end

/-- The product of two irrational numbers is not always irrational. -/
lemma part_b : ¬ ∀ {a b : ℝ}, irrational a → irrational b → irrational (a * b) :=
begin
  simp, 
  use real.sqrt 2, 
  split,
  {exact irrational_sqrt_two,},
  {use 1/(real.sqrt 2),
  split,
  {apply irrational.of_inv,
  simp,
  exact irrational_sqrt_two,},
  {simp,
  intro h,
  apply irrational.ne_one,
  {exact h,},{refl,},},},
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

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Natasha Johnson
-/

import tactic
import data.real.irrational

namespace chapter02.exercise03


def rational (x : ℝ) :=
  ∃ (a b : ℤ), x = a / b

/-- The product of two rational numbers is always rational. -/
lemma part_a : ∀ {a b : ℝ}, rational a → rational b → rational (a * b) :=
begin
  rintro a b ⟨x1,y1,rfl⟩ ⟨x2,y2,rfl⟩,
  use [x1*x2, y1*y2],
  push_cast,
  simp only [div_eq_mul_inv, mul_inv],
  ring,
end

/-- The product of two irrational numbers is not always irrational. -/
lemma part_b : ¬ ∀ {a b : ℝ}, irrational a → irrational b → irrational (a * b) :=
begin
  push_neg,
  refine ⟨real.sqrt 2, real.sqrt 2, irrational_sqrt_two, irrational_sqrt_two, _⟩,
  rw irrational_iff_ne_rational,
  push_neg,
  use [2, 1], 
  norm_num,
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

end chapter02.exercise03

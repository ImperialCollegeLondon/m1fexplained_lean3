import data.real.sqrt
import data.int.sqrt
import tactic
import data.int.parity -- even and odd

lemma part_a : real.sqrt 6 - real.sqrt 2 > 1 :=
begin
  have a:= real.sqrt_nonneg (6:real),
  have b:= real.sqrt_nonneg (2:real),
  have c : 2*(real.sqrt 2) >= 0 := by linarith,
  suffices: real.sqrt 6 > 1 + real.sqrt 2, by linarith,
  suffices: (real.sqrt 6)^2 > (1+real.sqrt(2))^2,
  {
    exact lt_of_pow_lt_pow 2 a this,
  },
  rw real.sq_sqrt,
  rw add_sq 1 (real.sqrt 2),
  simp only [one_pow, mul_one, real.sq_sqrt, zero_le_bit0, zero_le_one, gt_iff_lt],
  suffices: 2*(real.sqrt 2) < 3, by linarith,
  suffices: (2*(real.sqrt 2))^2 < 3^2, 
  {
    apply lt_of_pow_lt_pow 2,
    norm_num,
    exact this,
  },
  simp only [mul_pow],
  rw real.sq_sqrt,
  norm_num,
  simp only [zero_le_bit0, zero_le_one],
  norm_num,
end

lemma part_b (n : ℤ) : even (n^2) → even n :=
begin
  sorry,
end

lemma part_c (n : ℤ) (h : ∃ m : ℤ, n = m^3 - m) : 6 ∣ n :=
begin
  sorry
end

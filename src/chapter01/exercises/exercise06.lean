import data.real.sqrt
import data.int.sqrt
import tactic
import data.int.parity -- even and odd
import data.zmod.basic

namespace chapter01.exercise06

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
  rw [real.sq_sqrt, add_sq 1 (real.sqrt 2)],
  simp only [one_pow, mul_one, real.sq_sqrt, zero_le_bit0, zero_le_one, gt_iff_lt],
  suffices: 2*(real.sqrt 2) < 3, by linarith,
  suffices: (2*(real.sqrt 2))^2 < 3^2, 
  {
    refine lt_of_pow_lt_pow 2 _ this,
    norm_num,
  },
  {
    rw [mul_pow, real.sq_sqrt],
    { norm_num, },
    { rw zero_le_bit0,
      exact zero_le_one },
  },
  norm_num,
end

lemma part_b_n (n : ℕ) : even (n^2) → even n :=
begin
  contrapose,
  repeat {rw nat.not_even_iff},
  intro h,
  rw sq,
  exact nat.odd_mul_odd h h,
end

lemma part_c (n : ℤ) (h : ∃ m : ℤ, n = m^3 - m) : 6 ∣ n :=
begin
  rcases h with ⟨m, rfl⟩,
  rw ← int.modeq_zero_iff_dvd,
  have := zmod.int_coe_eq_int_coe_iff (m^3 - m) 0 6,
  norm_cast at this,
  rw ← this,
  rw [int.cast_sub, int.cast_pow],
  generalize : (↑m : zmod 6) = m6,
  revert m6,
  dec_trivial,
end

end chapter01.exercise06

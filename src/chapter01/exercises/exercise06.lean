import data.real.sqrt
import data.int.sqrt
import tactic
import data.int.parity -- even and odd
import data.zmod.basic

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
  have p: m^3 - m = (m+1)*(m-1)*m,
  ring_nf,
  rw p, 
  have q: (6:ℤ) = 2 * 3, refl,
  rw q,
  rw ← int.modeq_zero_iff_dvd,
  have r: nat.coprime 2 3, norm_num,
  rw ← int.modeq_and_modeq_iff_modeq_mul,
  {
    split,
    {
      have := zmod.int_coe_eq_int_coe_iff ((m + 1) * (m - 1) * m) 0 2,
      norm_cast at this,
      rw ← this,
      simp only [int.cast_mul, int.cast_add, int.cast_one, int.cast_sub, mul_eq_zero],
      generalize : (↑m : zmod 2) = m2,
      revert m2,
      dec_trivial,
    },
    {
      have := zmod.int_coe_eq_int_coe_iff ((m + 1) * (m - 1) * m) 0 3,
      norm_cast at this,
      rw ← this,
      simp only [int.cast_mul, int.cast_add, int.cast_one, int.cast_sub, mul_eq_zero],
      generalize : (↑m : zmod 3) = m3,
      revert m3,
      dec_trivial,
    },
  },
  {
    norm_num,
  },
end

import data.real.sqrt
import tactic
import data.int.parity -- even and odd
import data.zmod.algebra
lemma sub_mul_add (x y : ℝ ) : (x - y)*(x + y) = x^2 - y^2 := 
begin 
  ring,
end
--example (a b c d : ℝ ) (h1: a ≤ c )(h2: b ≤ d): a+b ≤ c+ d:=
--by library_search
--lemma sqrt_lt_num (a b : ℝ )(h1 : a^2 < b) : a < b :=
--begin
  --sorry,
--end

example (a b : ℝ ) : (a*b)^2 = a^2*b^2:=
by library_search

--#print sub_mul_add

lemma part_a : real.sqrt 6 - real.sqrt 2 > 1 :=
begin

  by_contra,
  push_neg at h,
  have q : (real.sqrt 6 - real.sqrt 2)*(real.sqrt 6 + real.sqrt 2 )≤ 1*(real.sqrt 6 + real.sqrt 2 ),
  { apply mul_le_mul_of_nonneg_right(h),
    apply add_nonneg,
    { apply real.sqrt_nonneg,},
    { apply real.sqrt_nonneg,}, },
  simp at q,
  rw sub_mul_add at q,
  rw real.sq_sqrt at q,
  swap,
  norm_num,
  rw real.sq_sqrt at q,
  swap,
  norm_num,
  have h2 := add_le_add q h,
  have h3 : 3 ≤ 2*real.sqrt(2),
  linarith,
  have h4 : (9:ℝ) ≤ 8,
  swap, 
  linarith,
  have h5 := pow_le_pow_of_le_left (by norm_num) h3 2,
  rw [mul_pow, real.sq_sqrt] at h5,
  norm_num at h5,
  norm_num,
end

example (a b c : ℝ ) : a ≤ b → c ≥ 0 → a*c ≤ b*c := mul_le_mul_of_nonneg_right

lemma part_a2 : real.sqrt 20 - real.sqrt 12 > 1 :=
begin
  by_contra,
  push_neg at h,
  have q : (real.sqrt 20 - real.sqrt 12)*(real.sqrt 20 + real.sqrt 12) ≤ 1*(real.sqrt 20 + real.sqrt 12),
  {apply mul_le_mul_of_nonneg_right (h),
    apply add_nonneg,
    repeat {apply real.sqrt_nonneg,},
    },
  simp at q,
  rw sub_mul_add at q,
  sorry
end

lemma part_b (n : ℤ) : even (n^2) → even n :=
begin
  rw sq,
  by_contra,
  push_neg at h,
  cases h with hsq hodd,
  rw int.odd_iff_not_even.symm at hodd,
  have q : odd (n*n), 
  apply odd.mul,
  repeat {assumption},
  finish,  
end

example (a b: ℕ ) : a ∣ b = 0 zmod a := by library_search

lemma part_c (n : ℤ) (h : ∃ m : ℤ, n = m^3 - m) : 6 ∣ n :=
begin
  cases h with m h,
  subst h,
  
end


import tactic
import data.real.basic -- for part d

lemma part_a (n : ℕ) : (11 : ℤ) ∣ 5^(2*n) - 3^n :=
begin
  induction n with x hx,
  { norm_num, },
  rw [nat.succ_eq_add_one, mul_add,pow_add,mul_one],
  nth_rewrite 1 pow_succ,
  cases hx with m hm,
  have q : (5:ℤ)^2 = (22:ℤ) + (3:ℤ), norm_num,
  rw [q, mul_add],
  nth_rewrite 2 mul_comm,
  have p : (3:ℤ) * (5:ℤ) ^ (2 * x) - (3:ℤ) * (3:ℤ) ^ x = (3:ℤ) * ((5:ℤ)^(2*x) - (3:ℤ)^x),
  {
    rw mul_sub _,
  },
  use (2:ℤ) * (5:ℤ) ^ (2 * x) + (3:ℤ)*m,
  linear_combination 3 * hm,
end


-- let m be n-1 so 4n-1 becomes 4m+3
lemma part_b (m : ℕ) : (2^(4 * m + 3)) % 10 = 8 :=
begin
  induction m with x hx,
  norm_num,
  rw [pow_add, pow_mul,pow_succ, ←pow_mul, mul_assoc, ← pow_add],
  rw [nat.mul_mod, hx],
  norm_num,
end

-- "positive" is not needed here
lemma part_c (n : ℕ) : 9 ∣ n^3 + (n+1)^3 + (n+2)^3 :=
begin
  induction n with x hx,
  { norm_num, },
  repeat {rw [← nat.add_one]},
  have h: 9 ∣ 27 + 27*x + 9 * x^2,
  {
    use 3+3*x+x^2,
    ring_nf,
  },
  have p := nat.dvd_add h hx,
  convert p using 1,
  ring,
end

-- also works for n=0
lemma part_d (n : ℕ) (x : ℝ) (hx : 2 ≤ x) : (n : ℝ) * x ≤ x^n :=
begin
  induction n with h hh,
  { norm_num, },
  by_cases hn : h = 0, 
  {
    rw hn,
    simp only [nat.cast_one, one_mul, pow_one],
  },
  { 
    rw [pow_succ, nat.cast_succ,mul_comm],
    rw mul_le_mul_left,
    have p : ↑h + 1 ≤ ↑h * x,
    {
      have g : ↑h * 2 ≤ ↑h * x,
      {
        rwa mul_le_mul_left,
        norm_cast,
        exact pos_iff_ne_zero.mpr hn,
      },
      have q : ↑h + 1 ≤ ↑h * (2: ℝ),
      {
        norm_cast,
        rw mul_two,
        simp only [add_le_add_iff_left],
        exact nat.one_le_iff_ne_zero.mpr hn,
      },
      exact le_trans q g,
    },
    apply le_trans p,
    exact hh,
    linarith,
  }
end

lemma part_e (n : ℕ) (hn : 3 ≤ n) : 4^n + 3^n + 2^n < 5^n :=
begin
  induction n with h hx,
  norm_num at hn,
  repeat {rw [pow_succ]},
  have p : 2 * 2 ^ h < 5 * 2 ^ h, by simp only [mul_lt_mul_right, pow_pos, nat.succ_pos', nat.bit0_lt_bit1_iff, nat.one_le_bit0_iff],
  have q : 3 * 3 ^ h < 5 * 3 ^ h, by simp only [mul_lt_mul_right, pow_pos, nat.succ_pos', bit1_lt_bit1, nat.one_lt_bit0_iff],
  have r : 4 * 4 ^ h < 5 * 4 ^ h, by  simp only [mul_lt_mul_right, pow_pos, nat.succ_pos', nat.bit0_lt_bit1_iff],
  have t : 5*4^h + 5*3^h + 5*2^h = 5*(4^h+3^h+2^h), by ring_nf,
  have s := add_lt_add (add_lt_add r q) p,
  rw t at s,
  by_cases hh: h = 2 , {
    rw hh,
    norm_num,
  },
  {
    have hhh : 3 ≤ h, { 
      obtain tt:= nat.of_le_succ hn,
      have := nat.succ_ne_succ.mpr hh,
      norm_num at this,
      cases tt,
      {  
        exact tt,
      },
      {
        exfalso,
        exact this tt.symm,
      }
    },
    apply lt_trans s,
    rw mul_lt_mul_left,
    {
      exact hx hhh,
    },
    norm_num,
  }
end



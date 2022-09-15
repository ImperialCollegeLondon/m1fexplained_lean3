import tactic
import data.real.basic -- for part d


lemma exercise (n : ℕ) (q : ℝ) (hgq : 0 < q) (hlq : q < (1/2 : ℝ)) : (1 + q)^n ≤ 1 + (2:ℝ)^n * q :=
begin
  induction n with h hh,
  norm_num,
  exact le_of_lt hgq,
  by_cases hz : h ≥ 1,
  swap,
  rw [not_le, nat.lt_one_iff] at hz,
  rw hz,
  simp only [pow_one, add_le_add_iff_left, two_mul,le_add_iff_nonneg_left],
  exact le_of_lt hgq,
  rw [pow_succ, pow_succ],
  have p : (1+q)*(1 + q) ^ h ≤ (1+q)*(1 + 2 ^ h * q),
  {
    rwa mul_le_mul_left,
    linarith,
  },
  apply le_trans p,
  ring_nf,
  rw [two_mul],
  apply add_le_add,
  {
    rw mul_le_mul_right,
    {
      rw [add_comm, add_assoc],
      apply add_le_add,
      refl,
      have t : 0 < (2:ℝ) := by simp only [zero_lt_bit0, zero_lt_one],
      rw ← mul_le_mul_left t,
      ring_nf,
      have s : 1*(2 : ℝ) ^ h + 2 ≤( 2 : ℝ)*(2 : ℝ)^h,
      {
        rw two_mul,
        simp only [one_mul, add_le_add_iff_left],
        norm_cast,
        nth_rewrite 0 ← pow_one 2,
        suffices : 1 ≤ h,
        {
          refine pow_mono _ hz,
          exact one_le_two,
        },
        exact hz,
      },
      have r: (2:ℝ) * q * (2 : ℝ) ^ h + 2 ≤ 1*(2 : ℝ) ^ h + 2,
      rw add_le_add_iff_right,
      {
        rw mul_le_mul_right,
        {
          linarith,
        },
        exact pow_pos t h,
      },
      apply le_trans r s,   
    },
    exact hgq,
  },
  refl,
end





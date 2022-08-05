import tactic

/-
Prove by induction that it's possible to pay, without requiring
change, any whole number of roubles greater than 7 with
banknotes of value 3 roubles and 5 roubles
-/


example (n : ℕ) (hn : 7 < n) : ∃ a b : ℕ, n = 3 * a + 5 * b :=
begin
  -- Remark: this looks a little subtle to me, you will have
  -- to think about exactly what statement you want to prove
  -- by induction.
  generalize hd : n - 8 = d,
  have hnd : n = d + 8,
  { linarith, },
  { rw hnd,
    clear hnd hd hn n,
    induction d with k hk,
    { use 1,
      use 1, 
      norm_num, },
    { change ∃ a b, k + 1 + 8 = 3 * a + 5 * b,
      rcases hk with ⟨a, b, hp⟩,
      by_cases h : 0 < b,
      { use a+2, 
        use b-1, 
        linarith, },
      { push_neg at h, 
        simp only [nonpos_iff_eq_zero] at h, 
        subst h, 
        norm_num at hp, 
        have hk: 6 < k + 8,
        { omega, },
        rw hp at hk, 
        have h3: 0 < 3,
        { simp, },
        have ha: 2 < a,
        { exact (mul_lt_mul_left h3).mp hk, },
        refine ⟨a-3, 2, _⟩, 
        ring_nf,
        change k + 8 + 1 = 3 * (a - 3) + 10,
        rw hp,
        linarith, } } },
end

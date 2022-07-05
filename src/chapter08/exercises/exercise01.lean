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
  sorry
end
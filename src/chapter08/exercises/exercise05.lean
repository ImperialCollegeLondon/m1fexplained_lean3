import tactic
import data.real.basic -- for part d

lemma part_a (n : ℕ) : (11 : ℤ) ∣ 5^(2*n) - 3^n :=
begin
  sorry
end

-- let m be n-1 so 4n-1 becomes 4m+3
lemma part_b (m : ℕ) : (2^(4 * m + 3)) % 10 = 8 :=
begin
  sorry
end

-- "positive" is not needed here
lemma part_c (n : ℕ) : 9 ∣ n^3 + (n+1)^3 + (n+2)^3 :=
begin
  sorry
end

-- also works for n=0
lemma part_d (n : ℕ) (x : ℝ) (hx : 2 ≤ x) : (n : ℝ) * x ≤ x^n :=
begin
  sorry
end

lemma part_e (n : ℕ) (hn : 3 ≤ n) : 4^n + 3^n + 2^n < 5^n :=
begin
  sorry
end

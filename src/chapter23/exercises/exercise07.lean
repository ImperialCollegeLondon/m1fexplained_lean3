import topology.instances.real 

open filter real
open_locale topology


theorem part_i_a (a : ℕ → ℝ) (h1 : a 1 = 1)
  (h2 : ∀ n : ℕ, a (n + 1) = (a n ^ 2 + 2) / (2 * a n)) :
  ∃ M : ℝ, ∀ n : ℕ, abs (a n) ≤ M :=
begin 
  sorry 
end 

theorem part_i_b (a : ℕ → ℝ) (h1 : a 1 = 1) (h2 : ∀ n, a (n+1) = (a n ^ 2 + 2) / (2 * a n)) :
  ∀ n, n ≥ 2 → a n ≥ a (n+1) :=
begin 
  sorry 
end 

theorem part_ii (a : ℕ → ℝ) (h1 : a 1 = 1) (h2 : ∀ n, a (n+1) = (a n ^ 2 + 2) / (2 * a n)) :
  tendsto a at_top (𝓝 2) :=
begin 
  sorry 
end 

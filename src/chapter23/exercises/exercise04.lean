import topology.instances.real 

namespace chapter23.exercise04

open filter real
open_locale topology

theorem part_i_a :
  ∃ b : ℝ, ∀ n, abs (n^3 / (n^3 - 1) : ℝ) ≤ b :=
begin 
  sorry, 
end 

theorem part_i_c (n : ℕ) :
  (n : ℝ)^3 / (n^3 - 1) ≥ (n + 1)^3 / ((n + 1)^3 - 1) :=
begin 
  sorry, 
end 

theorem part_i_d (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = n^3 / (n^3 - 1)) :
  ∃ l : ℝ, tendsto a at_top (𝓝 l) :=
begin 
  sorry 
end 

theorem part_ii_a :
  ∃ M : ℝ, ∀ m : ℕ, abs (2 ^ (1 / m)) ≤ M :=
begin 
  sorry 
end 

theorem part_ii_c (n : ℕ) : 
  2^(1/n) ≥ 2^(1/(n+1)) :=
begin 
  sorry 
end 

theorem part_ii_d (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = 2 ^ (1 / n)) :
  ∃ l : ℝ, tendsto a at_top (𝓝 l) :=
begin 
  sorry 
end 

theorem part_iii_a :
  ∃ b : ℝ, ∀ n : ℕ, abs (1 - (-1)^n / ↑n) ≤ b :=
begin 
  sorry 
end 

theorem part_iii_b (n : ℕ) :
  ¬ (∀ n : ℕ, (1 : ℝ) - (-1)^n / n ≤ 1 - (-1)^(n+1) / (n+1)) :=
begin 
  sorry 
end 

theorem part_iii_c (n : ℕ) : 
  ¬ (∀ m : ℕ, (1 - (-1)^n / n.cast : ℝ) ≥ (1 - (-1)^(n+m) / (n+m).cast : ℝ)) :=
begin 
  sorry 
end 

theorem part_iii_d (f : ℕ → ℝ) (hf : ∀ n : ℕ, f n = 1 - (-1)^n / n) :
  ∃ r : ℝ, tendsto f at_top (𝓝 r) :=
begin 
  sorry 
end 

theorem part_iv_a :
  ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, abs (5*n - n^2 : ℝ) ≥ m :=
begin 
  sorry 
end 

theorem part_iv_b :
  ¬ (∀ n : ℕ, abs (5*n - n^2 : ℝ) ≤ abs (5*(n+1) - (n+1)^2 : ℝ)) :=
begin 
  sorry 
end 

theorem part_iv_c :
  ¬ (∀ n : ℕ, abs (5*n - n^2 : ℝ) ≥ abs (5*(n+1) - (n+1)^2 : ℝ)) :=
begin 
  sorry 
end 

theorem part_iv_d :
  tendsto (λ n : ℕ, abs (5*n - n^2 : ℝ)) at_top at_top :=
begin 
  sorry 
end 

end chapter23.exercise04

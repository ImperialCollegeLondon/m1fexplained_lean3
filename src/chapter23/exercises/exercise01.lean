import data.real.sqrt
import data.complex.exponential

open filter real
open_locale topology

theorem part_i :
  tendsto (λ n : ℕ, n / (n + 5) : ℕ → ℝ) at_top (𝓝 1) :=
begin 
  rw tendsto,
  
end 

theorem part_ii :
  tendsto (λ n : ℕ, 1 / sqrt (n + 5)) at_top (𝓝 0) :=
begin 
  sorry 
end 

theorem part_iii :
  tendsto (λ n : ℕ, ↑n * sqrt n / (n + 5)) at_top at_top :=
begin 
  sorry
end 

theorem part_iv :
  tendsto (λ n : ℕ, ((-1)^n * sin n) / sqrt n ) at_top (𝓝 0) :=
begin 
  sorry 
end 

theorem part_v :
  tendsto (λ n : ℕ, (↑n^3 - 2*sqrt n + 7) / (2 - n^2 - 5*n^3)) at_top (𝓝 (-1/5)) :=
begin 
  sorry 
end  

theorem part_vi (n : ℕ) :
  ¬∃ l : ℝ, tendsto (λ n, (1 - (-1)^n * n) / n : ℕ → ℝ) at_top (𝓝 l) :=
begin 
  sorry 
end 

theorem part_vii :
  tendsto (λ n : ℕ, sqrt (n + 1) - sqrt n) at_top (𝓝 0) :=
begin 
  sorry
end 

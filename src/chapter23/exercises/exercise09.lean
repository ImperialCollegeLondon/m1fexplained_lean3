import topology.instances.real 

open filter real
open_locale topological_space 

variable a : ℕ → ℝ 

theorem part_a : 
  ¬ (∀ l : ℝ, tendsto a at_top (𝓝 l)) ↔ tendsto a at_top at_top :=
begin 
  sorry 
end 

theorem part_c : 
  (∀ R > 0, ∃ N : ℕ, ∀ n ≥ N, a n > R) ↔ (tendsto a at_top at_top) :=
begin 
  sorry 
end 

theorem part_d : 
  ¬ (∀ L : ℝ, ∀ ε : ℝ, ∃ N : ℕ, ∀ n ≥ N, abs (a n - L) > ε) ↔ (tendsto a at_top at_top) :=
begin 
  sorry 
end 

theorem part_e : 
  (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, a n > 1 / ε) ↔ (tendsto a at_top at_top) :=
begin 
  sorry 
end 

theorem part_f : 
  ¬ (∀ n : ℕ, a (n+1) > a n) ↔ (tendsto a at_top at_top) :=
begin 
  sorry 
end 

theorem part_g : 
  ¬ (∃ N : ℕ, ∀ R > 0, ∀ n ≥ N, a n > R) ↔ (tendsto a at_top at_top) :=
begin 
  sorry 
end 

theorem part_h : 
  ¬ (∀ R : ℝ, ∃ n : ℕ, a n > R) ↔ (tendsto a at_top at_top) :=
begin 
  sorry 
end 

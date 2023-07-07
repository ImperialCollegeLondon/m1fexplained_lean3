import topology.instances.real 

open filter real
open_locale topology

theorem problem_5 (a : ℝ) (f : ℕ → ℝ) :
  (∃ N, ∀ ε > 0, ∀ n ≥ N, abs (f n - a) < ε) ↔ (∃ N, ∀ n ≥ N, f n = a) :=
begin 
  sorry 
end 

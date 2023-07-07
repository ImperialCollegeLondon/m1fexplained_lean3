import topology.instances.real 

namespace chapter23.exercise05

open filter real
open_locale topology

theorem problem_5 (a : ℝ) (f : ℕ → ℝ) :
  (∃ N, ∀ ε > 0, ∀ n ≥ N, abs (f n - a) < ε) ↔ (∃ N, ∀ n ≥ N, f n = a) :=
begin 
  sorry 
end 

end chapter23.exercise05

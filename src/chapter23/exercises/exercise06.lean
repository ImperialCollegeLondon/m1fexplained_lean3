import topology.instances.real 

namespace chapter23.exercise06

open filter real
open_locale topology

theorem problem_6 (f : ℕ → ℝ) (hf : ∀ n, f (n + 1) ≤ f n)
  (hf_bdd : ∃ a, ∀ n, f n ≤ a) :
  ∃ a, tendsto f at_top (𝓝 a) :=
begin 
  sorry 
end 

end chapter23.exercise06

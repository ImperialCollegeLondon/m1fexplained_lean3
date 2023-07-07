import topology.instances.real 

namespace chapter23.exercise02

open filter real
open_locale topology

theorem problem_2 (X : Type*) [topological_space X] (a : ℕ → X) (l₁ l₂ : X)
  (h₁ : tendsto a at_top (𝓝 l₁)) (h₂ : tendsto a at_top (𝓝 l₂)) :
  l₁ = l₂ :=
begin 
  sorry 
end 

end chapter23.exercise02

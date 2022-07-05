import topology.instances.real 

open filter real
open_locale topological_space 

theorem leibeck_23_3 (S : set ℝ) (c : ℝ) (hc : is_lub S c) :
  ∃ (f : ℕ → ℝ), (∀ n, f n ∈ S) ∧ tendsto f at_top (𝓝 c) :=
begin 
  sorry 
end 

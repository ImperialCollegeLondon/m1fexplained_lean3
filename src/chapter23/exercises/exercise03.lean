import topology.instances.real 

namespace chapter23.exercise03

open filter real
open_locale topology

theorem leibeck_23_3 (S : set ℝ) (c : ℝ) (hc : is_lub S c) :
  ∃ (f : ℕ → ℝ), (∀ n, f n ∈ S) ∧ tendsto f at_top (𝓝 c) :=
begin 
  sorry 
end 

end chapter23.exercise03

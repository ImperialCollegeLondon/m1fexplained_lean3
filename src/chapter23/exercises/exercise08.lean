import topology.instances.real
import data.complex.exponential
import data.real.irrational 

open filter real
open_locale topological_space 
open_locale big_operators 

noncomputable def e : ℕ → ℝ := λ n, ∑ i in finset.range(n+1), 1 / (nat.factorial i)

theorem part_a (n : ℕ) :
  ∃ p : ℕ, e n = p / (nat.factorial n) :=
begin   
  sorry 
end 

theorem part_b (n : ℕ) : 
  0 < exp 1 - e n ∧ exp 1 - e n < 1 / (n * nat.factorial n) :=
begin 
  sorry 
end 

theorem part_c : 
  ∃ p : ℕ → ℝ, ∀ n : ℕ, 0 < exp 1 * nat.factorial n - e n ∧ 
  exp 1 * nat.factorial n - e n < 1 / (n * nat.factorial n) :=
begin 
  sorry 
end 

-- Assume e is rational, then show n!e ∈ ℤ for some n.
theorem part_d : 
  irrational (exp 1) := 
begin 
  sorry 
end 

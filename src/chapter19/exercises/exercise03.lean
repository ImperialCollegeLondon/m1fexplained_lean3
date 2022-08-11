import tactic
import data.real.basic
/-
Two functions f, g : ℝ → ℝ are such that for all x ∈ ℝ,
g(x) = x² + x + 3, and (g ∘ f)(x) = x² − 3x + 5.
Find the possibilities for f .
-/

def g : ℝ → ℝ := λ x, x^2+x+3

-- Edit the "∀ x, f x = 37" part of the claim below and replace it with your answer 
example (f : ℝ → ℝ) : ((g ∘ f) = λ x, x^2-3*x+5) ↔ ∀ x, f x = 37 :=
begin
  sorry
end

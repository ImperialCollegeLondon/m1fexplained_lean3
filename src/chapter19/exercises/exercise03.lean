import tactic
import data.real.basic

/-
Two functions f, g : ℝ → ℝ are such that for all x ∈ ℝ,
g(x) = x² + x + 3, and (g ∘ f)(x) = x² − 3x + 5.
Find the possibilities for f .
-/

def g : ℝ → ℝ := λ x, x^2+x+3

example (x y : ℝ) : y^2 + y + 3 = x^2 - 3 * x + 5 → y = x - 2 ∨ y = -x + 1 :=
begin
  intro h,
  have h' : y^2 + y + 3 = x^2 - 3 * x + 5 ↔ (y - (x - 2)) * (y - (-x + 1)) = 0,
  {
    split,
    intro h,
    nlinarith,
    intro h, 
    nlinarith,
  },
  simp [h', zero_eq_mul] at h,
  sorry,
end

example (a b : ℝ) (h : a * b = 0) : (a = 0 ∨ b = 0) :=
begin
  exact zero_eq_mul.mp (eq.symm h),
end

example (a b : ℝ) (h : a - b = 0) : (a = b) :=
begin
  library_search,
end

-- Edit the "∀ x, f x = 37" part of the claim below and replace it with your answer 
example (f : ℝ → ℝ) : ((g ∘ f) = λ x, x^2-3*x+5) ↔ ∀ x, f x = x - 2 ∨ f x = - x + 1 :=
begin
  simp [function.funext_iff, g],
  split,
  {
    intros h x,
    specialize h x,
    let y := f x,
    have : y^2 + y + 3 = x^2 - 3 * x + 5 → y = x - 2 ∨ y = -x + 1,
    {
      intro h,
      sorry
    },
    specialize this h,
    exact this,
  },
  {
    intros h x,
    specialize h x,
    cases h with h1 h2,
    simp [h1],
    ring,
    simp [h2],
    ring,
  },
end




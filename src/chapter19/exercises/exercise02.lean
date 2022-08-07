import data.real.basic
import tactic
/-
Q2. The functions f , g : ℝ → ℝ are defined as follows:
f(x) = 2x if 0 ≤ x ≤ 1, and f (x) = 1 otherwise;
g(x) = x^2 if 0 ≤ x ≤ 1, and g(x) = 0 otherwise.

Give formulae describing the functions `g ∘ f` and
`f ∘ g`. (Draw the graphs of these functions.)
-/

noncomputable theory

def f (x : ℝ) := if 0 ≤ x ∧ x ≤ 1 then 2 * x else 1

def g (x : ℝ) := if 0 ≤ x ∧ x ≤ 1 then x ^ 2 else 0

example : g ∘ f = sorry -- replace with formula for g ∘ f
:= sorry

example : f ∘ g = sorry -- replace with formula for f ∘ g
:= sorry
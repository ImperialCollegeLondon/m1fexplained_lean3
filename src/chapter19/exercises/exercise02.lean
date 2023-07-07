import data.real.basic
import tactic

namespace chapter19.exercise02

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

example (x : ℝ) : (g ∘ f) x = if 0 ≤ x ∧ x ≤ 1/2 then 4 * x ^ 2 else if 1/2 < x ∧ x ≤ 1 then 0 else 1 -- replace with formula for g ∘ f
:= 
begin
  change g (f x) = _,
  unfold f,
  unfold g,
  split_ifs;
  try {simp};
  try {rw not_and_distrib at *};
  try {cases h};
  try {cases h_1};
  try {cases h_2};
  try {cases h_3};
  try {linarith},
end

example (x : ℝ) : (f ∘ g) x = if 0 ≤ x ∧ x ≤ 1 then 2 * x ^ 2 else 0 
:= 
begin
  change f (g x) = _,
  unfold f,
  unfold g,
  split_ifs;
  try {simp};
  try {rw not_and_distrib at *};
  try {cases h};
  try {cases h_1};
  try {nlinarith},
end

end chapter19.exercise02

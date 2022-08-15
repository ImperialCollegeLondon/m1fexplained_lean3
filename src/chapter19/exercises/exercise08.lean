/-
8. The manufacturers of the high-fibre cereal “Improve Your Functions”
are offering a prize of £1000 to anyone who can find three different
integers a, b, c and a polynomial P(x) with integer coefficients, such that
P(a) = b, P(b) = c and P(c) = a.
Critics Ivor Smallbrain and Greta Picture spend several long evenings
trying to solve this, without success.
Prove that nobody will win the prize.
(Hint: Observe that P(x) − P(y) = (x − y)Q(x, y), where Q(x, y) is a
polynomial in x, y with integer coefficients. Substitute x = a, y = b, etc.,
into this equation and see what happens.)
-/

import tactic
import data.polynomial.eval

open_locale polynomial -- notation for polynomials

open polynomial

example : ¬ ∃ a b c : ℤ, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ∃ P : ℤ[X], eval P a = b ∧ eval P b = c ∧ eval P c = a :=
begin
  sorry
end
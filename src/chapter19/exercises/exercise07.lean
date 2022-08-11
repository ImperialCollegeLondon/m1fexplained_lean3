/-
7. (a) Let S = {1, 2, 3} and T = {1, 2, 3, 4, 5}. How many functions are
there from S to T ? How many of these are 1-1?
(b) Let |S| = m, |T | = n with m ≤ n. Show that the number of 1-1 func-
tions from S to T is equal to n(n − 1)(n − 2) · · ·(n − m + 1).
-/
import tactic

open_locale classical

-- replace 37 with the right number
lemma parta (S T : Type) [fintype S] [fintype T] (hS : fintype.card S = 3) (hT : fintype.card T = 5) :
  fintype.card (S → T) = 37 :=
begin
  sorry
end

-- replace 37 with the right number
lemma parta' (S T : Type) [fintype S] [fintype T] (hS : fintype.card S = 3) (hT : fintype.card T = 5) :
  fintype.card {f : S → T // function.injective f} = 37 :=
begin
  sorry
end

open_locale big_operators -- for Π 

lemma partb (S T : Type) [fintype S] [fintype T] (m n : ℕ) (hmn : m ≤ n) : 
  fintype.card {f : S → T // function.injective f} = ∏ i in finset.Icc (n - m + 1) n, i :=
begin
  sorry
end 
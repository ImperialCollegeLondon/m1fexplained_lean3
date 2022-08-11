/-
6. (a) Find an onto function from ℕ to ℤ.
(b) Find a 1-1 function from ℤ to ℕ.
-/

import tactic

open function

def f (n : ℕ) : ℤ := 37 -- replace 37 with a surjective function

lemma f_surj : surjective f :=
begin
  sorry
end

def g (z : ℤ) : ℕ := 37 -- replace 37 with an injective function

lemma g_inj : injective g :=
begin
  sorry
end

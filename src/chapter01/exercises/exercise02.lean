import data.real.basic

-- Let B,C,D,E be the following sets
def B : set ℝ := {x | x^2 < 4}
def C : set ℝ := {x | 0 ≤ x ∧ x < 2}
def D : set ℝ := {x | ∃ n : ℤ, x = n ∧ x^2 < 1}
def E : set ℝ := {1}


#print notation ¬ 
#print notation ⊆ 
#print notation *
#print notation +
-- Which pair of these sets has the property that neither is contained in the other?
lemma parta : ∃ S T ∈ ({B, C, D, E} : set (set ℝ)), ¬ (S ⊆ T) ∧ ¬ (T ⊆ S) :=
begin
  use D,
  use E,
  split,
  {simp,},
  {split,{simp,},
         {split,{
          rw set.subset_def,
          push_neg,use 0,split,{rw D,use 0,norm_num,},
                               {rw E,simp,},
         },{rw set.subset_def,
            push_neg,use 1,split,{simp[E],},
                                 {simp[D],},
         },},
                },
end

-- If X is either B,C,D,E and E ⊆ X ⊆ B, what else can we deduce about X? 
-- Note that figuring out what to prove is part of the question
lemma partb (X : set ℝ) (hX : X ∈ ({B,C,D,E} : set (set ℝ))) (h1 : E ⊆ X)
(h2 : X ⊆ B) : sorry :=
begin
  sorry
end

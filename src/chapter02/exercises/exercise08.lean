import tactic

inductive colour : Type
| red : colour
| blue : colour
| green : colour

def horrify : ℕ × ℕ × ℕ → colour → ℕ × ℕ × ℕ
| (r, b + 1, g + 1) red   := (r + 2, b, g)
| (r + 1, b, g + 1) blue  := (r, b + 2, g)
| (r + 1, b + 1, g) green := (r, b, g + 2)
| (r, b, g) _             := (r, b, g)

/-- Critic Ivor Smallbrain is watching the horror movie Salamanders on a
Desert Island. In the film, there are 30 salamanders living on a desert
island: 15 are red, 7 blue and 8 green. When two of a different colour
meet, horrifyingly they both change into the third colour. (For example,
if a red and a green meet, they both become blue.) When two of the same
colour meet, they change into both of the other colours. (For example, if
two reds meet, one becomes green and one becomes blue.) It is all quite
terrifying.

In between being horrified and terrified, Ivor idly wonders whether it
could ever happen that at some instant in the future, all of the salaman-
ders would be red. It turns out that this would never happen. -/
lemma salamander : ¬ ∃ (l : list colour), list.foldl horrify (15, 7, 8) l = (30, 0, 0) :=
begin
  sorry
end

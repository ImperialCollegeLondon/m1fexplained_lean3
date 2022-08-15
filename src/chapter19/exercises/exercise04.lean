/-
Let X, Y, Z be sets, and let f : X → Y and g : Y → Z be functions.
(a) Given that g ∘ f is onto, can you deduce that f is onto? Give a proof
or a counterexample.
(b) Given that g ∘ f is onto, can you deduce that g is onto?
(c) Given that g ∘ f is 1-1, can you deduce that f is 1-1?
(d) Given that g ∘ f is 1-1, can you deduce that g is 1-1?
-/
import tactic

open function -- so we can write `injective`/`surjective` instead of `function.injective`/`function.surjective`

-- For each of the parts below, if you think it's false then stick `¬` in front of it before you start proving it.

lemma parta : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), surjective (g ∘ f) → surjective f :=
begin
  sorry
end

lemma partb : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), surjective (g ∘ f) → surjective g :=
begin
  sorry
end

lemma partc : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), injective (g ∘ f) → injective f :=
begin
  sorry
end

lemma partd : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), injective (g ∘ f) → injective g :=
begin
  sorry
end

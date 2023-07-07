/-
Let X, Y, Z be sets, and let f : X → Y and g : Y → Z be functions.
(a) Given that g ∘ f is onto, can you deduce that f is onto? Give a proof
or a counterexample.
(b) Given that g ∘ f is onto, can you deduce that g is onto?
(c) Given that g ∘ f is 1-1, can you deduce that f is 1-1?
(d) Given that g ∘ f is 1-1, can you deduce that g is 1-1?
-/
import tactic

namespace chapter19.exercise04

open function -- so we can write `injective`/`surjective` instead of `function.injective`/`function.surjective`

-- For each of the parts below, if you think it's false then stick `¬` in front of it before you start proving it.


-- The below is for counterexamples
-- Let X be {a}
inductive X : Type
| a : X

-- Let Y be {b,c}
inductive Y : Type
| b : Y
| c : Y

-- Let Z be {d}
inductive Z : Type
| d : Z

-- Define f by f(X.a)=Y.b
def f : X → Y
| X.a := Y.b

-- define g by g(Y.b)=g(Y.c)=Z.d
def g : Y → Z
| Y.b := Z.d
| Y.c := Z.d

lemma parta : ¬ (∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), surjective (g ∘ f) → surjective f) :=
begin
  by_contra,
  specialize h X Y Z f g,
  have hgf : surjective (g ∘ f),
  { rintro ⟨⟩,
    use X.a,
    refl },
  obtain ⟨⟨⟩, ⟨⟩⟩ := h hgf Y.c,
end

lemma partb : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), surjective (g ∘ f) → surjective g :=
begin
  intros X Y Z f g hgf b,
  obtain ⟨a, hgf⟩ := hgf b,
  exact ⟨f a, hgf⟩,
end

lemma gf_injective : injective (g ∘ f) :=
begin
  rintros ⟨⟩ ⟨⟩ _,
  refl,
end

lemma partc : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), injective (g ∘ f) → injective f :=
begin
  intros X Y Z f g hgf a b hf,
  have hg : g (f a) = g (f b),
  { rw hf },
  exact hgf hg,
end

lemma partd : ¬ (∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), injective (g ∘ f) → injective g) :=
begin
  by_contra,
  specialize h X Y Z f g,
  specialize h gf_injective,
  have hy : g Y.b = g Y.c,
  { unfold g },
  specialize h hy,
  simpa using h,
end

end chapter19.exercise04

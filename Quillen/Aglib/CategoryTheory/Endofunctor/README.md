# Fixed words of an endofunctor

[FixedWords](FixedWords.lean) is a general candidate for
`Aglib.CategoryTheory.Endofunctor.FixedWords`. Its declarations use the native
namespace `CategoryTheory.Functor.FixedWords`. For a category `D`, an
endofunctor `F : D ⥤ D` and a specified natural isomorphism
`P : F ⋙ F ≅ F ⋙ F`, it defines `power F`, the insertion word `beta F P`
and the accumulated `fixedWord F P`. The original functor associators and
whiskering order remain explicit.

`power_succ_left`, `beta_succ_hom_app` and `fixedWord_succ_hom_app` give the
complete power and component recursion. `fixedWord_two` is the supplied `P`;
`fixedWord_three` and `fixedWord_three_hom_app` retain the specified
three-factor word. These statements require no braid or involution relation
and assert no independence from the chosen word.

The current consumer is
[GeometricConeFixedWords](../../../KTheory/Bass/GeometricConeFixedWords.lean),
which instantiates these words with the actual unlooped Bass cone functor and
its geometric square isomorphism. Its scalar-action, seed and telescope
comparisons remain in the Bass application; they are not hypotheses or
results of this general candidate.

## Global sections and finite Bass interchange

| Import after `Quillen.` | Principal interface |
| --- | --- |
| `Aglib.CategoryTheory.Endofunctor.FixedWords` | `CategoryTheory.Functor.FixedWords.power`, `beta`, `fixedWord` and their specified recursion; no word-independence or braid premise |

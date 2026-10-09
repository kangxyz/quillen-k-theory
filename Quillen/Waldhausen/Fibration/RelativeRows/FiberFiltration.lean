import Quillen.Waldhausen.Fibration.RelativeRows.SplitFiber
import Quillen.Waldhausen.Fibration.RelativeRows.FiltrationWeakMaps

/-! # The original split fiber has the literal constant initial filtration

Every initial interval [0,i+1] is sent to the original one-row interval
[0,1]. The original object, identity structural arrows and every original
morphism are therefore retained exactly, before nerves or realization.
-/
noncomputable section
open CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

@[simp] theorem fiber_initialFiltration_obj (n : SimplexCategory) (X : C) (i : Fin (n.len+1)) :
    ((initialFiltrationFunctor N n).obj ((fiber N n).obj X)).obj i = X := rfl

@[simp] theorem fiber_initialFiltration_arrow (n : SimplexCategory) (X : C)
    {i j : Fin (n.len+1)} (f : i ⟶ j) :
    ((initialFiltrationFunctor N n).obj ((fiber N n).obj X)).map f = 𝟙 X := rfl

@[simp] theorem fiber_initialFiltration_map (n : SimplexCategory) {X Y : C}
    (f : X ⟶ Y) (i : Fin (n.len+1)) :
    ((initialFiltrationFunctor N n).map ((fiber N n).map f)).app i = f := rfl

/-- The unchanged original fiber functor is sent to the actual constant-chain functor. -/
@[simp] theorem fiber_initialFiltrationFunctor (n : SimplexCategory) :
    fiber N n ⋙ initialFiltrationFunctor N n = Functor.const (Fin (n.len+1)) := by
  apply CategoryTheory.Functor.ext (F := fiber N n ⋙ initialFiltrationFunctor N n)
    (G := Functor.const (Fin (n.len+1))) (fun _ ↦ rfl)

end Quillen.Waldhausen.Fibration.RelativeRows

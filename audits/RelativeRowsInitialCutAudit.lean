import Quillen.Waldhausen.ExtensionCategory.IsomorphicSources
import Quillen.Waldhausen.ExtensionCategory.IsomorphicSourceCubes
import Quillen.Waldhausen.Fibration.RelativeRows.InitialCut
import Quillen.Waldhausen.Fibration.RelativeRows.InitialCutArrows
import Quillen.Waldhausen.Fibration.RelativeRows.InitialCutExact
import Quillen.Waldhausen.SConstruction.Rows.OneRowIso
import Quillen.Waldhausen.Fibration.RelativeRows.InitialCutIso
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.ExtensionCategory.IsomorphicSources, `Quillen.Waldhausen.ExtensionCategory.IsomorphicSourceCubes, `Quillen.Waldhausen.Fibration.RelativeRows.InitialCut, `Quillen.Waldhausen.Fibration.RelativeRows.InitialCutArrows, `Quillen.Waldhausen.Fibration.RelativeRows.InitialCutExact, `Quillen.Waldhausen.SConstruction.Rows.OneRowIso, `Quillen.Waldhausen.Fibration.RelativeRows.InitialCutIso]
  let mut count : Nat := 0
  for origin in targets do
    let mut subtotal : Nat := 0
    for (name, _) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      unless env.header.moduleNames[index.toNat]! == origin do continue
      count := count + 1
      subtotal := subtotal + 1
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{origin}: {name} depends on unsupported assumption {dependency}"
      logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
    logInfo m!"ORIGIN_COUNT {origin}: {subtotal}"
  unless count == 77 do throwError "Expected 77 initial-cut origins, got {count}"
  logInfo m!"Audited all {count} initial-cut declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen
section Square
variable {C : Type u} [Category.{v} C] (W : Structure C)
example {X Y : ExtensionCategory.Obj W} (f : X ⟶ Y) [IsIso f.hom.left]
    (h : W.cof f.hom.right) : ExtensionCategory.cof W f := ExtensionCategory.cof_of_left_isIso W f h
example {X Y : ExtensionCategory.Obj W} (f : X ⟶ Y) [IsIso X.obj.hom]
    (h : W.cof f.hom.left) : ExtensionCategory.cof W f := ExtensionCategory.cof_of_top_isIso W f h
example {X Y : ExtensionCategory.Obj W} (f : X ⟶ Y)
    (hX : IsZero X.obj.left) (hY : IsZero Y.obj.left) (h : W.cof f.hom.right) :
    ExtensionCategory.cof W f := ExtensionCategory.cof_of_zero_sources W f hX hY h
example {X Y : ExtensionCategory.Obj (ExtensionCategory.waldhausenStructure W)} (f : X ⟶ Y)
    [IsIso X.obj.hom.hom.left] [IsIso Y.obj.hom.hom.left]
    (hl : ExtensionCategory.cof W f.hom.left)
    (hr : ExtensionCategory.cof W ((ExtensionCategory.postcompose (ExtensionCategory.waldhausenStructure W)
      W (ExtensionCategory.middle_exact W)).map f)) :
    ExtensionCategory.cof (ExtensionCategory.waldhausenStructure W) f :=
  ExtensionCategory.cof_cube_of_horizontal_left_isIso W f hl hr
example : QuotientRows.oneEvaluation W ⋙ QuotientRows.oneEmbedding W ≅ 𝟭 _ := QuotientRows.oneRoundTripIso W
example : QuotientRows.oneEmbedding W ⋙ QuotientRows.oneEvaluation W = 𝟭 C := QuotientRows.oneEmbedding_oneEvaluation W
end Square
namespace Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V) (n : SimplexCategory)
example : cutFunctor N n = reindex N (SimplexCategory.const n n 0) := rfl
example : (cutIndex n).toOrderHom 0 = 0 := rfl
example (i : Fin (n.len+1)) : (cutIndex n).toOrderHom i.succ = (0 : Fin (n.len+1)).succ := rfl
example (X : Obj N n) (p : Interval (addInitial.obj n)) :
    ((cutToId N n).app X).hom.hom.app p = X.obj.obj.map ((cutIndexToId n).app p) := rfl
example (X : Obj N n) : (waldhausenStructure N n).cof ((cutToId N n).app X) := cutToId_cof N n X
example (X : Obj N n) : ((cutArrow N n).obj X).obj.hom = (cutToId N n).app X := rfl
example {X Y : Obj N n} (f : X ⟶ Y) : ((cutArrow N n).map f).hom.left = (cutFunctor N n).map f := rfl
example {X Y : Obj N n} (f : X ⟶ Y) : ((cutArrow N n).map f).hom.right = f := rfl
example {X Y : Obj N n} (f : X ⟶ Y) (h : (waldhausenStructure N n).cof f) :
    ExtensionCategory.cof (waldhausenStructure N n) ((cutArrow N n).map f) := cutArrow_map_cof N f h
example : IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
    (ExtensionCategory.waldhausenStructure (waldhausenStructure N n)).cof
    (ExtensionCategory.waldhausenStructure (waldhausenStructure N n)).weq (cutArrow N n) := cutArrow_exact N n
example : Additivity.IsCofibrationTransformation (waldhausenStructure N n) (cutToId N n) (waldhausenStructure N n) :=
  cutToId_isCofibrationTransformation N n
example : fiberOrdinal n ≫ firstPair n = cutIndex n := fiberOrdinal_firstPair n
example : firstRow N n ⋙ QuotientRows.oneEvaluation V = first N n := firstRow_oneEvaluation N n
example : first N n ⋙ fiber N n ≅ cutFunctor N n := firstFiberCutIso N n
example : (first N n ⋙ fiber N n) ⋙ forget N n ≅ cutFunctor N n ⋙ forget N n := firstFiberCutAmbientIso N n
end Fibration.RelativeRows
end Quillen.Waldhausen

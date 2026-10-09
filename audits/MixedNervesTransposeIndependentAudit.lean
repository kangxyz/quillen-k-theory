import Quillen.Waldhausen.Fibration.MixedNerves.TransposeNerves
import Quillen.Waldhausen.Fibration.TrivialCofibrations.Category
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.MixedNerves.FineChains,
    `Quillen.Waldhausen.Fibration.MixedNerves.ChainCategories,
    `Quillen.Waldhausen.Fibration.MixedNerves.Transpose,
    `Quillen.Waldhausen.Fibration.MixedNerves.TransposeNerves]
  let mut counts : Array Nat := targets.map (fun _ ↦ 0)
  let mut total : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[idx.toNat]!
    let some i := targets.findIdx? (· == origin) | continue
    counts := counts.modify i (· + 1)
    total := total + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "{origin}: {name} depends on unsupported {ax}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing origin {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless total == 179 && counts == #[24, 78, 61, 16] do
    throwError "Expected fixed179 origins (24+78+61+16), found {total}: {counts}"
  logInfo m!"TOTAL_ORIGINS {total}: {counts}"
noncomputable section
open CategoryTheory Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.MixedNerves
open RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
  (n k : SimplexCategory)
example : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := coarseChainNerve N
example : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := cofChainNerve N
example : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := horizontalNerve N
example : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := horizontalCofNerve N
example : HorizontalChains N k = TrivialCofibrations.WeakCategory (pointwiseCoarse N k) := rfl
example : HorizontalCofChains N k =
    TrivialCofibrations.CofibrationCategory (pointwiseCof V k) (pointwiseCoarse N k) := rfl
example : horizontalInclusion N k =
    TrivialCofibrations.inclusion (pointwiseCof V k) (pointwiseCoarse N k) := rfl
example (X : HorizontalCofChains N k) : ((horizontalInclusion N k).obj X).obj = X.obj := rfl
example {X Y : HorizontalCofChains N k} (f : X ⟶ Y) :
    ((horizontalInclusion N k).map f).hom = f.hom := rfl
example {X Y : FineChain V k} (f : X ⟶ Y) :
    pointwiseCoarse N k f ↔ ∀ i, N.coarse.weq (f.hom.app i) := Iff.rfl
example {X Y : FineChain V k} (f : X ⟶ Y) :
    pointwiseCof V k f ↔ ∀ i, V.cof (f.hom.app i) := Iff.rfl
example (F : ComposableArrows (FineWeakCoarseChains N n) k.len)
    (i : Fin (n.len+1)) (j : Fin (k.len+1)) :
    ((transposeCoarse N n k F).obj i).obj.obj.obj j = (F.obj j).obj.obj.obj i := rfl
example (F : ComposableArrows (FineWeakCoarseChains N n) k.len)
    {i j : Fin (n.len+1)} (f : i ⟶ j) (t : Fin (k.len+1)) :
    ((transposeCoarse N n k F).map f).hom.hom.app t = (F.obj t).obj.obj.map f := rfl
example (F : ComposableArrows (FineWeakCoarseChains N n) k.len)
    (i : Fin (n.len+1)) {j t : Fin (k.len+1)} (f : j ⟶ t) :
    ((transposeCoarse N n k F).obj i).obj.obj.map f = (F.map f).hom.hom.app i := rfl
example (F : ComposableArrows (FineWeakChains N n) k.len)
    {i j : Fin (n.len+1)} (f : i ⟶ j) (t : Fin (k.len+1)) :
    V.cof (((transposeCof N n k F).map f).hom.hom.app t) :=
  ((transposeCof N n k F).map f).property.1 t
example (F : ComposableArrows (FineWeakCoarseChains N n) k.len) :
    untransposeCoarse N n k (transposeCoarse N n k F) = F := untranspose_transposeCoarse N n k F
example (F : ComposableArrows (HorizontalChains N k) n.len) :
    transposeCoarse N n k (untransposeCoarse N n k F) = F := transpose_untransposeCoarse N n k F
example (F : ComposableArrows (FineWeakChains N n) k.len) :
    untransposeCof N n k (transposeCof N n k F) = F := untranspose_transposeCof N n k F
example (F : ComposableArrows (HorizontalCofChains N k) n.len) :
    transposeCof N n k (untransposeCof N n k F) = F := transpose_untransposeCof N n k F
example : (coarseChainNerve N).flip ≅ horizontalNerve N := coarseTransposeIso N
example : (cofChainNerve N).flip ≅ horizontalCofNerve N := cofTransposeIso N
example : ((flipFunctor _ _ _).map (chainInclusion N)) ≫ (coarseTransposeIso N).hom =
    (cofTransposeIso N).hom ≫ horizontalNerveInclusion N := transpose_inclusion N
example (F : ComposableArrows (FineWeakCoarseChains N n) k.len) :
    ((coarseTransposeIso N).hom.app (op k)).app (op n) F = transposeCoarse N n k F := rfl
example (F : ComposableArrows (HorizontalCofChains N k) n.len) :
    ((cofTransposeIso N).inv.app (op k)).app (op n) F = untransposeCof N n k F := rfl
example : TheoremA.diagonalMap (chainInclusion N) ≫ (coarseDiagonalIso N).hom =
    (cofDiagonalIso N).hom ≫ TheoremA.diagonalMap (horizontalNerveInclusion N) := diagonal_inclusion N
example (F : ComposableArrows (FineWeakCoarseChains N (SimplexCategory.mk 0)) 0) :
    ((transposeCoarse N (SimplexCategory.mk 0) (SimplexCategory.mk 0) F).obj 0).obj.obj.obj 0 =
      (F.obj 0).obj.obj.obj 0 := rfl
example (F : ComposableArrows (FineWeakChains N n) 0) :
    untransposeCof N n (SimplexCategory.mk 0) (transposeCof N n (SimplexCategory.mk 0) F) = F :=
  untranspose_transposeCof N n (SimplexCategory.mk 0) F
example (F : ComposableArrows (FineWeakCoarseChains N (SimplexCategory.mk 0)) k.len) :
    untransposeCoarse N (SimplexCategory.mk 0) k (transposeCoarse N (SimplexCategory.mk 0) k F) = F :=
  untranspose_transposeCoarse N (SimplexCategory.mk 0) k F
example {l : SimplexCategory} (α : k ⟶ l) (F : FineChain V l) :
    ((fineReindex V α).obj F).obj = (SimplexCategory.toCat.map α).toFunctor ⋙ F.obj := rfl
example {l : SimplexCategory} (α : k ⟶ l) {X Y : HorizontalChains N l} (f : X ⟶ Y)
    (i : Fin (k.len+1)) :
    ((horizontalReindex N α).map f).hom.hom.app i = f.hom.hom.app (α.toOrderHom i) := rfl
end Quillen.Waldhausen.Fibration.MixedNerves

namespace Quillen.Waldhausen.Fibration.MixedNerves
open RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
  (n k : SimplexCategory)
-- All natural transformations are retained in the actual underlying full category.
example {F G : FineChain V k} (f : F.obj ⟶ G.obj) : F ⟶ G := (fineChains V k).homMk f
example (F : ComposableArrows (HorizontalCofChains N k) n.len)
    (i : Fin (n.len+1)) (j : Fin (k.len+1)) :
    ((untransposeCof N n k F).obj j).obj.obj.obj i = (F.obj i).obj.obj.obj j := rfl
example (F : ComposableArrows (HorizontalCofChains N k) n.len)
    {i l : Fin (n.len+1)} (f : i ⟶ l) (j : Fin (k.len+1)) :
    ((untransposeCof N n k F).obj j).obj.obj.map f = (F.map f).hom.hom.app j := rfl
example (F : ComposableArrows (HorizontalCofChains N k) n.len)
    {j l : Fin (k.len+1)} (f : j ⟶ l) (i : Fin (n.len+1)) :
    ((untransposeCof N n k F).map f).hom.hom.app i = (F.obj i).obj.obj.map f := rfl
example {a b : SimplexCategoryᵒᵖ} (α : a ⟶ b) :
    (coarseChainNerve N).flip.map α ≫ (coarseTransposeIso N).hom.app b =
      (coarseTransposeIso N).hom.app a ≫ (horizontalNerve N).map α :=
  (coarseTransposeIso N).hom.naturality α
example {a b : SimplexCategoryᵒᵖ} (α : a ⟶ b) :
    ((cofChainNerve N).flip.obj (op k)).map α ≫ ((cofTransposeIso N).hom.app (op k)).app b =
      ((cofTransposeIso N).hom.app (op k)).app a ≫ ((horizontalCofNerve N).obj (op k)).map α :=
  ((cofTransposeIso N).hom.app (op k)).naturality α
example (F : ComposableArrows (HorizontalCofChains N (SimplexCategory.mk 0)) 0) :
    ((untransposeCof N (SimplexCategory.mk 0) (SimplexCategory.mk 0) F).obj 0).obj.obj.obj 0 =
      (F.obj 0).obj.obj.obj 0 := rfl
example (F : ComposableArrows (FineWeakChains N n) n.len) :
    (TheoremA.diagonalMap (chainInclusion N)).app (op n) F =
      F ⋙ weakForgetCofChain N n := rfl
end Quillen.Waldhausen.Fibration.MixedNerves

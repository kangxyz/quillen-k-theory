import Quillen.Waldhausen.Fibration.RelativeRows.CoarseEvaluation
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.FiberFiltration,
    `Quillen.Waldhausen.Fibration.RelativeRows.CoarseEvaluation]
  let mut counts : Array Nat := #[0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (· + 1)
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless counts == #[4,20] do throwError "Expected24 origins, found {counts}"
  logInfo m!"ORIGINS {counts}"
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.RelativeRows
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Categorical
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example (n : SimplexCategory) : fiber N n ⋙ initialFiltrationFunctor N n =
    Functor.const (Fin (n.len+1)) := fiber_initialFiltrationFunctor N n
example (n : SimplexCategory) (X : C) {i j : Fin (n.len+1)} (f : i ⟶ j) :
    ((initialFiltrationFunctor N n).obj ((fiber N n).obj X)).map f = 𝟙 X := rfl
example (n : SimplexCategory) {X Y : C} (f : X ⟶ Y) (i : Fin (n.len+1)) :
    ((initialFiltrationFunctor N n).map ((fiber N n).map f)).app i = f := rfl
example (X : C) : ((initialFiltrationFunctor N ⦋0⦌).obj ((fiber N ⦋0⦌).obj X)).obj 0 = X := rfl
end Categorical
section OriginalModels
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse)
example : coarseEvaluation N he = relativeFiltrationTotalMap N he ≫ MixedNerves.totalCofEvaluation N := rfl
example (n : SimplexCategory) (F : (TheoremA.diagonalSSet (relativeSRows N)).obj (op n))
    (i : Fin (n.len+1)) (p : Interval n) :
    (((coarseEvaluation N he).app (op n) F).val.obj (i,p)) =
      (F.val.obj (i,p)).obj.obj.obj (interval 0 i.succ (Fin.zero_le _)) := rfl
example : totalFiberInclusion N ≫ coarseEvaluation N he = sSetMap (changeWeak_exact N) :=
  totalFiberInclusion_coarseEvaluation N he
example (n : SimplexCategoryᵒᵖ) (F : (sSet V.cof V.weq).obj n) :
    (coarseEvaluation N he).app n ((totalFiberInclusion N).app n F) =
      (sSetMap (changeWeak_exact N)).app n F := by
  exact congrArg (fun f ↦ f.app n F) (totalFiberInclusion_coarseEvaluation N he)
example : (SSet.toTop.map (coarseEvaluation N he)).hom.comp
    (SSet.toTop.map (totalFiberInclusion N)).hom = changeWeakMap N :=
  totalFiberInclusion_coarseEvaluation_realized N he
example (n : SimplexCategory) :
    (coarseEvaluation N he).app (op n)
      (zeroSimplex (waldhausenStructure N n).cof (waldhausenStructure N n).weq
        (zero N n) (isZero N n) (op n)) =
      zeroSimplex N.coarse.cof N.coarse.weq N.coarse.zero N.coarse.isZero (op n) :=
  coarseEvaluation_zeroSimplex N he n
example (n : SimplexCategory) :
    (totalFiberInclusion N).app (op n) (zeroSimplex V.cof V.weq V.zero V.isZero (op n)) =
      zeroSimplex (waldhausenStructure N n).cof (waldhausenStructure N n).weq
        (zero N n) (isZero N n) (op n) := totalFiberInclusion_zeroSimplex N n
example : SSet.toTop.map (coarseEvaluation N he) (totalBasepoint N) = N.coarse.kBasepoint :=
  coarseEvaluation_basepoint N he
example : SSet.toTop.map (totalFiberInclusion N) V.kBasepoint = totalBasepoint N :=
  totalFiberInclusion_basepoint N
example : (coarseEvaluation N he).app (op ⦋0⦌) (totalZeroVertex N) =
    zeroSimplex N.coarse.cof N.coarse.weq N.coarse.zero N.coarse.isZero (op ⦋0⦌) :=
  coarseEvaluation_zeroSimplex N he ⦋0⦌
variable (D : RowFactorization.JointData N) (hs : RowFactorization.SecondEndpointSection N D)
  [N.coarse.weq.HasTwoOutOfThreeProperty]
example : ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (relativeSRows N)|
    |sSet N.coarse.cof N.coarse.weq| := coarseEvaluationHomotopyEquiv N he D hs
example : (coarseEvaluationHomotopyEquiv N he D hs).toFun =
    (SSet.toTop.map (coarseEvaluation N he)).hom := coarseEvaluationHomotopyEquiv_toFun N he D hs
example : (coarseEvaluationHomotopyEquiv N he D hs).toFun (totalBasepoint N) = N.coarse.kBasepoint := by
  rw [coarseEvaluationHomotopyEquiv_toFun]
  exact coarseEvaluation_basepoint N he
example : (coarseEvaluationHomotopyEquiv N he D hs).invFun.comp
    (SSet.toTop.map (coarseEvaluation N he)).hom |>.Homotopic (.id _) := by
  rw [← coarseEvaluationHomotopyEquiv_toFun]
  exact (coarseEvaluationHomotopyEquiv N he D hs).left_inv
end OriginalModels

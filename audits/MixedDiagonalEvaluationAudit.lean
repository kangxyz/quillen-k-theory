import Quillen.Waldhausen.Fibration.MixedNerves.DiagonalEvaluation
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.MixedNerves.DiagonalEvaluation]
  let mut counts : Array Nat := #[0]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    count := count + 1
    counts := counts.modify i (· + 1)
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing defining module {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless counts == #[33] do throwError "Expected33 origins, got {counts}"
  logInfo m!"Audited {count} original diagonal-evaluation origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.MixedNerves
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Categorical
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
  (k : SimplexCategory)
example (F : HorizontalChains N k) (i : Fin (k.len+1)) :
    (((horizontalCoarseDiagram N k).obj F).obj i).obj = F.obj.obj.obj i := rfl
example (F : HorizontalChains N k) {i j : Fin (k.len+1)} (f : i ⟶ j) :
    (((horizontalCoarseDiagram N k).obj F).map f).hom = F.obj.obj.map f := rfl
example {F G : HorizontalChains N k} (f : F ⟶ G) (i : Fin (k.len+1)) :
    (((horizontalCoarseDiagram N k).map f).app i).hom = f.hom.hom.app i := rfl
example (F : ComposableArrows (HorizontalChains N k) k.len) (i : Fin (k.len+1)) :
    ((diagonalCoarseChain N k F).obj i).obj = (F.obj i).obj.obj.obj i := rfl
example (F : ComposableArrows (HorizontalChains N k) k.len) {i j : Fin (k.len+1)} (f : i ⟶ j) :
    ((diagonalCoarseChain N k F).map f).hom =
      (F.map f).hom.hom.app i ≫ (F.obj j).obj.obj.map f := rfl
example (F : ComposableArrows (HorizontalChains N k) k.len) {i j : Fin (k.len+1)} (f : i ⟶ j) :
    N.coarse.weq ((F.map f).hom.hom.app i ≫ (F.obj j).obj.obj.map f) :=
  diagonalCoarseChain_map_weak N k F f
example (F : ComposableArrows (HorizontalChains N ⦋0⦌) 0) :
    ((diagonalCoarseChain N ⦋0⦌ F).obj 0).obj = (F.obj 0).obj.obj.obj 0 := rfl
end Categorical
section Realization
variable {C : Type (max u v)} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example (k : SimplexCategory) (F : ComposableArrows (HorizontalChains N k) k.len) :
    (diagonalEvaluation N).app (op k) F = diagonalCoarseChain N k F := rfl
example {k l : SimplexCategoryᵒᵖ} (α : k ⟶ l) :
    (TheoremA.diagonalSSet (horizontalNerve N)).map α ≫ (diagonalEvaluation N).app l =
      (diagonalEvaluation N).app k ≫ (nerve (TrivialCofibrations.WeakCategory N.coarse.weq)).map α :=
  (diagonalEvaluation N).naturality α
example : constantHorizontalDiagonalMap N ≫ diagonalEvaluation N = 𝟙 _ := constantDiagonal_evaluation N
example : (SSet.toTop.map (diagonalEvaluation N)).hom.comp
    (SSet.toTop.map (constantHorizontalDiagonalMap N)).hom = ContinuousMap.id _ :=
  diagonalEvaluation_constant N
example : ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (horizontalNerve N)|
    (ClassifyingSpace (TrivialCofibrations.WeakCategory N.coarse.weq)) := diagonalEvaluationHomotopyEquiv N
example : (diagonalEvaluationHomotopyEquiv N).toFun =
    (SSet.toTop.map (diagonalEvaluation N)).hom := rfl
example : (diagonalEvaluationHomotopyEquiv N).invFun =
    (SSet.toTop.map (constantHorizontalDiagonalMap N)).hom := diagonalEvaluationHomotopyEquiv_invFun N
example : ((diagonalEvaluationHomotopyEquiv N).invFun.comp
    (diagonalEvaluationHomotopyEquiv N).toFun).Homotopic (ContinuousMap.id _) :=
  (diagonalEvaluationHomotopyEquiv N).left_inv
example : ((diagonalEvaluationHomotopyEquiv N).toFun.comp
    (diagonalEvaluationHomotopyEquiv N).invFun).Homotopic (ContinuousMap.id _) :=
  (diagonalEvaluationHomotopyEquiv N).right_inv
example : (constantHorizontalDiagonalMap N ≫ diagonalEvaluation N).app (op ⦋0⦌)
    ((Functor.const (Fin 1)).obj (⟨V.zero⟩ : TrivialCofibrations.WeakCategory N.coarse.weq)) =
      (Functor.const (Fin 1)).obj (⟨V.zero⟩ : TrivialCofibrations.WeakCategory N.coarse.weq) := by
  rw [constantDiagonal_evaluation]
  rfl
end Realization
section Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
example (X : Scheme.{u}) (k : SimplexCategory) :
    HorizontalChains (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) k ⥤
      ComposableArrows (TrivialCofibrations.WeakCategory
        (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.weq) k.len :=
  horizontalCoarseDiagram (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) k
def actualSchemeDiagonalEvaluation (X : Scheme.{u}) :
    ContinuousMap.HomotopyEquiv
      |TheoremA.diagonalSSet (horizontalNerve (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)))|
      (ClassifyingSpace (TrivialCofibrations.WeakCategory
        (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.weq)) :=
  diagonalEvaluationHomotopyEquiv.{u+1, u} (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))
#print axioms actualSchemeDiagonalEvaluation
end Scheme

import Quillen.Waldhausen.Fibration.MixedNerves.ChainEvaluation
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.MixedNerves.ChainEvaluation]
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
  unless counts == #[20] do throwError "Expected20 origins, got {counts}"
  logInfo m!"Audited {count} original chain-evaluation origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.MixedNerves
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Generic
variable {C : Type (max u v)} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example : coarseChainEvaluation N = (coarseDiagonalIso N).hom ≫ diagonalEvaluation N := rfl
example (k : SimplexCategory) (F : ComposableArrows (FineWeakCoarseChains N k) k.len)
    (i : Fin (k.len+1)) : (((coarseChainEvaluation N).app (op k) F).obj i).obj =
      (F.obj i).obj.obj.obj i := rfl
example (k : SimplexCategory) (F : ComposableArrows (FineWeakCoarseChains N k) k.len)
    {i j : Fin (k.len+1)} (f : i ⟶ j) : (((coarseChainEvaluation N).app (op k) F).map f).hom =
      (F.obj i).obj.obj.map f ≫ (F.map f).hom.hom.app j := rfl
example (k : SimplexCategory) (F : ComposableArrows (FineWeakCoarseChains N k) k.len)
    {i j : Fin (k.len+1)} (f : i ⟶ j) :
    N.coarse.weq ((F.obj i).obj.obj.map f ≫ (F.map f).hom.hom.app j) :=
  (((coarseChainEvaluation N).app (op k) F).map f).property
example : (coarseChainEvaluationHomotopyEquiv N).toFun =
    (SSet.toTop.map (coarseChainEvaluation N)).hom := coarseChainEvaluationHomotopyEquiv_toFun N
example : (coarseChainEvaluationHomotopyEquiv N).invFun =
    (SSet.toTop.map (coarseChainSection N)).hom := coarseChainEvaluationHomotopyEquiv_invFun N
example : coarseChainSection N ≫ coarseChainEvaluation N = 𝟙 _ := coarseChainSection_evaluation N
example : cofChainEvaluation N = TheoremA.diagonalMap (chainInclusion N) ≫ coarseChainEvaluation N := rfl
example (k : SimplexCategory) (F : ComposableArrows (RelativeRows.FineWeakChains N k) k.len)
    (i : Fin (k.len+1)) : (((cofChainEvaluation N).app (op k) F).obj i).obj =
      (F.obj i).obj.obj.obj i := rfl
example (F : ComposableArrows (FineWeakCoarseChains N ⦋0⦌) 0) :
    (((coarseChainEvaluation N).app (op ⦋0⦌) F).obj 0).obj = (F.obj 0).obj.obj.obj 0 := rfl
example : (coarseChainSection N ≫ coarseChainEvaluation N).app (op ⦋0⦌)
    ((Functor.const (Fin 1)).obj (⟨V.zero⟩ : TrivialCofibrations.WeakCategory N.coarse.weq)) =
      (Functor.const (Fin 1)).obj (⟨V.zero⟩ : TrivialCofibrations.WeakCategory N.coarse.weq) := by
  rw [coarseChainSection_evaluation]
  rfl
end Generic
section Natural
variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {N : NestedWeakEquivalences V} {M : NestedWeakEquivalences W}
  (F : CompatibleFunctor N M)
example (X : TrivialCofibrations.WeakCategory N.coarse.weq) :
    ((coarseWeakPostcompose F).obj X).obj = F.toFunctor.obj X.obj := rfl
example {X Y : TrivialCofibrations.WeakCategory N.coarse.weq} (f : X ⟶ Y) :
    ((coarseWeakPostcompose F).map f).hom = F.toFunctor.map f.hom := rfl
example : TheoremA.diagonalMap (horizontalNerveMap F) ≫ diagonalEvaluation M =
    diagonalEvaluation N ≫ nerveMap (coarseWeakPostcompose F) := diagonalEvaluation_naturality F
example : TheoremA.diagonalMap (coarseNerveMap F) ≫ coarseChainEvaluation M =
    coarseChainEvaluation N ≫ nerveMap (coarseWeakPostcompose F) := coarseChainEvaluation_naturality F
example : TheoremA.diagonalMap (cofNerveMap F) ≫ cofChainEvaluation M =
    cofChainEvaluation N ≫ nerveMap (coarseWeakPostcompose F) := cofChainEvaluation_naturality F
end Natural
section Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
def actualSchemeCoarseChainEvaluation (X : Scheme.{u}) :
    ContinuousMap.HomotopyEquiv
      |TheoremA.diagonalSSet (coarseChainNerve (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)))|
      (ClassifyingSpace (TrivialCofibrations.WeakCategory
        (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.weq)) :=
  coarseChainEvaluationHomotopyEquiv.{u+1,u} (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))
#print axioms actualSchemeCoarseChainEvaluation
end Scheme

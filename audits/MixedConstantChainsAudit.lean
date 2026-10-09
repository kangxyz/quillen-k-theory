import Quillen.Waldhausen.Fibration.MixedNerves.ConstantDiagonal
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.MixedNerves.ConstantChains,
    `Quillen.Waldhausen.Fibration.MixedNerves.ConstantDiagonal]
  let mut counts : Array Nat := #[0,0]
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
  unless counts == #[33,8] do throwError "Expected41 original origins (33+8), got {counts}"
  logInfo m!"Audited {count} original constant-chain origins."

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
example (k : SimplexCategory) (X : TrivialCofibrations.WeakCategory N.coarse.weq) (i : Fin (k.len+1)) :
    ((constantHorizontal N k).obj X).obj.obj.obj i = X.obj := rfl
example (k : SimplexCategory) {X Y : TrivialCofibrations.WeakCategory N.coarse.weq}
    (f : X ⟶ Y) (i : Fin (k.len+1)) : ((constantHorizontal N k).map f).hom.hom.app i = f.hom := rfl
example (k : SimplexCategory) {F G : HorizontalChains N k} (f : F ⟶ G) :
    ((evaluateHorizontalZero N k).map f).hom = f.hom.hom.app 0 := rfl
example (k : SimplexCategory) : constantHorizontal N k ⋙ evaluateHorizontalZero N k = 𝟭 _ :=
  constantHorizontal_evaluateZero N k
example (k : SimplexCategory) (F : HorizontalChains N k) (i : Fin (k.len+1)) :
    ((constantInitial N k).app F).hom.hom.app i = F.obj.obj.map (homOfLE (Fin.zero_le i)) := rfl
example (k : SimplexCategory) (F : HorizontalChains N k) (i : Fin (k.len+1)) :
    N.coarse.weq (((constantInitial N k).app F).hom.hom.app i) :=
  ((constantInitial N k).app F).property i
example {k l : SimplexCategory} (α : k ⟶ l) :
    constantHorizontal N l ⋙ horizontalReindex N α = constantHorizontal N k := constantHorizontal_reindex N α
example (k : SimplexCategory) (i : Fin (k.len+1)) :
    ((constantHorizontal N k).obj ⟨V.zero⟩).obj.obj.obj i = V.zero := rfl
example (F : HorizontalChains N ⦋0⦌) :
    ((constantInitial N ⦋0⦌).app F).hom.hom.app 0 = 𝟙 (F.obj.obj.obj 0) := by
  change F.obj.obj.map (𝟙 (0 : Fin (1 : ℕ))) = _
  exact F.obj.obj.map_id _
end Categorical
section Realization
variable {C : Type (max u v)} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example : (Functor.const SimplexCategoryᵒᵖ).obj (nerve (TrivialCofibrations.WeakCategory N.coarse.weq)) ⟶
    horizontalNerve N := constantHorizontalNerve N
example (k : SimplexCategory) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (TrivialCofibrations.WeakCategory N.coarse.weq))
      (ClassifyingSpace (HorizontalChains N k)) := constantHorizontalClassifyingHomotopyEquiv N k
example (k : SimplexCategory) : (constantHorizontalClassifyingHomotopyEquiv N k).toFun =
    (classifyingSpaceMap (constantHorizontal N k)).hom := rfl
example (k : SimplexCategory) : (constantHorizontalClassifyingHomotopyEquiv N k).invFun =
    (classifyingSpaceMap (evaluateHorizontalZero N k)).hom := rfl
example : constantHorizontalDiagonalMap N = (TheoremA.diagonalConstantIso _).inv ≫
    TheoremA.diagonalMap (constantHorizontalNerve N) := rfl
example : ContinuousMap.HomotopyEquiv (ClassifyingSpace (TrivialCofibrations.WeakCategory N.coarse.weq))
    |TheoremA.diagonalSSet (horizontalNerve N)| := constantHorizontalDiagonalHomotopyEquiv N
example : (constantHorizontalDiagonalHomotopyEquiv N).toFun =
    (SSet.toTop.map (constantHorizontalDiagonalMap N)).hom := constantHorizontalDiagonalHomotopyEquiv_toFun N
end Realization
section Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
example (X : Scheme.{u}) (k : SimplexCategory) :
    TrivialCofibrations.WeakCategory (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.weq ⥤
      HorizontalChains (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) k :=
  constantHorizontal (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) k
end Scheme

import Quillen.Waldhausen.QuillenComparison.RowFull
import Quillen.Waldhausen.QuillenComparison.FlagPresentation
import Quillen.Waldhausen.QuillenComparison.MixedNerve
import Quillen.Waldhausen.QuillenComparison.ChainClassification
import Quillen.Waldhausen.QuillenComparison.BisimplicialMap
import Quillen.Waldhausen.QuillenComparison.RowDiagonal
import Quillen.Waldhausen.QuillenComparison.ComparisonHom
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Waldhausen.QuillenComparison.ExactRectangles,
    `Quillen.Waldhausen.QuillenComparison.IntervalSpans,
    `Quillen.Waldhausen.QuillenComparison.SpanNaturality,
    `Quillen.Waldhausen.QuillenComparison.VerticalSpans,
    `Quillen.Waldhausen.QuillenComparison.Reindexing,
    `Quillen.Waldhausen.QuillenComparison.RowGroupoid,
    `Quillen.Waldhausen.QuillenComparison.InitialFlag,
    `Quillen.Waldhausen.QuillenComparison.EdgewiseIndices,
    `Quillen.Waldhausen.QuillenComparison.RowSimplicial,
    `Quillen.Waldhausen.QuillenComparison.RowFaithful,
    `Quillen.Waldhausen.QuillenComparison.InitialFlagIso,
    `Quillen.Waldhausen.QuillenComparison.SpanLifting,
    `Quillen.Waldhausen.QuillenComparison.RecoverSubobjects,
    `Quillen.Waldhausen.QuillenComparison.SparseRows,
    `Quillen.Waldhausen.QuillenComparison.RowFull,
    `Quillen.Waldhausen.QuillenComparison.QuotientCalculus,
    `Quillen.Waldhausen.QuillenComparison.AdmissibleFlags,
    `Quillen.Waldhausen.QuillenComparison.FlagMaps,
    `Quillen.Waldhausen.QuillenComparison.FlagPresentation,
    `Quillen.Waldhausen.QuillenComparison.MixedNerve,
    `Quillen.Waldhausen.QuillenComparison.ChainClassification,
    `Quillen.Waldhausen.QuillenComparison.SimplicialMap,
    `Quillen.Waldhausen.QuillenComparison.BisimplicialMap,
    `Quillen.Waldhausen.QuillenComparison.RowDiagonal,
    `Quillen.Waldhausen.QuillenComparison.Basepoint,
    `Quillen.Waldhausen.QuillenComparison.ComparisonHom]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless modules.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count = 465 do throwError "Expected frozen 465-declaration scope; audited {count}"
  logInfo m!"Audited all {count} declarations from the frozen stable Q/S row and map modules."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v w
namespace Quillen.Waldhausen.QuillenComparison
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)
example (n : SimplexCategory) : (rowChainComparison E n).Faithful := inferInstance
example (n : SimplexCategory) : (rowChainComparison E n).Full := inferInstance
example : sSet E.inflation (MorphismProperty.isomorphisms C) ≅
    TheoremA.diagonalSSet (rowNerve E) := rowDiagonalIso E
example : Edgewise.ε.op ⋙ rowNerve E ⟶ chainCoreNerve (Q E.deflation E.inflation) :=
  rowChainNerveMap E
example (n : SimplexCategoryᵒᵖ) : (rowChainNerveMap E).app n =
    MixedNerve.map.{u, v, max u v} (rowChainComparison E n.unop) := rfl
example {n : SimplexCategory} (A : Fin (n.len + 1) ⥤ C)
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f)) : Row E n := flagRow E A hA
example {n : SimplexCategory} (F : Row E n) :
    flagRow E (initialFlag E F) (initialFlag_inflation E F) ⟶ F := completedInitialIso E F
example (D : Type u) [Category.{v} D] :
    Classification.sSet D ≅ TheoremA.diagonalSSet (chainCoreNerve D) := chainCoreDiagonalIso D
example {C D : Type (max u v w)} [Category.{v} C] [Category.{w} D] (e : C ≌ D) :
    ContinuousMap.HomotopyEquiv |nerve C| |nerve D| := MixedNerve.realizationEquivalence.{u, v, w} e
example {C D : Type (max u v w)} [Category.{v} C] [Category.{w} D] (e : C ≌ D) :
    (MixedNerve.realizationEquivalence.{u, v, w} e).toFun =
      (SSet.toTop.map (MixedNerve.map.{u, v, w} e.functor)).hom := rfl
example (n : ℕ) : (ofExactCategory E).K n →* E.K n := comparisonK E n
example (n : ℕ) : (subdivisionKEquiv E n).toMonoidHom = subdivisionEndpointK E n := rfl
example (n : ℕ) : (comparisonK E n).comp (subdivisionEndpointK E n) =
    subdivisionComparisonK E n := comparisonK_comp_endpoint E n
example : realizationComparison E (subdivisionBasepoint E) = E.kBasepoint :=
  realizationComparison_basepoint E
example : realizationEndpoint E (subdivisionBasepoint E) = (ofExactCategory E).kBasepoint :=
  realizationEndpoint_basepoint E
end Quillen.Waldhausen.QuillenComparison

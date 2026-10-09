import Quillen.Waldhausen.QuillenComparison.Equivalence
import Quillen.Waldhausen.QuillenComparison.Functoriality
import Lean.Util.CollectAxioms

/-! Recursive standard-axiom audit of every declaration whose defining module
is one of the frozen Q/S proof modules, including generated declarations. -/

open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.CategoryTheory.ExactCategory.SpecialFractions,
    `Quillen.Waldhausen.QuillenComparison.AdmissibleFlags,
    `Quillen.Waldhausen.QuillenComparison.Basepoint,
    `Quillen.Waldhausen.QuillenComparison.BisimplicialMap,
    `Quillen.Waldhausen.QuillenComparison.ChainClassification,
    `Quillen.Waldhausen.QuillenComparison.ComparisonHom,
    `Quillen.Waldhausen.QuillenComparison.EdgewiseIndices,
    `Quillen.Waldhausen.QuillenComparison.Equivalence,
    `Quillen.Waldhausen.QuillenComparison.ExactRectangles,
    `Quillen.Waldhausen.QuillenComparison.ExtendedRows,
    `Quillen.Waldhausen.QuillenComparison.ExtendedSpan,
    `Quillen.Waldhausen.QuillenComparison.Factorization,
    `Quillen.Waldhausen.QuillenComparison.FlagExtension,
    `Quillen.Waldhausen.QuillenComparison.FlagMaps,
    `Quillen.Waldhausen.QuillenComparison.FlagPresentation,
    `Quillen.Waldhausen.QuillenComparison.FlagPullback,
    `Quillen.Waldhausen.QuillenComparison.FlagReindexing,
    `Quillen.Waldhausen.QuillenComparison.Functoriality,
    `Quillen.Waldhausen.QuillenComparison.InitialFlag,
    `Quillen.Waldhausen.QuillenComparison.InitialFlagIso,
    `Quillen.Waldhausen.QuillenComparison.IntervalSpans,
    `Quillen.Waldhausen.QuillenComparison.IntervalTransport,
    `Quillen.Waldhausen.QuillenComparison.MixedNerve,
    `Quillen.Waldhausen.QuillenComparison.PullbackQuotients,
    `Quillen.Waldhausen.QuillenComparison.QuotientCalculus,
    `Quillen.Waldhausen.QuillenComparison.ReconstructedRows,
    `Quillen.Waldhausen.QuillenComparison.ReconstructedSpan,
    `Quillen.Waldhausen.QuillenComparison.ReconstructionIndices,
    `Quillen.Waldhausen.QuillenComparison.RecoverSubobjects,
    `Quillen.Waldhausen.QuillenComparison.Reindexing,
    `Quillen.Waldhausen.QuillenComparison.RowBase,
    `Quillen.Waldhausen.QuillenComparison.RowDiagonal,
    `Quillen.Waldhausen.QuillenComparison.RowEssentialSurjective,
    `Quillen.Waldhausen.QuillenComparison.RowFaithful,
    `Quillen.Waldhausen.QuillenComparison.RowFull,
    `Quillen.Waldhausen.QuillenComparison.RowGroupoid,
    `Quillen.Waldhausen.QuillenComparison.RowSimplicial,
    `Quillen.Waldhausen.QuillenComparison.SimplicialMap,
    `Quillen.Waldhausen.QuillenComparison.SpanLifting,
    `Quillen.Waldhausen.QuillenComparison.SpanNaturality,
    `Quillen.Waldhausen.QuillenComparison.SparseRows,
    `Quillen.Waldhausen.QuillenComparison.VerticalSpans]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless modules.contains origin do continue
    count := count + 1
    unless seen.contains origin do seen := seen.push origin
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for origin in modules do
    unless seen.contains origin do throwError "Empty defining-module audit: {origin}"
  logInfo m!"Audited {count} declarations from {modules.size} Q/S proof modules."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
namespace Quillen.Waldhausen.QuillenComparison
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)
example (n : SimplexCategory) : (rowChainComparison E n).Full := inferInstance
example (n : SimplexCategory) : (rowChainComparison E n).Faithful := inferInstance
example (n : SimplexCategory) : (rowChainComparison E n).EssSurj := inferInstance
example (n : SimplexCategory) : (rowChainComparison E n).IsEquivalence := inferInstance
example : ContinuousMap.HomotopyEquiv (SubdivisionSpace E) E.KSpace :=
  realizationComparisonHomotopyEquiv E
example : (realizationComparisonHomotopyEquiv E).toFun = (realizationComparison E).hom := rfl
example : realizationComparisonHomotopyEquiv E (subdivisionBasepoint E) = E.kBasepoint :=
  realizationComparisonHomotopyEquiv_basepoint E
example : realizationEndpoint E (subdivisionBasepoint E) = (ofExactCategory E).kBasepoint :=
  realizationEndpoint_basepoint E
example (n : ℕ) : (ofExactCategory E).K n ≃* E.K n := comparisonKEquiv E n
example (n : ℕ) : (comparisonKEquiv E n).toMonoidHom = comparisonK E n := rfl
example (n : ℕ) : (comparisonKEquiv E n).toMonoidHom.comp (subdivisionEndpointK E n) =
    subdivisionComparisonK E n := comparisonK_comp_endpoint E n
end Quillen.Waldhausen.QuillenComparison

import Quillen.Waldhausen.QuillenComparison.Equivalence
import Quillen.Scheme.Comparison.SmallVectorBundleK
import Quillen.PerfectComplexes.KTheory
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.QuillenComparison.RowEssentialSurjective,
    `Quillen.Waldhausen.QuillenComparison.Equivalence]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count = 31 do throwError "Expected frozen 31-declaration scope; audited {count}"
  logInfo m!"Audited all {count} final Q/S endpoint declaration origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v
namespace Quillen.Waldhausen.QuillenComparison
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)
example (n : SimplexCategory) : (rowChainComparison E n).IsEquivalence := inferInstance
example (n : SimplexCategory) : (rowChainEquivalence E n).functor = rowChainComparison E n := rfl
example (n : ℕ) (G : ComposableArrows (Q E.deflation E.inflation) n) :
    ∃ F : Row E (Edgewise.ε.obj ⦋n⦌),
      Nonempty (((rowChainComparison E ⦋n⦌).obj F).of ≅ G) := exists_row_of_chain E n G
example : ContinuousMap.HomotopyEquiv (SubdivisionSpace E) E.KSpace :=
  realizationComparisonHomotopyEquiv E
example : (realizationComparisonHomotopyEquiv E).toFun = (realizationComparison E).hom := rfl
example : realizationComparisonHomotopyEquiv E (subdivisionBasepoint E) = E.kBasepoint :=
  realizationComparisonHomotopyEquiv_basepoint E
example : ContinuousMap.HomotopyEquiv (ofExactCategory E).Delooping E.KSpace :=
  deloopingHomotopyEquiv E
example (n : ℕ) : (ofExactCategory E).K n ≃* E.K n := comparisonKEquiv E n
example (n : ℕ) : (comparisonKEquiv E n).toMonoidHom = comparisonK E n := rfl
example (n : ℕ) : (subdivisionComparisonKEquiv E n).toMonoidHom = subdivisionComparisonK E n := rfl
example (n : ℕ) : (comparisonKEquiv E n).toMonoidHom.comp (subdivisionEndpointK E n) =
    subdivisionComparisonK E n := comparisonK_comp_endpoint E n
end Quillen.Waldhausen.QuillenComparison

namespace Quillen
attribute [local instance] Abelian.hasFiniteBiproducts
example (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) : Scheme.K X n ≃*
    (Waldhausen.ofExactCategory (SchemeSheaf.vectorBundleExactStructure X)).K n :=
  (SchemeSheaf.smallVectorBundleKEquiv X n).trans
    (Waldhausen.QuillenComparison.comparisonKEquiv (SchemeSheaf.vectorBundleExactStructure X) n).symm
example (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) : Scheme.K X n →* PerfectComplexes.PerfectK X n :=
  (PerfectComplexes.vectorBundleToPerfectSMap X n).comp
    (((SchemeSheaf.smallVectorBundleKEquiv X n).trans
      (Waldhausen.QuillenComparison.comparisonKEquiv (SchemeSheaf.vectorBundleExactStructure X) n).symm).toMonoidHom)
end Quillen

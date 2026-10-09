import Lean.Util.CollectAxioms
import Quillen.Waldhausen.QuillenComparison.Equivalence
import Quillen.Waldhausen.QuillenComparison.Functoriality

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut modules : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless (`Quillen.Waldhausen.QuillenComparison).isPrefixOf origin ||
      origin == `Quillen.CategoryTheory.ExactCategory.SpecialFractions ||
      origin == `Quillen.CategoryTheory.QConstruction.Core do continue
    modules := modules.insert origin
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  logInfo m!"Audited all {count} exact Q/S declaration origins across {modules.size} implementation modules."

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)
open Waldhausen Waldhausen.QuillenComparison

example (n : SimplexCategory) : (rowChainComparison E n).Full := inferInstance
example (n : SimplexCategory) : (rowChainComparison E n).Faithful := inferInstance
example (n : SimplexCategory) : (rowChainComparison E n).EssSurj := inferInstance
example (n : ℕ) (G : ComposableArrows E.QCategory n) :
    ∃ F : Row E (Edgewise.ε.obj (SimplexCategory.mk n)),
      Nonempty (((rowChainComparison E (SimplexCategory.mk n)).obj F).of ≅ G) :=
  exists_row_of_chain E n G

example : ContinuousMap.HomotopyEquiv (SubdivisionSpace E) E.KSpace :=
  realizationComparisonHomotopyEquiv E
example : (realizationComparisonHomotopyEquiv E).toFun =
    (realizationComparison E).hom := rfl
example : realizationComparisonHomotopyEquiv E (subdivisionBasepoint E) =
    E.kBasepoint := realizationComparisonHomotopyEquiv_basepoint E
example (n : ℕ) : (ofExactCategory E).K n ≃* E.K n := comparisonKEquiv E n
example (n : ℕ) : (comparisonKEquiv E n).toMonoidHom = comparisonK E n := rfl
example (n : ℕ) : Function.Bijective (comparisonK E n) :=
  (comparisonKEquiv E n).bijective
example (n : ℕ) :
    (comparisonKEquiv E n).toMonoidHom.comp (subdivisionEndpointK E n) =
      subdivisionComparisonK E n := comparisonK_comp_endpoint E n

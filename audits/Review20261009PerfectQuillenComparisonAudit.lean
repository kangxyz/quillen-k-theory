import Quillen.PerfectComplexes.QuillenComparison
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.PerfectComplexes.QuillenComparison
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count = 33 do throwError "Expected frozen 33-declaration scope; audited {count}"
  logInfo m!"Audited all {count} perfect Q/S comparison declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace Quillen.PerfectComplexes
example (X : Scheme.{u}) (n : ℕ) : Quillen.Scheme.K X n ≃*
    (Waldhausen.ofExactCategory (SchemeSheaf.vectorBundleExactStructure X)).K n := vectorBundleQSEquiv X n
example (X : Scheme.{u}) (n : ℕ) :
    (vectorBundleQSEquiv X n).toMonoidHom =
      (Waldhausen.QuillenComparison.comparisonKEquiv
        (SchemeSheaf.vectorBundleExactStructure X) n).symm.toMonoidHom.comp
          (SchemeSheaf.smallVectorBundleKMap X n) := rfl
example (X : Scheme.{u}) (n : ℕ) : Quillen.Scheme.K X n →* StrictK X n := vectorBundleToStrictKMap X n
example (X : Scheme.{u}) (n : ℕ) : Quillen.Scheme.K X n →* PerfectK X n := vectorBundleToPerfectKMap X n
example (X : Scheme.{u}) (n : ℕ) :
    vectorBundleToStrictKMap X n =
      (vectorBundleSComparison X n).comp (vectorBundleQSEquiv X n).toMonoidHom := rfl
example (X : Scheme.{u}) (n : ℕ) :
    vectorBundleToPerfectKMap X n =
      (vectorBundleToPerfectSMap X n).comp (vectorBundleQSEquiv X n).toMonoidHom := rfl
example (X : Scheme.{u}) (n : ℕ) :
    (strictToPerfectKMap X n).comp (vectorBundleToStrictKMap X n) = vectorBundleToPerfectKMap X n := rfl
end Quillen.PerfectComplexes

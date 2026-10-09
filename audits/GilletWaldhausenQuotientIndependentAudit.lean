import Quillen.Waldhausen.GilletWaldhausen.QuotientExact
import Quillen.Scheme.VectorBundle.KernelClosure
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless (`Quillen.Waldhausen.GilletWaldhausen).isPrefixOf origin do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless count == 164 do throwError "Unexpected acyclic algebra origin count: {count}"
  logInfo m!"Audited all {count} exact acyclic cycle/truncation declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Quillen
open Waldhausen.GilletWaldhausen
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

example (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (h₃ : S.X₃.Acyclic) (n : ℤ) :
    (S.map (cyclesFunctor A (ComplexShape.up ℤ) n)).ShortExact := cycles_shortExact S hS h₃ n
example (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (h₃ : S.X₃.Acyclic) (n : ℤ) :
    (S.map ((ComplexShape.embeddingUpIntLE n).truncLEFunctor A)).ShortExact :=
  truncLE_shortExact S hS h₃ n

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]
  [(abelianExactStructure A).IsExtensionClosed P]
example (n : ℤ) : ExactFunctor (boundedAcyclicExactStructure P)
    (boundedAcyclicExactStructure P) := boundedAcyclicTruncLEExactFunctor P n
example (n : ℤ) : (boundedAcyclicTruncLEExactFunctor P n).toFunctor =
    acyclicTruncationSequenceFunctor P n ⋙ ShortComplex.π₁ := rfl

open AlgebraicGeometry SchemeSheaf
example (X : Scheme.{u}) (n : ℤ) :
    ExactFunctor (boundedAcyclicExactStructure (finiteLocallyFree X))
      (boundedAcyclicExactStructure (finiteLocallyFree X)) :=
  boundedAcyclicTruncLEExactFunctor (finiteLocallyFree X) n

example (n : ℤ) : ExactFunctor (boundedAcyclicExactStructure P)
    (boundedAcyclicExactStructure P) := boundedAcyclicQuotientExactFunctor P n
example (n : ℤ) : (boundedAcyclicQuotientExactFunctor P n).toFunctor =
    acyclicTruncationSequenceFunctor P n ⋙ ShortComplex.π₃ := rfl

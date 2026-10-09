import Lean.Util.CollectAxioms
import Quillen.Waldhausen.GilletWaldhausen.AcyclicTruncation

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless #[`Quillen.Waldhausen.GilletWaldhausen.AcyclicCycles,
      `Quillen.Waldhausen.GilletWaldhausen.BoundedAcyclic,
      `Quillen.Waldhausen.GilletWaldhausen.TruncationMaps,
      `Quillen.Waldhausen.GilletWaldhausen.AcyclicTruncation].contains origin do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless count == 70 do throwError "Unexpected GW algebra origin count: {count}"
  logInfo m!"Audited all {count} bounded acyclic cycle/truncation declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Quillen
open Waldhausen.GilletWaldhausen
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]
  [(abelianExactStructure A).IsExtensionClosed P]
  (K : CochainComplex A ℤ) (n : ℤ) (hK : boundedAcyclic P K)

example : boundedAcyclic P (K.truncLE n) := truncLE_mem K n P hK
example : boundedAcyclic P (K.shortComplexTruncLE n).X₃ :=
  truncationQuotient_mem K n P hK
example : (boundedAcyclicExactStructure P).conflation
    (acyclicTruncationSequence K n P hK) := acyclicTruncationSequence_conflation K n P hK
example : (acyclicTruncationSequence K n P hK).f.hom = (K.shortComplexTruncLE n).f := rfl
example : (acyclicTruncationSequence K n P hK).g.hom = (K.shortComplexTruncLE n).g := rfl
example : (K.shortComplexTruncLE n).X₃.X n ≅ K.cycles (n + 1) :=
  truncationQuotientBoundaryIso K n (hK.2.2 (n + 1))

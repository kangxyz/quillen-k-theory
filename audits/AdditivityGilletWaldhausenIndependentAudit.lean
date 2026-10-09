import Quillen.Waldhausen.Additivity.IntervalArrows
import Quillen.Waldhausen.Additivity.SplitSequence
import Lean.Util.CollectAxioms
import Quillen.Waldhausen.GilletWaldhausen.TruncationCofibrationSequence
import Quillen.Waldhausen.GilletWaldhausen.TruncationLayer
noncomputable section

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless (`Quillen.Waldhausen.GilletWaldhausen).isPrefixOf origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 275 do
    throwError "Expected 275 GW origins, found {count}"
  logInfo m!"Audited all {count} Gillet-Waldhausen-origin declarations, including private/generated declarations; only propext, Classical.choice, Quot.sound."

#print axioms Quillen.Waldhausen.GilletWaldhausen.cycles_mem
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncLE_inclusion_boundary
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncationQuotientBoundaryIso
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncLE_mem
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncationQuotient_mem
#print axioms Quillen.Waldhausen.GilletWaldhausen.acyclicTruncationSequence_conflation

universe v u
open CategoryTheory CategoryTheory.Limits Quillen
open Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    [(abelianExactStructure A).IsExtensionClosed P]
    (K : CochainComplex A ℤ) (n : ℤ) (hK : boundedAcyclic P K) :
    (boundedAcyclicExactStructure P).conflation (acyclicTruncationSequence K n P hK) :=
  acyclicTruncationSequence_conflation K n P hK

#print axioms Quillen.Waldhausen.GilletWaldhausen.truncationSequenceFunctor
#print axioms Quillen.Waldhausen.GilletWaldhausen.acyclicTruncationSequenceFunctor
#print axioms Quillen.Waldhausen.GilletWaldhausen.acyclicTruncationConflationFunctor
#print axioms Quillen.Waldhausen.GilletWaldhausen.acyclicTruncationConflationFunctor_comp_inclusion

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    [(abelianExactStructure A).IsExtensionClosed P] (n : ℤ) :
    (boundedAcyclic P).FullSubcategory ⥤ (boundedAcyclicConflations P).FullSubcategory :=
  acyclicTruncationConflationFunctor P n

#print axioms Quillen.Waldhausen.GilletWaldhausen.cyclesMap_epi_of_exactAt
#print axioms Quillen.Waldhausen.GilletWaldhausen.cycles_shortExact
#print axioms Quillen.Waldhausen.GilletWaldhausen.boundedAcyclicCyclesExactFunctor
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncLE_shortExact
#print axioms Quillen.Waldhausen.GilletWaldhausen.boundedAcyclicTruncLEExactFunctor
#print axioms Quillen.Waldhausen.GilletWaldhausen.boundedAcyclicTruncLEFunctor_eq_first

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    [(abelianExactStructure A).IsExtensionClosed P] (n : ℤ) :
    ExactFunctor (boundedAcyclicExactStructure P) (boundedAcyclicExactStructure P) :=
  boundedAcyclicTruncLEExactFunctor P n

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    [(abelianExactStructure A).IsExtensionClosed P] [P.IsClosedUnderFiniteProducts] (n : ℤ) :
    ExactFunctor (boundedAcyclicExactStructure P)
      (ExactSubcategory.exactStructure (abelianExactStructure A) P) :=
  boundedAcyclicCyclesExactFunctor P n

#print axioms Quillen.Waldhausen.GilletWaldhausen.truncationQuotientBoundaryIso_projection
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncationQuotientBoundaryIso_naturality
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncationQuotient_shortExact
#print axioms Quillen.Waldhausen.GilletWaldhausen.boundedAcyclicQuotientEvalIsoCycles
#print axioms Quillen.Waldhausen.GilletWaldhausen.boundedAcyclicQuotientExactFunctor

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    [(abelianExactStructure A).IsExtensionClosed P] (n : ℤ) :
    ExactFunctor (boundedAcyclicExactStructure P) (boundedAcyclicExactStructure P) :=
  boundedAcyclicQuotientExactFunctor P n

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    [(abelianExactStructure A).IsExtensionClosed P] (n : ℤ) :
    (boundedAcyclicQuotientExactFunctor P n).toFunctor =
      acyclicTruncationSequenceFunctor P n ⋙ ShortComplex.π₃ := rfl

#print axioms Quillen.Waldhausen.GilletWaldhausen.relativePushout_inflation
#print axioms Quillen.Waldhausen.GilletWaldhausen.exactFunctorSequence_isCofibrationSequence
#print axioms Quillen.Waldhausen.GilletWaldhausen.boundedAcyclicTruncation_cofibration
#print axioms Quillen.Waldhausen.GilletWaldhausen.boundedAcyclicTruncation_isCofibrationSequence
#print axioms Quillen.Waldhausen.GilletWaldhausen.boundedAcyclicTruncation_isCofibrationSequence_quasiIso

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    [(abelianExactStructure A).IsExtensionClosed P] (n : ℤ) :
    Waldhausen.Additivity.IsCofibrationSequence
      (Waldhausen.complexSubcategory (boundedAcyclic P))
      (Waldhausen.complexSubcategory (boundedAcyclic P))
      (boundedAcyclicTruncationInclusion P n) (boundedAcyclicTruncationProjection P n) :=
  boundedAcyclicTruncation_isCofibrationSequence_quasiIso P n

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P] (n : ℤ)
    (K : (boundedAcyclic P).FullSubcategory) :
    ((boundedAcyclicTruncationInclusion P n).app K).hom = K.obj.ιTruncLE n := rfl

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P] (n : ℤ)
    (K : (boundedAcyclic P).FullSubcategory) :
    ((boundedAcyclicTruncationProjection P n).app K).hom =
      (K.obj.shortComplexTruncLE n).g := rfl

#print axioms Quillen.Waldhausen.GilletWaldhausen.identityDiskFunctor
#print axioms Quillen.Waldhausen.GilletWaldhausen.identityDisk_acyclic
#print axioms Quillen.Waldhausen.GilletWaldhausen.boundedAcyclicDiskExactFunctor
#print axioms Quillen.Waldhausen.GilletWaldhausen.oneStepLayerDiskIso
#print axioms Quillen.Waldhausen.GilletWaldhausen.oneStepLayerExactFunctor
#print axioms Quillen.Waldhausen.GilletWaldhausen.oneStepCycleDiskExactFunctor

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P] (n : ℤ) :
    oneStepLayerFunctor P n ≅
      boundedAcyclicCyclesFunctor P (n + 1) ⋙ boundedAcyclicDiskFunctor P n :=
  oneStepLayerDiskIso P n

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsExtensionClosed P] [P.IsClosedUnderFiniteProducts] (n : ℤ) :
    ExactFunctor (ExactSubcategory.exactStructure (abelianExactStructure A) P)
      (boundedAcyclicExactStructure P) := boundedAcyclicDiskExactFunctor P n

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P] (n : ℤ)
    (K : (boundedAcyclic P).FullSubcategory) :
    ((oneStepLayerFunctor P n).obj K).obj =
      ((K.obj.truncLE (n + 1)).shortComplexTruncLE n).X₃ := rfl

example {A : Type u} [Category.{v} A] [Abelian A] (n : ℤ) (X : A) :
    (identityDiskFunctor n).obj X = HomologicalComplex.double (𝟙 X)
      (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) := rfl

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let origins := #[`Quillen.Waldhausen.Additivity.CofiberEndpoint,
    `Quillen.Waldhausen.Additivity.CofibrationSequence,
    `Quillen.Waldhausen.Additivity.CoproductAlgebra,
    `Quillen.Waldhausen.Additivity.IntervalArrows,
    `Quillen.Waldhausen.Additivity.PushoutCofibrations,
    `Quillen.Waldhausen.Additivity.PushoutEndpoints,
    `Quillen.Waldhausen.Additivity.PushoutFunctor,
    `Quillen.Waldhausen.Additivity.PushoutInterchange,
    `Quillen.Waldhausen.Additivity.PushoutPreservation,
    `Quillen.Waldhausen.Additivity.SplitSequence,
    `Quillen.Waldhausen.Additivity.ZeroFactorization]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origins.contains origin do continue
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED ADDITIVITY {name}"
  unless count == 167 do
    throwError "Expected 167 frozen additivity origins, found {count}"
  logInfo m!"Audited all {count} frozen additivity-algebra declaration origins."

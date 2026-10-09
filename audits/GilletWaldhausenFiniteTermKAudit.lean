import Quillen.Waldhausen.GilletWaldhausen.FiniteTermKEquivalence
import Quillen.Waldhausen.GilletWaldhausen.BoundedTermsSSetColimit
import Quillen.Waldhausen.GilletWaldhausen.StupidTruncationKMap
import Quillen.Waldhausen.Additivity.BasedAdditivity
import Quillen.Waldhausen.Cylinder.AmbientRelative
import Quillen.Waldhausen.GilletWaldhausen.BoundedTermsAcyclic
import Quillen.PerfectComplexes.Strict
import Quillen.Waldhausen.GilletWaldhausen.CycleEvaluationSequence
import Quillen.Waldhausen.Additivity.RealizedAdditivity
import Quillen.Waldhausen.GilletWaldhausen.BoundedSSetColimit
import Lean.Util.CollectAxioms
import Quillen.Waldhausen.GilletWaldhausen.AdjacentTruncation
import Quillen.Waldhausen.GilletWaldhausen.FixedBounds
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
  unless count == 772 do
    throwError "Expected 772 Gillet-Waldhausen origins, found {count}"
  logInfo m!"Audited all {count} Gillet-Waldhausen-origin declarations, including private/generated declarations; only propext, Classical.choice, Quot.sound."

#print axioms Quillen.Waldhausen.GilletWaldhausen.cycles_mem
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncLE_inclusion_boundary
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncationQuotientBoundaryIso
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncLE_mem
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncationQuotient_mem
#print axioms Quillen.Waldhausen.GilletWaldhausen.acyclicTruncationSequence_conflation

universe v u
open CategoryTheory CategoryTheory.Limits Quillen
open scoped ZeroObject
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

#print axioms Quillen.Waldhausen.GilletWaldhausen.truncLECompMap_isIso
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncLECompIso
#print axioms Quillen.Waldhausen.GilletWaldhausen.truncLECompIso_inclusion
#print axioms Quillen.Waldhausen.GilletWaldhausen.adjacentTruncation_isCofibrationSequence
#print axioms Quillen.Waldhausen.GilletWaldhausen.adjacentTruncation_isCofibrationSequence_quasiIso
#print axioms Quillen.Waldhausen.GilletWaldhausen.fixedBoundsTruncLEZeroIso
#print axioms Quillen.Waldhausen.GilletWaldhausen.fixedBoundsTruncLEIdentityIso
#print axioms Quillen.Waldhausen.GilletWaldhausen.fixedAcyclicExactStructure
#print axioms Quillen.Waldhausen.GilletWaldhausen.fixedAcyclicTruncLEExactFunctor

example {A : Type u} [Category.{v} A] [Abelian A] (n m : ℤ) (h : n < m) :
    (ComplexShape.embeddingUpIntLE m).truncLEFunctor A ⋙
        (ComplexShape.embeddingUpIntLE n).truncLEFunctor A ≅
      (ComplexShape.embeddingUpIntLE n).truncLEFunctor A := truncLECompIso n m h

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    [(abelianExactStructure A).IsExtensionClosed P] (n : ℤ) :
    Waldhausen.Additivity.IsCofibrationSequence
      (Waldhausen.complexSubcategory (boundedAcyclic P))
      (Waldhausen.complexSubcategory (boundedAcyclic P))
      (adjacentTruncationInclusion P n) (adjacentTruncationProjection P n) :=
  adjacentTruncation_isCofibrationSequence_quasiIso P n

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P] (a b : ℤ) :
    (fixedAcyclicBounds P a b).ι ⋙ boundedAcyclicTruncLEFunctor P (a - 1) ≅
      (Functor.const (fixedAcyclicBounds P a b).FullSubcategory).obj
        (0 : (boundedAcyclic P).FullSubcategory) := fixedBoundsTruncLEZeroIso P a b (a - 1) (by omega)

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P] (a b : ℤ) :
    (fixedAcyclicBounds P a b).ι ⋙ boundedAcyclicTruncLEFunctor P b ≅
      (fixedAcyclicBounds P a b).ι := fixedBoundsTruncLEIdentityIso P a b b le_rfl

example {A : Type u} [Category.{v} A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    [(abelianExactStructure A).IsExtensionClosed P] (a b n : ℤ) :
    ExactFunctor (fixedAcyclicExactStructure P a b) (boundedAcyclicExactStructure P) :=
  fixedAcyclicTruncLEExactFunctor P a b n


open scoped Simplicial
open Quillen.Waldhausen
section BoundedCoverage
universe w
variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)

-- Coverage itself does not assume any closure properties on the term predicate.
example {I : Type w} [Finite I] (K : I → (boundedAcyclic P).FullSubcategory) :
    ∃ N : ℕ, ∀ i, HasTermBounds (K i).obj (-(N : ℤ)) N :=
  boundedStratum_covers_finite P K

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
variable (W : MorphismProperty (boundedAcyclic P).FullSubcategory)

-- No ambient kernel-closure or finite-product assumption is an input here.
example (N : ℕ) {X Y : (boundedStratum P N).FullSubcategory} (f : X ⟶ Y) :
    (boundedStratumExactStructure P N).inflation f ↔
      (boundedAcyclicExactStructure P).inflation f.hom :=
  boundedStratum_inflation_iff P N f

example (N : ℕ) :
    boundedStratumWeak P (MorphismProperty.isomorphisms _) N =
      MorphismProperty.isomorphisms _ := by
  ext X Y f
  exact ObjectProperty.isIso_hom_iff f

example (N : ℕ) {X Y : (boundedStratum P N).FullSubcategory} (f : X ⟶ Y) :
    boundedStratumWeak P (complexSubcategory (boundedAcyclic P)).weq N f ↔
      QuasiIso f.hom.hom := Iff.rfl

example {N M : ℕ} (h : N ≤ M) :
    boundedStratumSSetTransition P W h ≫ boundedStratumSSetInclusion P W M =
      boundedStratumSSetInclusion P W N := boundedStratumSSetTransition_inclusion P W h

example : IsColimit (boundedSSetCocone P W) := boundedSSetCocone_isColimit P W

example (N : ℕ) : (boundedSSetCocone P W).ι.app (boundedStageIndex N) =
    boundedStratumSSetInclusion P W N := rfl

example (N M : ℕ) (h : N ≤ M) :
    (boundedSSetDiagram P W).map (AsSmall.up.map (homOfLE h)) =
      boundedStratumSSetTransition P W h := rfl

example : boundedAcyclicSSet P (complexSubcategory (boundedAcyclic P)).weq =
    sSet (complexSubcategory (boundedAcyclic P)).cof (complexSubcategory (boundedAcyclic P)).weq := rfl

example {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, |boundedAcyclicSSet P W|)) :
    ∃ N : ℕ, ∃ g : C(T, |boundedStratumSSet P W N|),
      (SSet.toTop.map (boundedStratumSSetInclusion P W N)).hom.comp g = f :=
  boundedSSet_compact_factors P W f

example {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (N : ℕ) {a b : C(T, |boundedStratumSSet P W N|)} (S : Set T) (hS : IsCompact S)
    (H : ((SSet.toTop.map (boundedStratumSSetInclusion P W N)).hom.comp a).HomotopyRel
      ((SSet.toTop.map (boundedStratumSSetInclusion P W N)).hom.comp b) S) :
    ∃ M : ℕ, ∃ h : N ≤ M,
      Nonempty (((SSet.toTop.map (boundedStratumSSetTransition P W h)).hom.comp a).HomotopyRel
        ((SSet.toTop.map (boundedStratumSSetTransition P W h)).hom.comp b) S) :=
  boundedSSet_homotopyRel_factors P W N S hS H
end BoundedCoverage


section CycleEvaluation
variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)

-- The actual term evaluation exists without closure hypotheses.
example (n : ℤ) {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    ((boundedAcyclicEvaluationFunctor P n).map f).hom = f.hom.f n := rfl

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
local instance : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

-- No kernel-closure hypothesis is used for exact evaluation.
example (n : ℤ) : ExactFunctor (boundedAcyclicExactStructure P)
    (ExactSubcategory.exactStructure (abelianExactStructure A) P) :=
  boundedAcyclicEvaluationExactFunctor P n

variable [(abelianExactStructure A).IsKernelClosed P]
example (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    ((boundedAcyclicCycleInclusion P n).app K).hom = K.obj.iCycles n := rfl
example (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    ((boundedAcyclicCycleProjection P n).app K).hom = K.obj.toCycles n (n + 1) := rfl
example (n : ℤ) : Additivity.IsCofibrationSequence
    (ofExactCategory (boundedAcyclicExactStructure P))
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P))
    (boundedAcyclicCycleInclusion P n) (boundedAcyclicCycleProjection P n) :=
  boundedAcyclicCycleEvaluation_isCofibrationSequence P n
end CycleEvaluation

-- The existing realized S-map API uses a common object/hom universe.
-- In that interface the actual algebraic sequence yields precisely the
-- unbased incidence homotopy, without supplying a homotopy as input.
section RealizedIncidence
variable {A : Type u} [SmallCategory A] [Abelian A] (P : ObjectProperty A)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]
local instance : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P
example (n : ℤ) :
    (deloopingMap (boundedAcyclicEvaluationExactFunctor P n).waldhausenExact).hom.Homotopic
      (deloopingMap (Additivity.sumFunctor_isExact
        (ofExactCategory (boundedAcyclicExactStructure P))
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P))
        (boundedAcyclicCyclesExactFunctor P (n + 1)).waldhausenExact
        (boundedAcyclicCyclesExactFunctor P n).waldhausenExact)).hom :=
  Additivity.deloopingMap_additivity _ _ (boundedAcyclicCycleInclusion P n)
    (boundedAcyclicCycleProjection P n) (boundedAcyclicCycleEvaluation_isCofibrationSequence P n)
end RealizedIncidence


section BoundedTerms
variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)

-- Shifts do not require any closure assumptions on the term predicate.
example {K : CochainComplex A ℤ} (hK : boundedTerms P K) (s : ℤ) :
    boundedTerms P (K⟦s⟧) := boundedTerms_shift P hK s
example {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    ((boundedAcyclicTermsInclusion P).map f).hom = f.hom := rfl

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

-- Neither kernel closure nor projectivity is an input to this ambient category.
example : ExactStructure (boundedTerms P).FullSubcategory := boundedTermsExactStructure P
example {K L : CochainComplex A ℤ} (hK : boundedTerms P K) (hL : boundedTerms P L)
    (f : K ⟶ L) : boundedTerms P (CochainComplex.mappingCone f) :=
  boundedTerms_mappingCone P hK hL f
example : ExactFunctor (boundedAcyclicExactStructure P) (boundedTermsExactStructure P) :=
  boundedAcyclicTermsExactInclusion P
example {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    (boundedTermsExactStructure P).inflation ((boundedAcyclicTermsInclusion P).map f) ↔
      (boundedAcyclicExactStructure P).inflation f :=
  boundedAcyclicTermsInclusion_inflation_iff P f
example : IsExact
    (complexSubcategory (boundedAcyclic P)).cof (complexSubcategory (boundedAcyclic P)).weq
    (complexSubcategory (boundedTerms P)).cof (complexSubcategory (boundedTerms P)).weq
    (boundedAcyclicTermsInclusion P) := boundedAcyclicTermsInclusion_quasiExact P
example {Z K : (boundedTerms P).FullSubcategory} (hZ : IsZero Z) (f : Z ⟶ K) :
    (complexSubcategory (boundedTerms P)).weq f ↔ K.obj.Acyclic :=
  boundedTerms_weq_from_zero_iff P hZ f
example (K : (boundedTerms P).FullSubcategory) :
    (complexSubcategory (boundedTerms P)).weq
      ((complexSubcategory (boundedTerms P)).isZero.to_ K) ↔ boundedAcyclic P K.obj :=
  boundedTerms_weaklyAcyclic_iff P K
-- The proved generic cone/shift closure supplies the actual inherited cylinder endpoints.
example (f : Arrow (boundedTerms P).FullSubcategory) :
    (complexSubcategory (boundedTerms P)).cof
      (SplitFactorization.subcategoryJointInclusion (boundedTerms P)
        (boundedTerms_mappingCone P) f) :=
  (SplitFactorization.subcategoryJointInclusion_cof (boundedTerms P)
    (boundedTerms_mappingCone P) (fun _ hK ↦ boundedTerms_shift P hK 1) f).1
end BoundedTerms

-- On an arbitrary scheme, the generic ambient objects are exactly the
-- already accepted actual strict-perfect complexes, by definition.
example (X : AlgebraicGeometry.Scheme.{u}) :
    boundedTerms (SchemeSheaf.finiteLocallyFree X) = PerfectComplexes.strictPerfect X := rfl


section StupidTruncation
variable {A : Type u} [Category.{v} A] [Abelian A]

-- These are exactly mathlib's original objects, functors, and morphisms.
example (K : CochainComplex A ℤ) (n : ℤ) :
    stupidTruncGE K n = K.stupidTrunc (ComplexShape.embeddingUpIntGE n) := rfl
example (n : ℤ) : stupidTruncGEFunctor (A := A) n =
    (ComplexShape.embeddingUpIntGE n).stupidTruncFunctor A := rfl
example {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (stupidTruncGEFunctor n).map f =
      HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE n) := rfl
example (K : CochainComplex A ℤ) (n i : ℤ) (hi : n ≤ i) :
    (stupidTruncGEInclusion K n).f i = (stupidTruncGEXIso K n i hi).hom :=
  stupidTruncGEInclusion_f_of_le K n i hi
example (K : CochainComplex A ℤ) (n : ℤ) :
    degreewiseSplitMono (stupidTruncGEInclusion K n) :=
  stupidTruncGEInclusion_degreewiseSplitMono K n
example (K : CochainComplex A ℤ) {n m : ℤ} (h : n ≤ m) :
    stupidTruncGETransition K h ≫ stupidTruncGEInclusion K n = stupidTruncGEInclusion K m :=
  stupidTruncGETransition_inclusion K h
example (K : CochainComplex A ℤ) (n : ℤ) :
    (stupidTruncGELayerSequence K n).ShortExact := stupidTruncGELayerSequence_shortExact K n
example (K : CochainComplex A ℤ) (n i : ℤ) :
    ((stupidTruncGELayerSequence K n).map (HomologicalComplex.eval A (ComplexShape.up ℤ) i)).Splitting :=
  stupidTruncGELayerSequenceSplitting K n i
example (K : CochainComplex A ℤ) (n : ℤ) :
    cokernel.π (stupidTruncGELayerSequence K n).f ≫ (stupidTruncGELayerCokernelIso K n).hom =
      stupidTruncGELayerProjection K n := stupidTruncGELayerCokernelIso_projection K n
end StupidTruncation


section StupidExact
variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
-- Membership needs neither extension nor kernel closure.
example {K : CochainComplex A ℤ} (hK : boundedTerms P K) (i : ℤ) :
    boundedTerms P (stupidTruncGE K i) := stupidTruncGE_mem P hK i
example {K L : (boundedTerms P).FullSubcategory} (f : K ⟶ L) (i : ℤ) :
    ((boundedTermsStupidTruncGEFunctor P i).map f).hom =
      HomologicalComplex.stupidTruncMap f.hom (ComplexShape.embeddingUpIntGE i) := rfl
example (K : (boundedTerms P).FullSubcategory) {i j : ℤ} (h : i ≤ j) :
    ((boundedTermsStupidTruncGETransitionNat P h).app K).hom =
      stupidTruncGETransition K.obj h := rfl
example (K : (boundedTerms P).FullSubcategory) (i : ℤ) :
    ((boundedTermsStupidLayerProjectionNat P i).app K).hom =
      stupidTruncGELayerProjection K.obj i := rfl
variable [(abelianExactStructure A).IsExtensionClosed P]
-- Exactness and the genuine relative-pushout axiom need no kernel closure.
example (i : ℤ) : ExactFunctor (boundedTermsExactStructure P) (boundedTermsExactStructure P) :=
  boundedTermsStupidTruncGEExactFunctor P i
example (i : ℤ) : ExactFunctor (boundedTermsExactStructure P) (boundedTermsExactStructure P) :=
  boundedTermsStupidLayerExactFunctor P i
example (i : ℤ) : Additivity.IsCofibrationSequence
    (ofExactCategory (boundedTermsExactStructure P)) (ofExactCategory (boundedTermsExactStructure P))
    (boundedTermsStupidTruncGETransitionNat P (by omega : i ≤ i + 1))
    (boundedTermsStupidLayerProjectionNat P i) := boundedTermsStupidLayer_isCofibrationSequence P i
end StupidExact

section StupidBasedAdditivity
variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
-- This is an equality of the actual public normalized K-maps in the iso model.
-- It is not a quasi-isomorphism assertion or an arithmetic sum of K homomorphisms.
theorem brutal_KMap_additivity (i : ℤ) (n : ℕ) :
    KMap (boundedTermsStupidTruncGEExactFunctor P i).waldhausenExact n =
      KMap (Additivity.sumFunctor_isExact
        (ofExactCategory (boundedTermsExactStructure P))
        (ofExactCategory (boundedTermsExactStructure P))
        (boundedTermsStupidLayerExactFunctor P i).waldhausenExact
        (boundedTermsStupidTruncGEExactFunctor P (i + 1)).waldhausenExact) n :=
  Additivity.KMap_additivity _ _ (boundedTermsStupidTruncGETransitionNat P (by omega : i ≤ i + 1))
    (boundedTermsStupidLayerProjectionNat P i) (boundedTermsStupidLayer_isCofibrationSequence P i) n
#print axioms brutal_KMap_additivity
end StupidBasedAdditivity


section StupidFixedBounds
variable {A : Type u} [Category.{v} A] [Abelian A]
-- The raw endpoints require only genuine actual term bounds.
example (K : CochainComplex A ℤ) (a b i : ℤ) (hK : HasTermBounds K a b) (hi : b < i) :
    IsZero (stupidTruncGE K i) := stupidTruncGE_isZero_above_bound K a b i hK hi
example (K : CochainComplex A ℤ) (a b i : ℤ) (hK : HasTermBounds K a b) (hi : i ≤ a) :
    IsIso (stupidTruncGEInclusion K i) := stupidTruncGEInclusion_isIso_below_bound K a b i hK hi
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
-- The original upper and lower endpoints need no kernel or extension closure.
example (a b i : ℤ) (hi : b < i) :
    (fixedTermsBounds P a b).ι ⋙ boundedTermsStupidTruncGEFunctor P i ≅
      (Functor.const (fixedTermsBounds P a b).FullSubcategory).obj
        (0 : (boundedTerms P).FullSubcategory) := fixedTermsStupidTruncGEZeroIso P a b i hi
example (a b i : ℤ) (hi : i ≤ a) (K : (fixedTermsBounds P a b).FullSubcategory) :
    (((fixedTermsStupidTruncGEIdentityIso P a b i hi).hom.app K).hom) =
      stupidTruncGEInclusion K.obj.obj i := rfl
variable [(abelianExactStructure A).IsExtensionClosed P]
-- Independent object/hom universes, no acyclicity or kernel closure.
example (a b : ℤ) : ExactStructure (fixedTermsBounds P a b).FullSubcategory :=
  fixedTermsExactStructure P a b
example (a b i : ℤ) {K L : (fixedTermsBounds P a b).FullSubcategory} (f : K ⟶ L) :
    ((fixedTermsStupidTruncGEExactFunctor P a b i).toFunctor.map f).hom =
      HomologicalComplex.stupidTruncMap f.hom.hom (ComplexShape.embeddingUpIntGE i) := rfl
example (a b i : ℤ) (hi : i ≤ a) (k : ℕ) :
    KMap (fixedTermsStupidTruncGEExactFunctor P a b i).waldhausenExact k =
      KMap (fixedTermsInclusionExactFunctor P a b).waldhausenExact k :=
  fixedTermsStupidTruncGE_KMap_inclusion P a b i hi k
example (a b i : ℤ) (hi : b < i) (k : ℕ) :
    KMap (fixedTermsStupidTruncGEExactFunctor P a b i).waldhausenExact k = 1 :=
  fixedTermsStupidTruncGE_KMap_zero P a b i hi k
example (a b i : ℤ) (k : ℕ) :
    KMap (fixedTermsStupidTruncGEExactFunctor P a b i).waldhausenExact k =
      (KMap (boundedTermsStupidTruncGEExactFunctor P i).waldhausenExact k).comp
        (KMap (fixedTermsInclusionExactFunctor P a b).waldhausenExact k) :=
  fixedTermsStupidTruncGE_KMap_comp P a b i k
end StupidFixedBounds


section BoundedTermsCoverage
universe w
variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)

-- Coverage itself does not assume any closure properties on the term predicate.
example {I : Type w} [Finite I] (K : I → (boundedTerms P).FullSubcategory) :
    ∃ N : ℕ, ∀ i, HasTermBounds (K i).obj (-(N : ℤ)) N :=
  boundedTermsStratum_covers_finite P K

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
variable (W : MorphismProperty (boundedTerms P).FullSubcategory)

-- No ambient kernel-closure or finite-product assumption is an input here.
example (N : ℕ) {X Y : (boundedTermsStratum P N).FullSubcategory} (f : X ⟶ Y) :
    (boundedTermsStratumExactStructure P N).inflation f ↔
      (boundedTermsExactStructure P).inflation f.hom :=
  boundedTermsStratum_inflation_iff P N f

example (N : ℕ) :
    boundedTermsStratumWeak P (MorphismProperty.isomorphisms _) N =
      MorphismProperty.isomorphisms _ := by
  ext X Y f
  exact ObjectProperty.isIso_hom_iff f

example (N : ℕ) {X Y : (boundedTermsStratum P N).FullSubcategory} (f : X ⟶ Y) :
    boundedTermsStratumWeak P (complexSubcategory (boundedTerms P)).weq N f ↔
      QuasiIso f.hom.hom := Iff.rfl

example {N M : ℕ} (h : N ≤ M) :
    boundedTermsStratumSSetTransition P W h ≫ boundedTermsStratumSSetInclusion P W M =
      boundedTermsStratumSSetInclusion P W N := boundedTermsStratumSSetTransition_inclusion P W h

example : IsColimit (boundedTermsSSetCocone P W) := boundedTermsSSetCocone_isColimit P W

example (N : ℕ) : (boundedTermsSSetCocone P W).ι.app (boundedStageIndex N) =
    boundedTermsStratumSSetInclusion P W N := rfl

example (N M : ℕ) (h : N ≤ M) :
    (boundedTermsSSetDiagram P W).map (AsSmall.up.map (homOfLE h)) =
      boundedTermsStratumSSetTransition P W h := rfl

example : boundedTermsSSet P (complexSubcategory (boundedTerms P)).weq =
    sSet (complexSubcategory (boundedTerms P)).cof (complexSubcategory (boundedTerms P)).weq := rfl

example {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, |boundedTermsSSet P W|)) :
    ∃ N : ℕ, ∃ g : C(T, |boundedTermsStratumSSet P W N|),
      (SSet.toTop.map (boundedTermsStratumSSetInclusion P W N)).hom.comp g = f :=
  boundedTermsSSet_compact_factors P W f

example {T : Type w} [TopologicalSpace T] [CompactSpace T]
    (N : ℕ) {a b : C(T, |boundedTermsStratumSSet P W N|)} (S : Set T) (hS : IsCompact S)
    (H : ((SSet.toTop.map (boundedTermsStratumSSetInclusion P W N)).hom.comp a).HomotopyRel
      ((SSet.toTop.map (boundedTermsStratumSSetInclusion P W N)).hom.comp b) S) :
    ∃ M : ℕ, ∃ h : N ≤ M,
      Nonempty (((SSet.toTop.map (boundedTermsStratumSSetTransition P W h)).hom.comp a).HomotopyRel
        ((SSet.toTop.map (boundedTermsStratumSSetTransition P W h)).hom.comp b) S) :=
  boundedTermsSSet_homotopyRel_factors P W N S hS H
end BoundedTermsCoverage


section FiniteTermAlgebra
variable {A : Type u} [Category.{v} A] [Abelian A]
-- Raw bound retention uses genuine original mono/epi maps only.
example {K : CochainComplex A ℤ} {a b : ℤ} (h : HasTermBounds K a b) (i : ℤ) :
    HasTermBounds (stupidTruncGE K i) a b := h.stupidTruncGE i
example {K : CochainComplex A ℤ} {a b : ℤ} (h : HasTermBounds K a b) (i : ℤ) :
    HasTermBounds ((stupidTruncGELayerFunctor i).obj K) a b := h.stupidLayer i
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
example (a b i : ℤ) (hi : i ≤ a) (K : (fixedTermsBounds P a b).FullSubcategory) :
    (((finiteTermIdentityIso P a b i hi).hom.app K).hom.hom) =
      stupidTruncGEInclusion K.obj.obj i := rfl
example (a b i : ℤ) {K L : (fixedTermsBounds P a b).FullSubcategory} (f : K ⟶ L) :
    ((finiteTermTruncation P a b i).map f).hom.hom =
      HomologicalComplex.stupidTruncMap f.hom.hom (ComplexShape.embeddingUpIntGE i) := rfl
example (a b i : ℤ) (ha : a ≤ i) (hb : i ≤ b) {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((finiteTermSingle P a b i ha hb).map f).hom.hom =
      (HomologicalComplex.single A (ComplexShape.up ℤ) i).map f.hom := rfl
example (a b i : ℤ) (ha : a ≤ i) (hb : i ≤ b) (X : P.FullSubcategory) :
    (((finiteTermSingleEvaluationIso P a b i ha hb).hom.app X).hom) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i X.obj).hom := rfl
variable [(abelianExactStructure A).IsExtensionClosed P]
example (a b i : ℤ) : Additivity.IsCofibrationSequence
    (ofExactCategory (fixedTermsExactStructure P a b)) (ofExactCategory (fixedTermsExactStructure P a b))
    (finiteTermTransition P a b (by omega : i ≤ i + 1)) (finiteTermProjection P a b i) :=
  finiteTerm_isCofibrationSequence P a b i
-- Literal finite multiplication, including K₀, is derived rather than hypothesized.
example (a b : ℤ) (m : ℕ) (hm : b < a + (m : ℤ)) (k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a b)).K k) :
    let := Additivity.KCommGroup (ofExactCategory (fixedTermsExactStructure P a b)) k
    x = ∏ i : Fin m, KMap (finiteTermLayerExact P a b (a + (i : ℤ))).waldhausenExact k x :=
  finiteTerm_KMap_layers P a b m hm k x
end FiniteTermAlgebra

section FiniteTermK
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
local instance : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P
-- The genuine finite equivalence has no kernel closure or equivalence input.
example (a : ℤ) (m k : ℕ) :
    (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))).K k ≃*
      (Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :=
  finiteTermKEquiv P a m k
example (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))).K k) (i : Fin m) :
    finiteTermKEquiv P a m k x i = KMap (finiteTermEvaluationExact P a (a + (m : ℤ) - 1)
      (a + (i : ℤ))).waldhausenExact k x := rfl
example (a : ℤ) (m k : ℕ)
    (x : Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    (finiteTermKEquiv P a m k).symm x = finiteTermReassemble P a m k x := rfl
-- Empty actual intervals and the original K₀ are both included.
example (a : ℤ) (x : (ofExactCategory (fixedTermsExactStructure P a (a + (0 : ℤ) - 1))).K 0) :
    x = 1 := by
  have h := finiteTerm_KMap_layers P a (a + (0 : ℤ) - 1) 0 (by omega) 0 x
  simpa using h
-- This is exactly the isomorphism weak model of the genuine inherited structure.
example (a b : ℤ) {K L : (fixedTermsBounds P a b).FullSubcategory} (f : K ⟶ L) :
    (ofExactCategory (fixedTermsExactStructure P a b)).weq f ↔ IsIso f := Iff.rfl
end FiniteTermK

-- The compatible universe contract includes arbitrary scheme sheaves.
-- No noetherian, regularity, resolution-property or global-projectivity input.
noncomputable def strictFiniteTermKEquiv (X : AlgebraicGeometry.Scheme.{u}) (a : ℤ) (m k : ℕ) :=
  finiteTermKEquiv.{u, u+1} (SchemeSheaf.finiteLocallyFree X) a m k
#print axioms strictFiniteTermKEquiv

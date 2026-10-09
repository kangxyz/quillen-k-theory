import Quillen.Waldhausen.Fibration.TrivialCofibrations.Classifying
import Quillen.Waldhausen.Fibration.Rows.TrivialCofibrationCylinder
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.TrivialCofibrations.Category,
    `Quillen.Waldhausen.Fibration.TrivialCofibrations.CommaCylinder,
    `Quillen.Waldhausen.Fibration.Rows.TrivialCofibrationCylinder,
    `Quillen.Waldhausen.Fibration.TrivialCofibrations.Classifying]
  let mut counts : Array Nat := #[0,0,0,0]
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
  unless counts == #[39,27,13,5] && count == 84 do throwError "Expected exactly 84 comparison origins, found {count}"
  logInfo m!"Audited {count} genuine weak-cofibration comparison origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.TrivialCofibrations
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Generic
variable {C : Type u} [Category.{v} C]
  (cof weq : MorphismProperty C) [cof.IsMultiplicative] [weq.IsMultiplicative]
  (D : CylinderData cof weq) [weq.HasTwoOutOfThreeProperty] (Y : WeakCategory weq)
example (X : CofibrationCategory cof weq) : ((inclusion cof weq).obj X).obj = X.obj := rfl
example {X Y : CofibrationCategory cof weq} (f : X ⟶ Y) : ((inclusion cof weq).map f).hom = f.hom := rfl
example (F : Over cof weq Y) : ((overArrow cof weq Y).obj F).hom = F.hom.hom := rfl
example {F G : Over cof weq Y} (α : F ⟶ G) :
    ((overArrow cof weq Y).map α).left = α.left.hom := rfl
example {F G : Over cof weq Y} (α : F ⟶ G) :
    ((overArrow cof weq Y).map α).right = 𝟙 Y.obj := rfl
example (F : Over cof weq Y) :
    (overCylinderObj cof weq D Y F).hom.hom = D.projection.app (Arrow.mk F.hom.hom) := rfl
example (F : Over cof weq Y) :
    ((overInclusion cof weq D Y).app F).left.hom = D.inclusion.app (Arrow.mk F.hom.hom) := rfl
example (F : Over cof weq Y) :
    ((overTarget cof weq D Y).app F).left.hom = D.target.app (Arrow.mk F.hom.hom) := rfl
example (F : Over cof weq Y) :
    cof (((overTarget cof weq D Y).app F).left.hom) ∧
      weq (((overTarget cof weq D Y).app F).left.hom) :=
  ((overTarget cof weq D Y).app F).left.property
example (F : Over cof weq Y) :
    ((overTarget cof weq D Y).app F).left.hom ≫
      (overCylinderObj cof weq D Y F).hom.hom = 𝟙 Y.obj := D.target_projection _
example : ContractibleSpace (ClassifyingSpace (Over cof weq Y)) := comma_contractible cof weq D Y
example : (ContinuousMap.id (ClassifyingSpace (Over cof weq Y))).Homotopy
    (ContinuousMap.const _ (classifyingSpacePoint (overPoint cof weq Y))) := commaContraction cof weq D Y
example (F : Over cof weq Y) :
    cof (((overInclusion cof weq D Y).app F).left.hom) ∧
      weq (((overInclusion cof weq D Y).app F).left.hom) :=
  ((overInclusion cof weq D Y).app F).left.property
example {F G : Over cof weq Y} (α : F ⟶ G) :
    ((overCylinder cof weq D Y).map α).left.hom =
      D.middle.map (Arrow.homMk α.left.hom (𝟙 Y.obj)
        (by
          have h := congrArg (fun f ↦ f.hom) (CostructuredArrow.w α)
          change α.left.hom ≫ G.hom.hom = F.hom.hom at h
          change α.left.hom ≫ G.hom.hom = F.hom.hom ≫ 𝟙 Y.obj
          simpa only [Category.comp_id] using h)) := rfl
end Generic
section Small
variable {C : Type u} [SmallCategory C]
  (cof weq : MorphismProperty C) [cof.IsMultiplicative] [weq.IsMultiplicative]
  (D : CylinderData cof weq) [weq.HasTwoOutOfThreeProperty]
example : ContinuousMap.HomotopyEquiv (ClassifyingSpace (CofibrationCategory cof weq))
    (ClassifyingSpace (WeakCategory weq)) := inclusionClassifyingHomotopyEquiv cof weq D
example : (inclusionClassifyingHomotopyEquiv cof weq D).toFun =
    (classifyingSpaceMap (inclusion cof weq)).hom := inclusionClassifyingHomotopyEquiv_toFun cof weq D
end Small
section Rows
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : RowFactorization.JointData N)
  (hs : RowFactorization.SecondEndpointSection N D) (n : SimplexCategory)
example : CylinderData (RowWeakEquivalences.coarseStructure N n).cof
    (RowWeakEquivalences.coarseStructure N n).weq := RowFactorization.trivialCofibrationCylinder N D hs n
example : (RowFactorization.trivialCofibrationCylinder N D hs n).target =
    RowFactorization.targetInclusion N D n := rfl
example : (RowFactorization.trivialCofibrationCylinder N D hs n).projection =
    (RowFactorization.factorization N D n).projection := rfl
example (f : Arrow (QuotientRows.Obj V n)) :
    ((RowFactorization.trivialCofibrationCylinder N D hs n).target.app f) ≫
      ((RowFactorization.trivialCofibrationCylinder N D hs n).projection.app f) = 𝟙 f.right :=
  (RowFactorization.trivialCofibrationCylinder N D hs n).target_projection f
end Rows
section Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
example (X : Scheme.{u}) (n : SimplexCategory) :
    CylinderData (RowWeakEquivalences.coarseStructure (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) n).cof
      (RowWeakEquivalences.coarseStructure (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) n).weq :=
  complexRowTrivialCofibrationCylinder (boundedTerms (SchemeSheaf.finiteLocallyFree X))
    (fun hK hL f ↦ boundedTerms_mappingCone _ hK hL f)
    (fun _ hK ↦ boundedTerms_shift _ hK 1) n
end Scheme

section SmallRows
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : RowFactorization.JointData N)
  (hs : RowFactorization.SecondEndpointSection N D) (n : SimplexCategory)
  [N.coarse.weq.HasTwoOutOfThreeProperty]
example : (inclusionClassifyingHomotopyEquiv
    (RowWeakEquivalences.coarseStructure N n).cof
    (RowWeakEquivalences.coarseStructure N n).weq
    (RowFactorization.trivialCofibrationCylinder N D hs n)).toFun =
      (classifyingSpaceMap (inclusion
        (RowWeakEquivalences.coarseStructure N n).cof
        (RowWeakEquivalences.coarseStructure N n).weq)).hom :=
  inclusionClassifyingHomotopyEquiv_toFun _ _ _
end SmallRows

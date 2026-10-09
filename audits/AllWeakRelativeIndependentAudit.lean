import Quillen.Waldhausen.Fibration.AllWeak.RelativeContractible
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.AllWeak.Basic,
    `Quillen.Waldhausen.Fibration.AllWeak.CoproductCylinder,
    `Quillen.Waldhausen.Fibration.AllWeak.RelativeContractible]
  let mut counts : Array Nat := #[0, 0, 0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (· + 1)
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing defining module {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless counts == #[26, 14, 4] do throwError "Expected44 origins, got {counts}"
  logInfo m!"Audited all all-weak relative origins: {counts}"

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section ArbitraryUniverses
variable {C : Type u} [Category.{v} C] (W : Structure C)
example : (AllWeak.waldhausenStructure W).cof = W.cof := rfl
example : (AllWeak.waldhausenStructure W).zero = W.zero := rfl
example {X Y : C} (f : X ⟶ Y) : (AllWeak.waldhausenStructure W).weq f := AllWeak.weak W f
example (X : C) : Acyclic (AllWeak.waldhausenStructure W) X := AllWeak.acyclic W X
example : ExtensionAxiom (AllWeak.waldhausenStructure W) := AllWeak.extensionAxiom W
example : (AllWeak.waldhausenStructure W).weq.HasTwoOutOfThreeProperty := inferInstance
example (X : C) : (AllWeak.zeroToIdentity W).app X = W.isZero.to_ X := rfl
example : (ContinuousMap.id (AllWeak.waldhausenStructure W).Delooping).Homotopy
    (ContinuousMap.const _ (AllWeak.waldhausenStructure W).kBasepoint) := AllWeak.contraction W
example (t : unitInterval) :
    AllWeak.contraction W (t, (AllWeak.waldhausenStructure W).kBasepoint) =
      (AllWeak.waldhausenStructure W).kBasepoint := AllWeak.contraction_fixed_zero W t
example : ContractibleSpace (AllWeak.waldhausenStructure W).Delooping := inferInstance
example : RowFactorization.JointData (AllWeak.nested W) := AllWeak.jointData W
example : RowFactorization.SecondEndpointSection (AllWeak.nested W) (AllWeak.jointData W) :=
  AllWeak.jointData_secondEndpointSection W
variable [HasBinaryCoproducts C]
example (f : Arrow C) : ((AllWeak.coproductJointData W).joint.obj f).obj.hom =
    𝟙 (f.left ⨿ f.right) := rfl
example (f : Arrow C) : (AllWeak.coproductJointData W).inl.app f =
    (coprod.inl : f.left ⟶ f.left ⨿ f.right) := rfl
example (f : Arrow C) : (AllWeak.coproductJointData W).inr.app f =
    (coprod.inr : f.right ⟶ f.left ⨿ f.right) := rfl
example (f : Arrow C) : (AllWeak.coproductJointData W).projection.app f =
    coprod.desc f.hom (𝟙 f.right) := rfl
example : IsExact (ArrowCategory.waldhausenStructure W).cof
    (ArrowCategory.waldhausenStructure W).weq
    (ExtensionCategory.waldhausenStructure W).cof
    (ExtensionCategory.waldhausenStructure W).weq (AllWeak.coproductJointData W).joint :=
  (AllWeak.coproductJointData W).exact
end ArbitraryUniverses
section CommonUniverse
variable {C : Type u} [SmallCategory C] (W : Structure C)
example : ContractibleSpace
    |TheoremA.diagonalSSet (RelativeRows.relativeSRows (AllWeak.nested W))| := inferInstance
example : (AllWeak.relativeEvaluationHomotopyEquiv W).toFun =
    (SSet.toTop.map (RelativeRows.coarseEvaluation (AllWeak.nested W)
      (AllWeak.extensionAxiom W))).hom := AllWeak.relativeEvaluationHomotopyEquiv_toFun W
example : (AllWeak.relativeEvaluationHomotopyEquiv W).toFun
    (RelativeRows.totalBasepoint (AllWeak.nested W)) =
      (AllWeak.waldhausenStructure W).kBasepoint :=
  AllWeak.relativeEvaluationHomotopyEquiv_basepoint W
example {V : Structure C} (N : NestedWeakEquivalences V) :
    ContractibleSpace |TheoremA.diagonalSSet
      (RelativeRows.relativeSRows (AllWeak.nested (acyclicStructure N)))| := inferInstance
example {V : Structure C} (n : SimplexCategory) :
    RowFactorization.SecondEndpointSection
      (AllWeak.nested (QuotientRows.waldhausenStructure V n))
      (AllWeak.jointData (QuotientRows.waldhausenStructure V n)) :=
  AllWeak.jointData_secondEndpointSection _
end CommonUniverse
section BoundedTerms
open GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [SmallCategory A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example : ContractibleSpace |TheoremA.diagonalSSet
    (RelativeRows.relativeSRows (AllWeak.nested (ofExactCategory (boundedTermsExactStructure P))))| :=
  inferInstance
end BoundedTerms

section StrongerOriginalConsumers
variable {C : Type u} [Category.{v} C] (W : Structure C)
example : (AllWeak.nested W).coarse.weq = (⊤ : MorphismProperty C) := rfl
example (n : SimplexCategory) {X Y : RelativeRows.Obj (AllWeak.nested W) n} (f : X ⟶ Y) :
    (RelativeRows.waldhausenStructure (AllWeak.nested W) n).weq f ↔
      ∀ p : Interval (RelativeRows.addInitial.obj n),W.weq (f.hom.hom.app p) := Iff.rfl
example [HasBinaryCoproducts C] (f : Arrow C) :
    (AllWeak.coproductJointData W).inl.app f ≫
      ((AllWeak.coproductJointData W).joint.obj f).obj.hom ≫
      (AllWeak.coproductJointData W).projection.app f = f.hom :=
  (AllWeak.coproductJointData W).factorization f
example [HasBinaryCoproducts C] (f : Arrow C) :
    (AllWeak.coproductJointData W).inr.app f ≫
      ((AllWeak.coproductJointData W).joint.obj f).obj.hom ≫
      (AllWeak.coproductJointData W).projection.app f = 𝟙 f.right :=
  AllWeak.coproductJointData_secondEndpointSection W f
example (x : (AllWeak.waldhausenStructure W).Delooping) : AllWeak.contraction W (0,x) = x :=
  (AllWeak.contraction W).map_zero_left x
example (x : (AllWeak.waldhausenStructure W).Delooping) : AllWeak.contraction W (1,x) =
    (AllWeak.waldhausenStructure W).kBasepoint := (AllWeak.contraction W).map_one_left x
end StrongerOriginalConsumers
section StrongerCommonUniverse
variable {C : Type u} [SmallCategory C] (W : Structure C)
example : RelativeRows.totalFiberInclusion (AllWeak.nested W) ≫
    RelativeRows.coarseEvaluation (AllWeak.nested W) (AllWeak.extensionAxiom W) =
      sSetMap (changeWeak_exact (AllWeak.nested W)) :=
  RelativeRows.totalFiberInclusion_coarseEvaluation _ _
example : (AllWeak.relativeEvaluationHomotopyEquiv W).invFun.comp
    (SSet.toTop.map (RelativeRows.coarseEvaluation (AllWeak.nested W)
      (AllWeak.extensionAxiom W))).hom |>.Homotopic (.id _) := by
  rw [← AllWeak.relativeEvaluationHomotopyEquiv_toFun]
  exact (AllWeak.relativeEvaluationHomotopyEquiv W).left_inv
end StrongerCommonUniverse

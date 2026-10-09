import Quillen.Waldhausen.Fibration.RelativeRows.CoarseEvaluation
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.Waldhausen.Fibration.ComplexExtension
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.FiberFiltration,
    `Quillen.Waldhausen.Fibration.RelativeRows.CoarseEvaluation]
  let mut counts : Array Nat := #[0,0]
  let mut total : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    total := total+1
    counts := counts.modify i (·+1)
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing origin {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless total == 24 && counts == #[4,20] do
    throwError "Expected fixed24 origins (4+20), found {total}: {counts}"
  logInfo m!"FIXED24 PASSED {total}: {counts}"
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.RelativeRows
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Categorical
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example (n : SimplexCategory) : fiber N n ⋙ initialFiltrationFunctor N n =
    Functor.const (Fin (n.len+1)) := fiber_initialFiltrationFunctor N n
example (n : SimplexCategory) (X : C) {i j : Fin (n.len+1)} (f : i ⟶ j) :
    ((initialFiltrationFunctor N n).obj ((fiber N n).obj X)).map f = 𝟙 X := rfl
example (n : SimplexCategory) {X Y : C} (f : X ⟶ Y) (i : Fin (n.len+1)) :
    ((initialFiltrationFunctor N n).map ((fiber N n).map f)).app i = f := rfl
example (X : C) : ((initialFiltrationFunctor N ⦋0⦌).obj ((fiber N ⦋0⦌).obj X)).obj 0 = X := rfl
end Categorical
section OriginalModels
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse)
example : coarseEvaluation N he = relativeFiltrationTotalMap N he ≫ MixedNerves.totalCofEvaluation N := rfl
example (n : SimplexCategory) (F : (TheoremA.diagonalSSet (relativeSRows N)).obj (op n))
    (i : Fin (n.len+1)) (p : Interval n) :
    (((coarseEvaluation N he).app (op n) F).val.obj (i,p)) =
      (F.val.obj (i,p)).obj.obj.obj (interval 0 i.succ (Fin.zero_le _)) := rfl
example : totalFiberInclusion N ≫ coarseEvaluation N he = sSetMap (changeWeak_exact N) :=
  totalFiberInclusion_coarseEvaluation N he
example (n : SimplexCategoryᵒᵖ) (F : (sSet V.cof V.weq).obj n) :
    (coarseEvaluation N he).app n ((totalFiberInclusion N).app n F) =
      (sSetMap (changeWeak_exact N)).app n F := by
  exact congrArg (fun f ↦ f.app n F) (totalFiberInclusion_coarseEvaluation N he)
example : (SSet.toTop.map (coarseEvaluation N he)).hom.comp
    (SSet.toTop.map (totalFiberInclusion N)).hom = changeWeakMap N :=
  totalFiberInclusion_coarseEvaluation_realized N he
example (n : SimplexCategory) :
    (coarseEvaluation N he).app (op n)
      (zeroSimplex (waldhausenStructure N n).cof (waldhausenStructure N n).weq
        (zero N n) (isZero N n) (op n)) =
      zeroSimplex N.coarse.cof N.coarse.weq N.coarse.zero N.coarse.isZero (op n) :=
  coarseEvaluation_zeroSimplex N he n
example (n : SimplexCategory) :
    (totalFiberInclusion N).app (op n) (zeroSimplex V.cof V.weq V.zero V.isZero (op n)) =
      zeroSimplex (waldhausenStructure N n).cof (waldhausenStructure N n).weq
        (zero N n) (isZero N n) (op n) := totalFiberInclusion_zeroSimplex N n
example : SSet.toTop.map (coarseEvaluation N he) (totalBasepoint N) = N.coarse.kBasepoint :=
  coarseEvaluation_basepoint N he
example : SSet.toTop.map (totalFiberInclusion N) V.kBasepoint = totalBasepoint N :=
  totalFiberInclusion_basepoint N
example : (coarseEvaluation N he).app (op ⦋0⦌) (totalZeroVertex N) =
    zeroSimplex N.coarse.cof N.coarse.weq N.coarse.zero N.coarse.isZero (op ⦋0⦌) :=
  coarseEvaluation_zeroSimplex N he ⦋0⦌
variable (D : RowFactorization.JointData N) (hs : RowFactorization.SecondEndpointSection N D)
  [N.coarse.weq.HasTwoOutOfThreeProperty]
example : ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (relativeSRows N)|
    |sSet N.coarse.cof N.coarse.weq| := coarseEvaluationHomotopyEquiv N he D hs
example : (coarseEvaluationHomotopyEquiv N he D hs).toFun =
    (SSet.toTop.map (coarseEvaluation N he)).hom := coarseEvaluationHomotopyEquiv_toFun N he D hs
example : (coarseEvaluationHomotopyEquiv N he D hs).toFun (totalBasepoint N) = N.coarse.kBasepoint := by
  rw [coarseEvaluationHomotopyEquiv_toFun]
  exact coarseEvaluation_basepoint N he
example : (coarseEvaluationHomotopyEquiv N he D hs).invFun.comp
    (SSet.toTop.map (coarseEvaluation N he)).hom |>.Homotopic (.id _) := by
  rw [← coarseEvaluationHomotopyEquiv_toFun]
  exact (coarseEvaluationHomotopyEquiv N he D hs).left_inv
end OriginalModels

open CochainComplex Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
namespace BoundedTermsRelativeCoarseConsumer
variable {A : Type u} [SmallCategory A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- Only the original term-subcategory hypotheses; all cylinder/section/extension
inputs are the actual already proved bounded-complex constructions. -/
def actualEquiv :
    ContinuousMap.HomotopyEquiv
      |TheoremA.diagonalSSet (RelativeRows.relativeSRows (boundedTermsNested P))|
      |sSet (boundedTermsNested P).coarse.cof (boundedTermsNested P).coarse.weq| := by
  letI : (boundedTermsNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (boundedTerms P)
  exact RelativeRows.coarseEvaluationHomotopyEquiv (boundedTermsNested P)
    (complexSubcategory_extensionAxiom (boundedTerms P))
    (complexJointData (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ hK ↦ boundedTerms_shift P hK 1))
    (complexJointData_secondEndpointSection (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ hK ↦ boundedTerms_shift P hK 1))

/-- The consumer retains the exact original relative-to-coarse S-map. -/
example : (actualEquiv P).toFun =
    (SSet.toTop.map (RelativeRows.coarseEvaluation (boundedTermsNested P)
      (complexSubcategory_extensionAxiom (boundedTerms P)))).hom := by
  let : (boundedTermsNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (boundedTerms P)
  exact RelativeRows.coarseEvaluationHomotopyEquiv_toFun (boundedTermsNested P)
    (complexSubcategory_extensionAxiom (boundedTerms P))
    (complexJointData (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ hK ↦ boundedTerms_shift P hK 1))
    (complexJointData_secondEndpointSection (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ hK ↦ boundedTerms_shift P hK 1))

#print axioms actualEquiv
end BoundedTermsRelativeCoarseConsumer

section IndependentCanonicalArrows
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse)
example (n : SimplexCategory) (F : (sSet V.cof V.weq).obj (op n))
    {a b : Grid n} (f : a ⟶ b) :
    (((coarseEvaluation N he).app (op n) ((totalFiberInclusion N).app (op n) F)).val.map f) =
      F.val.map f := by
  change F.val.map (homOfLE (show a ≤ (a.1,b.2) from ⟨le_rfl,(leOfHom f).2⟩)) ≫
    (𝟙 _ ≫ F.val.map (homOfLE (show (a.1,b.2) ≤ b from ⟨(leOfHom f).1,le_rfl⟩))) = F.val.map f
  simp only [Category.id_comp, ← F.val.map_comp]
  rfl
example (F : (sSet V.cof V.weq).obj (op ⦋0⦌)) :
    (((coarseEvaluation N he).app (op ⦋0⦌) ((totalFiberInclusion N).app (op ⦋0⦌) F)).val.obj
      (0, interval 0 0 le_rfl)) = F.val.obj (0, interval 0 0 le_rfl) := by
  exact congrArg (fun X ↦ (X.app (op ⦋0⦌) F).val.obj (0, interval 0 0 le_rfl))
    (totalFiberInclusion_coarseEvaluation N he)
example : totalZeroVertex N = zeroSimplex (waldhausenStructure N ⦋0⦌).cof
    (waldhausenStructure N ⦋0⦌).weq (zero N ⦋0⦌) (isZero N ⦋0⦌) (op ⦋0⦌) := rfl
example (D : RowFactorization.JointData N) (hs : RowFactorization.SecondEndpointSection N D)
    [N.coarse.weq.HasTwoOutOfThreeProperty] (x : V.Delooping) :
    (coarseEvaluationHomotopyEquiv N he D hs).toFun (SSet.toTop.map (totalFiberInclusion N) x) =
      changeWeakMap N x := by
  rw [coarseEvaluationHomotopyEquiv_toFun]
  exact DFunLike.congr_fun (totalFiberInclusion_coarseEvaluation_realized N he) x
example {D : Type u} [Category.{v} D] (W : Structure D) (M : NestedWeakEquivalences W)
    (n : SimplexCategory) {X Y : D} (f : X ⟶ Y) :
    ((initialFiltrationFunctor M n).map ((fiber M n).map f)).app 0 = f := rfl
end IndependentCanonicalArrows

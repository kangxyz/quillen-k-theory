import Quillen.Waldhausen.Fibration.MixedNerves.TotalEvaluation
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.MixedNerves.TotalEvaluation]
  let mut counts : Array Nat := #[0]
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
  unless counts == #[18] do throwError "Expected18 origins, got {counts}"
  logInfo m!"Audited {count} original total-evaluation origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.MixedNerves
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Generic
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example : coarseRowDiagonals N ⟶ coarseWeakRowNerve N := coarseRowEvaluation N
example (m : SimplexCategory) : (coarseRowEvaluation N).app (op m) =
    coarseChainEvaluation (RowWeakEquivalences.nested N m) := rfl
example {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    (coarseRowDiagonals N).map α ≫ (coarseRowEvaluation N).app n =
      (coarseRowEvaluation N).app m ≫ (coarseWeakRowNerve N).map α := (coarseRowEvaluation N).naturality α
example : ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (coarseRowDiagonals N)|
    |TheoremA.diagonalSSet (coarseWeakRowNerve N)| := coarseRowEvaluationHomotopyEquiv N
example : (coarseRowEvaluationHomotopyEquiv N).toFun =
    (SSet.toTop.map (TheoremA.diagonalMap (coarseRowEvaluation N))).hom := rfl
example : totalCoarseEvaluation N = TheoremA.diagonalMap (coarseRowEvaluation N) ≫
    (coarseSSetIso N).hom := rfl
example : ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (coarseRowDiagonals N)|
    |sSet N.coarse.cof N.coarse.weq| := totalCoarseEvaluationHomotopyEquiv N
example : (totalCoarseEvaluationHomotopyEquiv N).toFun =
    (SSet.toTop.map (totalCoarseEvaluation N)).hom := totalCoarseEvaluationHomotopyEquiv_toFun N
example (m : SimplexCategory) : (cofRowEvaluation N).app (op m) =
    cofChainEvaluation (RowWeakEquivalences.nested N m) := rfl
example : totalCofEvaluation N = TheoremA.diagonalMap (rowDiagonalInclusion N) ≫
    totalCoarseEvaluation N := totalCofEvaluation_eq N
example (n : SimplexCategory)
    (F : ComposableArrows (FineWeakCoarseChains (RowWeakEquivalences.nested N n) n) n.len)
    (i : Fin (n.len+1)) (p : Interval n) :
    (((totalCoarseEvaluation N).app (op n) F).val.obj (i,p)) =
      ((F.obj i).obj.obj.obj i).obj.obj p := rfl
example (F : ComposableArrows (FineWeakCoarseChains (RowWeakEquivalences.nested N ⦋0⦌) ⦋0⦌) 0)
    (p : Interval ⦋0⦌) : (((totalCoarseEvaluation N).app (op ⦋0⦌) F).val.obj (0,p)) =
      ((F.obj 0).obj.obj.obj 0).obj.obj p := rfl
end Generic
section Cylinder
variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)
  (D : RowFactorization.JointData N) (hs : RowFactorization.SecondEndpointSection N D)
  [N.coarse.weq.HasTwoOutOfThreeProperty]
example : ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (cofRowDiagonals N)|
    |sSet N.coarse.cof N.coarse.weq| := totalCofEvaluationHomotopyEquiv N D hs
example : (totalCofEvaluationHomotopyEquiv N D hs).toFun =
    (SSet.toTop.map (totalCofEvaluation N)).hom := totalCofEvaluationHomotopyEquiv_toFun N D hs
end Cylinder
section Complex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [SmallCategory A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))
example : ContinuousMap.HomotopyEquiv
    |TheoremA.diagonalSSet (cofRowDiagonals (complexSubcategoryNested P))|
    |sSet (complexSubcategoryNested P).coarse.cof (complexSubcategoryNested P).coarse.weq| := by
  letI : (complexSubcategoryNested P).coarse.weq.HasTwoOutOfThreeProperty := complexSubcategory_saturated P
  exact totalCofEvaluationHomotopyEquiv (complexSubcategoryNested P) (complexJointData P hcone hshift)
    (complexJointData_secondEndpointSection P hcone hshift)
end Complex
section Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
def actualSchemeTotalCoarseEvaluation (X : Scheme.{u}) :
    ContinuousMap.HomotopyEquiv
      |TheoremA.diagonalSSet (coarseRowDiagonals (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)))|
      |sSet (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.cof
        (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.weq| :=
  totalCoarseEvaluationHomotopyEquiv (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))
#print axioms actualSchemeTotalCoarseEvaluation
end Scheme

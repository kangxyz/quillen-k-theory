import Quillen.Waldhausen.Fibration.AllWeak.RelativeInclusion
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Waldhausen.Fibration.AllWeak.RelativeInclusion
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count == 23 do throwError "Expected23 origins, got {count}"
  logInfo m!"Audited all{count} original relative-inclusion declarations."
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Categorical
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example (n : SimplexCategory) : IsExact
    (RelativeRows.waldhausenStructure (AllWeak.nested (acyclicStructure N)) n).cof
    (RelativeRows.waldhausenStructure (AllWeak.nested (acyclicStructure N)) n).weq
    (RelativeRows.waldhausenStructure N n).cof (RelativeRows.waldhausenStructure N n).weq
    (AllWeak.relativeInclusion N n) := AllWeak.relativeInclusion_exact N n
example (n : SimplexCategory)
    (X : RelativeRows.Obj (AllWeak.nested (acyclicStructure N)) n)
    (p : Interval (RelativeRows.addInitial.obj n)) :
    (((AllWeak.relativeInclusion N n).obj X).obj.obj.obj p) = (X.obj.obj.obj p).obj := rfl
example {n : SimplexCategory} {X Y : RelativeRows.Obj (AllWeak.nested (acyclicStructure N)) n}
    (f : X ⟶ Y) (p : Interval (RelativeRows.addInitial.obj n)) :
    (((AllWeak.relativeInclusion N n).map f).hom.hom.app p) = (f.hom.hom.app p).hom := rfl
example (n : SimplexCategory) : (AllWeak.relativeInclusion N n).obj
    (RelativeRows.zero (AllWeak.nested (acyclicStructure N)) n) = RelativeRows.zero N n :=
  AllWeak.relativeInclusion_zero N n
example {m n : SimplexCategory} (α : m ⟶ n) :
    AllWeak.relativeInclusion N n ⋙ RelativeRows.reindex N α =
      RelativeRows.reindex (AllWeak.nested (acyclicStructure N)) α ⋙ AllWeak.relativeInclusion N m :=
  AllWeak.relativeInclusion_reindex N α
example (n : SimplexCategory) : AllWeak.relativeInclusion N n ⋙ RelativeRows.tailFunctor N n =
    RelativeRows.tailFunctor (AllWeak.nested (acyclicStructure N)) n ⋙
      QuotientRows.postcompose (acyclicStructure (AllWeak.nested (acyclicStructure N)))
        (acyclicStructure N) (acyclicInclusion_exact (AllWeak.nested (acyclicStructure N))) n :=
  AllWeak.relativeInclusion_tail N n
example (n : SimplexCategory) : RelativeRows.fiber (AllWeak.nested (acyclicStructure N)) n ⋙
    AllWeak.relativeInclusion N n = acyclicInclusion N ⋙ RelativeRows.fiber N n :=
  AllWeak.fiber_relativeInclusion N n
end Categorical
section Simplicial
variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)
example : AllWeak.relativeInclusionSRows N ≫ RelativeRows.tailSRows N =
    RelativeRows.tailSRows (AllWeak.nested (acyclicStructure N)) ≫
      AllWeak.ordinaryRowsInclusion (acyclicStructure N) := AllWeak.relativeInclusionSRows_tail N
example : AllWeak.relativeInclusionTotal N = TheoremA.diagonalMap (AllWeak.relativeInclusionSRows N) := rfl
example : RelativeRows.totalFiberInclusion (AllWeak.nested (acyclicStructure N)) ≫
    AllWeak.relativeInclusionTotal N =
      sSetMap (acyclicInclusion_exact N) ≫ RelativeRows.totalFiberInclusion N :=
  AllWeak.totalFiberInclusion_relativeInclusion N
example {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    (RelativeRows.relativeSRows (AllWeak.nested (acyclicStructure N))).map α ≫
      (AllWeak.relativeInclusionSRows N).app n =
      (AllWeak.relativeInclusionSRows N).app m ≫ (RelativeRows.relativeSRows N).map α :=
  (AllWeak.relativeInclusionSRows N).naturality α
example : SSet.toTop.map (AllWeak.relativeInclusionTotal N)
    (RelativeRows.totalBasepoint (AllWeak.nested (acyclicStructure N))) = RelativeRows.totalBasepoint N :=
  AllWeak.relativeInclusionTotal_basepoint N
example (n : SimplexCategory) :
    (AllWeak.relativeInclusionTotal N).app (op n)
      (zeroSimplex (RelativeRows.waldhausenStructure (AllWeak.nested (acyclicStructure N)) n).cof
        (RelativeRows.waldhausenStructure (AllWeak.nested (acyclicStructure N)) n).weq
        (RelativeRows.zero (AllWeak.nested (acyclicStructure N)) n)
        (RelativeRows.isZero (AllWeak.nested (acyclicStructure N)) n) (op n)) =
      zeroSimplex (RelativeRows.waldhausenStructure N n).cof
        (RelativeRows.waldhausenStructure N n).weq (RelativeRows.zero N n)
        (RelativeRows.isZero N n) (op n) := AllWeak.relativeInclusionTotal_zeroSimplex N n
variable (he : ExtensionAxiom N.coarse) [N.coarse.weq.HasTwoOutOfThreeProperty]
example : AllWeak.relativeInclusionTotal N ≫ RelativeRows.coarseEvaluation N he =
    RelativeRows.coarseEvaluation (AllWeak.nested (acyclicStructure N))
      (AllWeak.extensionAxiom (acyclicStructure N)) ≫ sSetMap (AllWeak.acyclicInclusion_exact N) :=
  AllWeak.relativeInclusionTotal_coarseEvaluation N he
example : (RelativeRows.totalFiberInclusion (AllWeak.nested (acyclicStructure N)) ≫
    AllWeak.relativeInclusionTotal N) ≫ RelativeRows.coarseEvaluation N he =
      sSetMap (acyclicInclusion_exact N) ≫ sSetMap (changeWeak_exact N) := by
  rw [AllWeak.totalFiberInclusion_relativeInclusion, Category.assoc,
    RelativeRows.totalFiberInclusion_coarseEvaluation]
end Simplicial
section Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
example (X : Scheme.{u}) (n : SimplexCategory) :
    RelativeRows.fiber (AllWeak.nested (acyclicStructure (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)))) n ⋙
      AllWeak.relativeInclusion (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) n =
      acyclicInclusion (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) ⋙
        RelativeRows.fiber (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) n :=
  AllWeak.fiber_relativeInclusion _ n
end Scheme

section IndependentOriginalMaps
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
section Categorical
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example (n : SimplexCategory) : AllWeak.relativeInclusion N n ⋙ RelativeRows.forget N n =
    RelativeRows.forget (AllWeak.nested (acyclicStructure N)) n ⋙
      QuotientRows.postcompose (acyclicStructure N) V (acyclicInclusion_exact N)
        (RelativeRows.addInitial.obj n) := AllWeak.relativeInclusion_forget N n
example (X : AcyclicCategory N) :
    (QuotientRows.oneChain (acyclicStructure N)).flip.obj X ⋙ acyclicInclusion N =
      (QuotientRows.oneChain V).flip.obj X.obj := AllWeak.oneChain_acyclicInclusion N X
example : QuotientRows.oneEmbedding (acyclicStructure N) ⋙
    QuotientRows.postcompose (acyclicStructure N) V (acyclicInclusion_exact N) ⦋1⦌ =
      acyclicInclusion N ⋙ QuotientRows.oneEmbedding V := AllWeak.oneEmbedding_acyclicInclusion N
end Categorical
section Realized
variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)
example : SSet.toTop.map (RelativeRows.totalFiberInclusion (AllWeak.nested (acyclicStructure N))) ≫
    SSet.toTop.map (AllWeak.relativeInclusionTotal N) =
      SSet.toTop.map (sSetMap (acyclicInclusion_exact N)) ≫
        SSet.toTop.map (RelativeRows.totalFiberInclusion N) := by
  simp only [← Functor.map_comp, AllWeak.totalFiberInclusion_relativeInclusion]
example : TheoremA.diagonalMap (AllWeak.relativeInclusionSRows N) ≫
    TheoremA.diagonalMap (RelativeRows.tailSRows N) =
      TheoremA.diagonalMap (RelativeRows.tailSRows (AllWeak.nested (acyclicStructure N))) ≫
        TheoremA.diagonalMap (AllWeak.ordinaryRowsInclusion (acyclicStructure N)) := by
  ext n F : 4
  rfl
variable (he : ExtensionAxiom N.coarse) [N.coarse.weq.HasTwoOutOfThreeProperty]
example : SSet.toTop.map (AllWeak.relativeInclusionTotal N) ≫
    SSet.toTop.map (RelativeRows.coarseEvaluation N he) =
      SSet.toTop.map (RelativeRows.coarseEvaluation (AllWeak.nested (acyclicStructure N))
        (AllWeak.extensionAxiom (acyclicStructure N))) ≫
          SSet.toTop.map (sSetMap (AllWeak.acyclicInclusion_exact N)) := by
  simp only [← Functor.map_comp, AllWeak.relativeInclusionTotal_coarseEvaluation]
end Realized
end
end IndependentOriginalMaps

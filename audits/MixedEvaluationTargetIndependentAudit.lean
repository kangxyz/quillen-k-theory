import Quillen.Waldhausen.Fibration.MixedNerves.DiagonalEvaluation
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
import Quillen.Waldhausen.Fibration.MixedNerves.ChainEvaluation
import Quillen.Waldhausen.Fibration.MixedNerves.CoarseRows
import Quillen.Waldhausen.Fibration.MixedNerves.TotalEvaluation
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.MixedNerves.DiagonalEvaluation,
    `Quillen.Waldhausen.Fibration.MixedNerves.ChainEvaluation,
    `Quillen.Waldhausen.Fibration.MixedNerves.CoarseRows,
    `Quillen.Waldhausen.Fibration.MixedNerves.TotalEvaluation]
  let mut counts : Array Nat := #[0,0,0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (· + 1)
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless counts == #[33,20,40,18] do throwError "Expected111 origins, found {counts}"
  logInfo m!"FIXED111 origins: {counts}"
namespace IndependentConsumer0
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.MixedNerves
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Categorical
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
  (k : SimplexCategory)
example (F : HorizontalChains N k) (i : Fin (k.len+1)) :
    (((horizontalCoarseDiagram N k).obj F).obj i).obj = F.obj.obj.obj i := rfl
example (F : HorizontalChains N k) {i j : Fin (k.len+1)} (f : i ⟶ j) :
    (((horizontalCoarseDiagram N k).obj F).map f).hom = F.obj.obj.map f := rfl
example {F G : HorizontalChains N k} (f : F ⟶ G) (i : Fin (k.len+1)) :
    (((horizontalCoarseDiagram N k).map f).app i).hom = f.hom.hom.app i := rfl
example (F : ComposableArrows (HorizontalChains N k) k.len) (i : Fin (k.len+1)) :
    ((diagonalCoarseChain N k F).obj i).obj = (F.obj i).obj.obj.obj i := rfl
example (F : ComposableArrows (HorizontalChains N k) k.len) {i j : Fin (k.len+1)} (f : i ⟶ j) :
    ((diagonalCoarseChain N k F).map f).hom =
      (F.map f).hom.hom.app i ≫ (F.obj j).obj.obj.map f := rfl
example (F : ComposableArrows (HorizontalChains N k) k.len) {i j : Fin (k.len+1)} (f : i ⟶ j) :
    N.coarse.weq ((F.map f).hom.hom.app i ≫ (F.obj j).obj.obj.map f) :=
  diagonalCoarseChain_map_weak N k F f
example (F : ComposableArrows (HorizontalChains N ⦋0⦌) 0) :
    ((diagonalCoarseChain N ⦋0⦌ F).obj 0).obj = (F.obj 0).obj.obj.obj 0 := rfl
end Categorical
section Realization
variable {C : Type (max u v)} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example (k : SimplexCategory) (F : ComposableArrows (HorizontalChains N k) k.len) :
    (diagonalEvaluation N).app (op k) F = diagonalCoarseChain N k F := rfl
example {k l : SimplexCategoryᵒᵖ} (α : k ⟶ l) :
    (TheoremA.diagonalSSet (horizontalNerve N)).map α ≫ (diagonalEvaluation N).app l =
      (diagonalEvaluation N).app k ≫ (nerve (TrivialCofibrations.WeakCategory N.coarse.weq)).map α :=
  (diagonalEvaluation N).naturality α
example : constantHorizontalDiagonalMap N ≫ diagonalEvaluation N = 𝟙 _ := constantDiagonal_evaluation N
example : (SSet.toTop.map (diagonalEvaluation N)).hom.comp
    (SSet.toTop.map (constantHorizontalDiagonalMap N)).hom = ContinuousMap.id _ :=
  diagonalEvaluation_constant N
example : ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (horizontalNerve N)|
    (ClassifyingSpace (TrivialCofibrations.WeakCategory N.coarse.weq)) := diagonalEvaluationHomotopyEquiv N
example : (diagonalEvaluationHomotopyEquiv N).toFun =
    (SSet.toTop.map (diagonalEvaluation N)).hom := rfl
example : (diagonalEvaluationHomotopyEquiv N).invFun =
    (SSet.toTop.map (constantHorizontalDiagonalMap N)).hom := diagonalEvaluationHomotopyEquiv_invFun N
example : ((diagonalEvaluationHomotopyEquiv N).invFun.comp
    (diagonalEvaluationHomotopyEquiv N).toFun).Homotopic (ContinuousMap.id _) :=
  (diagonalEvaluationHomotopyEquiv N).left_inv
example : ((diagonalEvaluationHomotopyEquiv N).toFun.comp
    (diagonalEvaluationHomotopyEquiv N).invFun).Homotopic (ContinuousMap.id _) :=
  (diagonalEvaluationHomotopyEquiv N).right_inv
example : (constantHorizontalDiagonalMap N ≫ diagonalEvaluation N).app (op ⦋0⦌)
    ((Functor.const (Fin 1)).obj (⟨V.zero⟩ : TrivialCofibrations.WeakCategory N.coarse.weq)) =
      (Functor.const (Fin 1)).obj (⟨V.zero⟩ : TrivialCofibrations.WeakCategory N.coarse.weq) := by
  rw [constantDiagonal_evaluation]
  rfl
end Realization
section Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
example (X : Scheme.{u}) (k : SimplexCategory) :
    HorizontalChains (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) k ⥤
      ComposableArrows (TrivialCofibrations.WeakCategory
        (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.weq) k.len :=
  horizontalCoarseDiagram (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) k
def actualSchemeDiagonalEvaluation (X : Scheme.{u}) :
    ContinuousMap.HomotopyEquiv
      |TheoremA.diagonalSSet (horizontalNerve (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)))|
      (ClassifyingSpace (TrivialCofibrations.WeakCategory
        (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.weq)) :=
  diagonalEvaluationHomotopyEquiv.{u+1, u} (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))
#print axioms actualSchemeDiagonalEvaluation
end Scheme

end
end IndependentConsumer0

namespace IndependentConsumer1
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.MixedNerves
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Generic
variable {C : Type (max u v)} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example : coarseChainEvaluation N = (coarseDiagonalIso N).hom ≫ diagonalEvaluation N := rfl
example (k : SimplexCategory) (F : ComposableArrows (FineWeakCoarseChains N k) k.len)
    (i : Fin (k.len+1)) : (((coarseChainEvaluation N).app (op k) F).obj i).obj =
      (F.obj i).obj.obj.obj i := rfl
example (k : SimplexCategory) (F : ComposableArrows (FineWeakCoarseChains N k) k.len)
    {i j : Fin (k.len+1)} (f : i ⟶ j) : (((coarseChainEvaluation N).app (op k) F).map f).hom =
      (F.obj i).obj.obj.map f ≫ (F.map f).hom.hom.app j := rfl
example (k : SimplexCategory) (F : ComposableArrows (FineWeakCoarseChains N k) k.len)
    {i j : Fin (k.len+1)} (f : i ⟶ j) :
    N.coarse.weq ((F.obj i).obj.obj.map f ≫ (F.map f).hom.hom.app j) :=
  (((coarseChainEvaluation N).app (op k) F).map f).property
example : (coarseChainEvaluationHomotopyEquiv N).toFun =
    (SSet.toTop.map (coarseChainEvaluation N)).hom := coarseChainEvaluationHomotopyEquiv_toFun N
example : (coarseChainEvaluationHomotopyEquiv N).invFun =
    (SSet.toTop.map (coarseChainSection N)).hom := coarseChainEvaluationHomotopyEquiv_invFun N
example : coarseChainSection N ≫ coarseChainEvaluation N = 𝟙 _ := coarseChainSection_evaluation N
example : cofChainEvaluation N = TheoremA.diagonalMap (chainInclusion N) ≫ coarseChainEvaluation N := rfl
example (k : SimplexCategory) (F : ComposableArrows (RelativeRows.FineWeakChains N k) k.len)
    (i : Fin (k.len+1)) : (((cofChainEvaluation N).app (op k) F).obj i).obj =
      (F.obj i).obj.obj.obj i := rfl
example (F : ComposableArrows (FineWeakCoarseChains N ⦋0⦌) 0) :
    (((coarseChainEvaluation N).app (op ⦋0⦌) F).obj 0).obj = (F.obj 0).obj.obj.obj 0 := rfl
example : (coarseChainSection N ≫ coarseChainEvaluation N).app (op ⦋0⦌)
    ((Functor.const (Fin 1)).obj (⟨V.zero⟩ : TrivialCofibrations.WeakCategory N.coarse.weq)) =
      (Functor.const (Fin 1)).obj (⟨V.zero⟩ : TrivialCofibrations.WeakCategory N.coarse.weq) := by
  rw [coarseChainSection_evaluation]
  rfl
end Generic
section Natural
variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {N : NestedWeakEquivalences V} {M : NestedWeakEquivalences W}
  (F : CompatibleFunctor N M)
example (X : TrivialCofibrations.WeakCategory N.coarse.weq) :
    ((coarseWeakPostcompose F).obj X).obj = F.toFunctor.obj X.obj := rfl
example {X Y : TrivialCofibrations.WeakCategory N.coarse.weq} (f : X ⟶ Y) :
    ((coarseWeakPostcompose F).map f).hom = F.toFunctor.map f.hom := rfl
example : TheoremA.diagonalMap (horizontalNerveMap F) ≫ diagonalEvaluation M =
    diagonalEvaluation N ≫ nerveMap (coarseWeakPostcompose F) := diagonalEvaluation_naturality F
example : TheoremA.diagonalMap (coarseNerveMap F) ≫ coarseChainEvaluation M =
    coarseChainEvaluation N ≫ nerveMap (coarseWeakPostcompose F) := coarseChainEvaluation_naturality F
example : TheoremA.diagonalMap (cofNerveMap F) ≫ cofChainEvaluation M =
    cofChainEvaluation N ≫ nerveMap (coarseWeakPostcompose F) := cofChainEvaluation_naturality F
end Natural
section Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
def actualSchemeCoarseChainEvaluation (X : Scheme.{u}) :
    ContinuousMap.HomotopyEquiv
      |TheoremA.diagonalSSet (coarseChainNerve (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)))|
      (ClassifyingSpace (TrivialCofibrations.WeakCategory
        (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.weq)) :=
  coarseChainEvaluationHomotopyEquiv.{u+1,u} (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))
#print axioms actualSchemeCoarseChainEvaluation
end Scheme

end
end IndependentConsumer1

namespace IndependentConsumer2
noncomputable section
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.Fibration.MixedNerves

open CategoryTheory Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.MixedNerves
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
  (n k : SimplexCategory)
example (F : Interval n ⥤ C) : QuotientRows.IsRow V F ↔ QuotientRows.IsRow N.coarse F := isRow_coarse_iff N F
example (F : QuotientRows.Obj V n) : ((coarseRowView N n).obj F).obj = F.obj := rfl
example (F : QuotientRows.Obj N.coarse n) : ((fineRowView N n).obj F).obj = F.obj := rfl
example {F G : QuotientRows.Obj V n} (f : F ⟶ G) : ((coarseRowView N n).map f).hom = f.hom := rfl
example {F G : QuotientRows.Obj N.coarse n} (f : F ⟶ G) : ((fineRowView N n).map f).hom = f.hom := rfl
example : coarseRowView N n ⋙ fineRowView N n = 𝟭 _ := coarseRowView_fineRowView N n
example : fineRowView N n ⋙ coarseRowView N n = 𝟭 _ := fineRowView_coarseRowView N n
example : coarseWeakRows N n ≌ QuotientRows.WeakRows N.coarse n := coarseWeakRowsEquivalence N n
example : (coarseWeakRowsEquivalence N n).functor = coarseWeakRowsToStandard N n := rfl
example : (coarseWeakRowsEquivalence N n).inverse = standardToCoarseWeakRows N n := rfl
example (X : coarseWeakRows N n) : ((coarseWeakRowsToStandard N n).obj X).obj.obj = X.obj.obj := rfl
example {X Y : coarseWeakRows N n} (f : X ⟶ Y) (p : Interval n) :
    ((coarseWeakRowsToStandard N n).map f).hom.hom.app p = f.hom.hom.app p := rfl
example {m : SimplexCategory} (α : m ⟶ n) : coarseWeakRowsReindex N α =
    widePostcompose (rowReindexCompatible N α).toFunctor _ _ (rowReindexCompatible N α).coarse := rfl
example {m : SimplexCategory} (α : m ⟶ n) :
    coarseWeakRowsReindex N α ⋙ coarseWeakRowsToStandard N m =
      coarseWeakRowsToStandard N n ⋙ QuotientRows.weakRowsReindex N.coarse α :=
  coarseWeakRowsToStandard_reindex N α
example : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := coarseWeakRowNerve N
example : coarseWeakRowNerve N ≅ QuotientRows.weakRowNerve N.coarse := coarseWeakRowNerveIso N
example (F : ComposableArrows (coarseWeakRows N n) k.len) (t : Fin (k.len+1)) (p : Interval n) :
    (((((coarseWeakRowNerveIso N).hom.app (op n)).app (op k) F).obj t).obj.obj.obj p) =
      (F.obj t).obj.obj.obj p := rfl
example (F : ComposableArrows (QuotientRows.WeakRows N.coarse n) k.len)
    {i j : Fin (k.len+1)} (f : i ⟶ j) (p : Interval n) :
    (((((coarseWeakRowNerveIso N).inv.app (op n)).app (op k) F).map f).hom.hom.app p) =
      (F.map f).hom.hom.app p := rfl
example : TheoremA.diagonalSSet (coarseWeakRowNerve N) ≅ sSet N.coarse.cof N.coarse.weq := coarseSSetIso N
example (F : ComposableArrows (coarseWeakRows N n) n.len) :
    ((coarseSSetIso N).hom.app (op n) F).val =
      QuotientRows.weakChainToGrid N.coarse (F ⋙ coarseWeakRowsToStandard N n) := rfl
example (F : ComposableArrows (coarseWeakRows N n) n.len) {a b : Grid n} (f : a ⟶ b) :
    ((coarseSSetIso N).hom.app (op n) F).val.map f =
      (QuotientRows.weakChainToGrid N.coarse (F ⋙ coarseWeakRowsToStandard N n)).map f := rfl
example (F : (sSet N.coarse.cof N.coarse.weq).obj (op n)) (t : Fin (n.len+1)) (p : Interval n) :
    ((((coarseSSetIso N).inv.app (op n) F).obj t).obj.obj.obj p) = F.val.obj (t,p) := rfl
example (F : ComposableArrows (coarseWeakRows N (SimplexCategory.mk 0)) 0) :
    (((coarseSSetIso N).hom.app (op (SimplexCategory.mk 0)) F).val.obj
      (0, interval 0 0 le_rfl)) = (F.obj 0).obj.obj.obj (interval 0 0 le_rfl) := rfl
end Quillen.Waldhausen.Fibration.MixedNerves

end
end IndependentConsumer2

namespace IndependentConsumer3
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

end
end IndependentConsumer3

noncomputable section
open CategoryTheory Opposite Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open MixedNerves
open scoped Simplicial Topology
universe u
variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)
example (n : SimplexCategory)
    (F : ComposableArrows (RelativeRows.FineWeakChains (RowWeakEquivalences.nested N n) n) n.len)
    (i : Fin (n.len+1)) (p : Interval n) :
    (((totalCofEvaluation N).app (op n) F).val.obj (i,p)) =
      ((F.obj i).obj.obj.obj i).obj.obj p := rfl
example : (totalCoarseEvaluationHomotopyEquiv N).invFun.comp
    (SSet.toTop.map (totalCoarseEvaluation N)).hom |>.Homotopic (.id _) := by
  rw [← totalCoarseEvaluationHomotopyEquiv_toFun]
  exact (totalCoarseEvaluationHomotopyEquiv N).left_inv
example (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D)
    [N.coarse.weq.HasTwoOutOfThreeProperty] :
    (SSet.toTop.map (totalCofEvaluation N)).hom.Homotopic
      (totalCofEvaluationHomotopyEquiv N D hs).toFun := by
  rw [totalCofEvaluationHomotopyEquiv_toFun]
example (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D)
    [N.coarse.weq.HasTwoOutOfThreeProperty] :
    ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (cofRowDiagonals N)|
      |sSet N.coarse.cof N.coarse.weq| := totalCofEvaluationHomotopyEquiv N D hs
end

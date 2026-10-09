import Quillen.Waldhausen.Fibration.MixedNerves.TotalRealization
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.MixedNerves.Postcompose,
    `Quillen.Waldhausen.Fibration.MixedNerves.PostcomposeNerves,
    `Quillen.Waldhausen.Fibration.MixedNerves.RowPostcompose,
    `Quillen.Waldhausen.Fibration.MixedNerves.TotalRealization]
  let mut counts : Array Nat := targets.map (fun _ ↦ 0)
  let mut total : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[idx.toNat]!
    let some i := targets.findIdx? (· == origin) | continue
    counts := counts.modify i (· + 1)
    total := total + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "{origin}: {name} depends on unsupported {ax}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing origin {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless total == 118 && counts == #[57, 22, 29, 10] do
    throwError "Expected fixed118 origins (57+22+29+10), found {total}: {counts}"
  logInfo m!"TOTAL_ORIGINS {total}: {counts}"
noncomputable section
open CategoryTheory Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.MixedNerves
open RelativeRows
section Generic
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {V : Structure C} {W : Structure D} {U : Structure E}
  {N : NestedWeakEquivalences V} {M : NestedWeakEquivalences W} {L : NestedWeakEquivalences U}
  (F : CompatibleFunctor N M) (G : CompatibleFunctor M L) (n k : SimplexCategory)
example : (CompatibleFunctor.id N).toFunctor = 𝟭 C := rfl
example : (F.comp G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl
example (X : FineChain V k) : ((finePostcompose F k).obj X).obj = X.obj ⋙ F.toFunctor := rfl
example {X Y : FineChain V k} (f : X ⟶ Y) (i : Fin (k.len+1)) :
    ((finePostcompose F k).map f).hom.app i = F.toFunctor.map (f.hom.app i) := rfl
example (X : CoarseWeakChain N n) : ((coarsePostcompose F n).obj X).obj = X.obj ⋙ F.toFunctor := rfl
example (X : CofibrationWeakChain N n) : ((cofPostcompose F n).obj X).obj = X.obj ⋙ F.toFunctor := rfl
example (X : CofibrationWeakChain N n) {i j : Fin (n.len+1)} (f : i ⟶ j) :
    W.cof (F.toFunctor.map (X.obj.map f)) := ((cofPostcompose F n).obj X).property.1 f
example (X : FineWeakCoarseChains N n) :
    ((fineWeakCoarsePostcompose F n).obj X).obj.obj = X.obj.obj ⋙ F.toFunctor := rfl
example {X Y : FineWeakCoarseChains N n} (f : X ⟶ Y) (i : Fin (n.len+1)) :
    ((fineWeakCoarsePostcompose F n).map f).hom.hom.app i = F.toFunctor.map (f.hom.hom.app i) := rfl
example {X Y : HorizontalCofChains N k} (f : X ⟶ Y) (i : Fin (k.len+1)) :
    ((horizontalCofPostcompose F k).map f).hom.hom.app i = F.toFunctor.map (f.hom.hom.app i) := rfl
example : coarseChainNerve N ⟶ coarseChainNerve M := coarseNerveMap F
example : cofChainNerve N ⟶ cofChainNerve M := cofNerveMap F
example : horizontalNerve N ⟶ horizontalNerve M := horizontalNerveMap F
example : horizontalCofNerve N ⟶ horizontalCofNerve M := horizontalCofNerveMap F
example : coarseNerveMap (F.comp G) = coarseNerveMap F ≫ coarseNerveMap G := coarseNerveMap_comp F G
example : cofNerveMap (F.comp G) = cofNerveMap F ≫ cofNerveMap G := cofNerveMap_comp F G
example : horizontalNerveMap (F.comp G) = horizontalNerveMap F ≫ horizontalNerveMap G := horizontalNerveMap_comp F G
example : horizontalCofNerveMap (F.comp G) = horizontalCofNerveMap F ≫ horizontalCofNerveMap G :=
  horizontalCofNerveMap_comp F G
example : chainInclusion N ≫ coarseNerveMap F = cofNerveMap F ≫ chainInclusion M := chainInclusion_naturality F
example : (flipFunctor _ _ _).map (coarseNerveMap F) ≫ (coarseTransposeIso M).hom =
    (coarseTransposeIso N).hom ≫ horizontalNerveMap F := coarseTransposeIso_naturality F
example : TheoremA.diagonalMap (cofNerveMap F) ≫ (cofDiagonalIso M).hom =
    (cofDiagonalIso N).hom ≫ TheoremA.diagonalMap (horizontalCofNerveMap F) := cofDiagonalIso_naturality F
example (X : ComposableArrows (FineWeakCoarseChains N n) k.len) (i : Fin (n.len+1)) (j : Fin (k.len+1)) :
    (((((coarseNerveMap F).app (op n)).app (op k) X).obj j).obj.obj.obj i) =
      F.toFunctor.obj ((X.obj j).obj.obj.obj i) := rfl
example (X : ComposableArrows (FineWeakChains N (SimplexCategory.mk 0)) 0) :
    (((((cofNerveMap F).app (op (SimplexCategory.mk 0))).app (op (SimplexCategory.mk 0)) X).obj 0).obj.obj.obj 0) =
      F.toFunctor.obj ((X.obj 0).obj.obj.obj 0) := rfl
end Generic
section Rows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
example : SimplexCategoryᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{max u v}) := coarseRowNerves N
example : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := cofRowDiagonals N
example {m n : SimplexCategory} (α : m ⟶ n) :
    (rowReindexCompatible N α).toFunctor = QuotientRows.reindex V α := rfl
example {m n : SimplexCategory} (α : m ⟶ n) {X Y : QuotientRows.Obj V n} (f : X ⟶ Y)
    (h : QuotientRows.cof V n f) : QuotientRows.cof V m ((QuotientRows.reindex V α).map f) :=
  (rowReindexCompatible N α).cof f h
example {m n : SimplexCategory} (α : m ⟶ n) {X Y : QuotientRows.Obj V n} (f : X ⟶ Y)
    (h : ∀ p, N.coarse.weq (f.hom.app p)) :
    ∀ p, N.coarse.weq (((QuotientRows.reindex V α).map f).hom.app p) :=
  (rowReindexCompatible N α).coarse f h
example {m m' : SimplexCategory} (α : m' ⟶ m) (n k : SimplexCategory)
    (X : ComposableArrows (FineWeakCoarseChains (RowWeakEquivalences.nested N m) n) k.len)
    (i : Fin (n.len+1)) (j : Fin (k.len+1)) :
    ((((((coarseRowNerves N).map α.op).app (op n)).app (op k) X).obj j).obj.obj.obj i) =
      (QuotientRows.reindex V α).obj ((X.obj j).obj.obj.obj i) := rfl
example {m m' : SimplexCategory} (α : m' ⟶ m) (n k : SimplexCategory)
    (X : ComposableArrows (FineWeakChains (RowWeakEquivalences.nested N m) n) k.len)
    (i : Fin (n.len+1)) {j l : Fin (k.len+1)} (f : j ⟶ l) :
    ((((((cofRowNerves N).map α.op).app (op n)).app (op k) X).map f).hom.hom.app i) =
      (QuotientRows.reindex V α).map ((X.map f).hom.hom.app i) := rfl
example (m : SimplexCategory) : (rowDiagonalInclusion N).app (op m) =
    TheoremA.diagonalMap (chainInclusion (RowWeakEquivalences.nested N m)) := rfl
example {l m n : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n) :
    rowReindexCompatible N (α ≫ β) = (rowReindexCompatible N β).comp (rowReindexCompatible N α) :=
  rowReindexCompatible_comp N α β
end Rows


section Total
open scoped Simplicial Topology
variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)
  (D : RowFactorization.JointData N) (hs : RowFactorization.SecondEndpointSection N D)
  [N.coarse.weq.HasTwoOutOfThreeProperty]
example : ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (cofRowDiagonals N)|
    |TheoremA.diagonalSSet (coarseRowDiagonals N)| := totalChainInclusionRealizationHomotopyEquiv N D hs
example : (totalChainInclusionRealizationHomotopyEquiv N D hs).toFun =
    (SSet.toTop.map (TheoremA.diagonalMap (rowDiagonalInclusion N))).hom := rfl
example (m : SimplexCategory) : (rowDiagonalInclusion N).app (op m) =
    TheoremA.diagonalMap (chainInclusion (RowWeakEquivalences.nested N m)) := rfl
example (X : (TheoremA.diagonalSSet (cofRowDiagonals N)).obj (op (SimplexCategory.mk 0))) :
    (TheoremA.diagonalMap (rowDiagonalInclusion N)).app (op (SimplexCategory.mk 0)) X =
      ((chainInclusion (RowWeakEquivalences.nested N (SimplexCategory.mk 0))).app
        (op (SimplexCategory.mk 0))).app (op (SimplexCategory.mk 0)) X := rfl
example (n : SimplexCategory)
    (X : (TheoremA.diagonalSSet (cofRowDiagonals N)).obj (op n))
    (i j : Fin (n.len+1)) (p : Interval n) :
    (((((TheoremA.diagonalMap (rowDiagonalInclusion N)).app (op n) X).obj i).obj.obj.obj j).obj.obj p) =
      (((X.obj i).obj.obj.obj j).obj.obj p) := rfl
example {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    (cofRowDiagonals N).map α ≫ (rowDiagonalInclusion N).app n =
      (rowDiagonalInclusion N).app m ≫ (coarseRowDiagonals N).map α :=
  (rowDiagonalInclusion N).naturality α
example {m n : SimplexCategory} (α : m ⟶ n) :
    TheoremA.diagonalMap (coarseNerveMap (rowReindexCompatible N α)) ≫
      (coarseDiagonalIso (RowWeakEquivalences.nested N m)).hom =
        (coarseDiagonalIso (RowWeakEquivalences.nested N n)).hom ≫
          TheoremA.diagonalMap (horizontalNerveMap (rowReindexCompatible N α)) :=
  coarseDiagonalIso_naturality (rowReindexCompatible N α)
end Total
section ConcreteTotal
open CochainComplex GilletWaldhausen
open scoped Simplicial Topology
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [SmallCategory A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example : (complexTotalChainInclusionRealizationHomotopyEquiv
    (boundedTerms P) (boundedTerms_mappingCone P) (fun _ h ↦ boundedTerms_shift P h 1)).toFun =
    (SSet.toTop.map (TheoremA.diagonalMap (rowDiagonalInclusion
      (complexSubcategoryNested (boundedTerms P))))).hom := rfl
end ConcreteTotal
end Quillen.Waldhausen.Fibration.MixedNerves

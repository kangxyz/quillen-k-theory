import Lean.Util.CollectAxioms
import Quillen.Waldhausen.Additivity.RealizedAdditivity
import Quillen.Waldhausen.GilletWaldhausen.TruncationCofibrationSequence

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[
    `Quillen.Waldhausen.Additivity.CofiberEndpoint,
    `Quillen.Waldhausen.Additivity.CofibrationSequence,
    `Quillen.Waldhausen.Additivity.CoproductAlgebra,
    `Quillen.Waldhausen.Additivity.DeformationMap,
    `Quillen.Waldhausen.Additivity.EndpointFamilies,
    `Quillen.Waldhausen.Additivity.EndpointHomotopies,
    `Quillen.Waldhausen.Additivity.EndpointNaturality,
    `Quillen.Waldhausen.Additivity.IntervalArrows,
    `Quillen.Waldhausen.Additivity.IntervalEndpoints,
    `Quillen.Waldhausen.Additivity.MixedDiagrams,
    `Quillen.Waldhausen.Additivity.PushoutCofibrations,
    `Quillen.Waldhausen.Additivity.PushoutEndpoints,
    `Quillen.Waldhausen.Additivity.PushoutFunctor,
    `Quillen.Waldhausen.Additivity.PushoutInterchange,
    `Quillen.Waldhausen.Additivity.PushoutPreservation,
    `Quillen.Waldhausen.Additivity.RealizationHomotopy,
    `Quillen.Waldhausen.Additivity.RealizedAdditivity,
    `Quillen.Waldhausen.Additivity.SplitSequence,
    `Quillen.Waldhausen.Additivity.SumDiagrams,
    `Quillen.Waldhausen.Additivity.ZeroFactorization,
    `Quillen.Topology.Realization.MixedOrdinal,
    `Quillen.Topology.Realization.MixedOrdinalEndpoints,
    `Quillen.Topology.Realization.MixedOrdinalCylinder,
    `Quillen.Topology.Realization.MixedOrdinalFunctor,
    `Quillen.Topology.Realization.MixedOrdinalContraction,
    `Quillen.Topology.Realization.MixedOrdinalBisimplicial,
    `Quillen.Topology.Realization.MixedOrdinalRealization,
    `Quillen.Waldhausen.SConstruction.NerveCylinder,
    `Quillen.Waldhausen.SConstruction.NerveCylinderNaturality,
    `Quillen.Waldhausen.SConstruction.WeakGridHomotopy]
  let mut count : Nat := 0
  let mut modules : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    modules := modules.insert origin
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless count == 457 do
    throwError "Expected 457 complete additivity origins, found {count}"
  unless modules.size == wanted.size do
    throwError "Expected {wanted.size} defining modules, found {modules.size}"
  logInfo m!"Audited all {count} declarations across {modules.size} frozen additivity/topology/helper modules."

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
open Quillen.Waldhausen.Additivity
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
  {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

example : (deloopingMap hs.exactG).hom.Homotopic
    (deloopingMap (sumFunctor_isExact V W hs.exactH hs.exactF)).hom :=
  deloopingMap_additivity V W a b hs

example : (deloopingMap hs.exactG).hom.Homotopy
    (deloopingMap (sumFunctor_isExact V W hs.exactH hs.exactF)).hom :=
  additivityHomotopy V W a b hs

namespace ActualTruncationConsumer
open GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]
  [(abelianExactStructure A).IsExtensionClosed P]

def truncationAdditivityHomotopy (n : ℤ) := by
  let V := ofExactCategory (boundedAcyclicExactStructure P)
  letI := hasBinaryCoproducts V
  exact additivityHomotopy V V (boundedAcyclicTruncationInclusion P n)
    (boundedAcyclicTruncationProjection P n) (boundedAcyclicTruncation_isCofibrationSequence P n)

end ActualTruncationConsumer

end
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.MixedOrdinalCylinder
example (n : SimplexCategory) (φ : Cut n) (i : Fin (n.len + 1)) :
    (firstIndex φ).toOrderHom i ≤ (switchedIndex φ).toOrderHom i := firstIndex_le_switchedIndex φ i
example {n m : SimplexCategory} (α : n ⟶ m) (φ : Cut m) :
    switchedIndex (α ≫ φ) ≫ mixedMap α (fun _ ↦ le_rfl) = α ≫ switchedIndex φ :=
  switchedIndex_naturality α φ
example (n : SimplexCategory) : mixedOrdinal (zeroCut n) ≅ n := zeroIso n
example (n : SimplexCategory) : mixedOrdinal (oneCut n) ≅ OrdinalSubdivision.δ.obj n := oneIso n
example (n : SimplexCategory) : (zeroIso n).inv = firstIndex (zeroCut n) := rfl
example (n : SimplexCategory) : (oneIso n).hom = inclusion (oneCut n) := rfl
example (n : SimplexCategory) (i j : Fin (n.len + 1)) :
    (firstIndex (oneCut n)).toOrderHom i ≤ (switchedIndex (oneCut n)).toOrderHom j :=
  firstIndex_one_le_switchedIndex n i j
example (X : SSet.{u}) : zeroSection X ≫ projection X = 𝟙 X := zeroSection_projection X
example (X : SSet.{u}) : oneSection X ≫ projection X = OrdinalSubdivision.endpoint X := oneSection_projection X
example (X : SSet.{u}) : SSet.Homotopy (projection X ≫ zeroSection X) (𝟙 _) := contraction X
example (X : SSet.{u}) : (projectionRealizationHomotopyEquiv X).toFun =
    (SSet.toTop.map (projection X)).hom := rfl
example (X : SSet.{u}) : (oneSectionRealizationHomotopyEquiv X).toFun =
    (SSet.toTop.map (oneSection X)).hom := rfl
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n m : SimplexCategoryᵒᵖ) :
    ((outerCylinder X).obj n).obj m =
      (Σ φ : Cut n.unop, (X.obj (op (mixedOrdinal φ))).obj m) := rfl
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : outerZeroSection X ≫ outerProjection X = 𝟙 X :=
  outerZeroSection_projection X
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    outerOneSection X ≫ outerProjection X = OrdinalSubdivision.horizontalEndpoint X :=
  outerOneSection_projection X
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    SSet.Homotopy (TheoremA.diagonalMap (outerProjection X) ≫
      TheoremA.diagonalMap (outerZeroSection X)) (𝟙 _) := outerContraction X
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (outerProjectionRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap (outerProjection X))).hom := rfl
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (outerOneSectionRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap (outerOneSection X))).hom := rfl
end Quillen.MixedOrdinalCylinder

end
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
open Quillen Quillen.Waldhausen
universe u v
variable {D : Type u} [Category.{v} D] (W : Structure D)

section Cylinder
variable {n m : SimplexCategory} {A B : Grid₂ n m ⥤ D} (η : A ⟶ B)
  (hη : ∀ p, W.weq (η.app p)) (hA : IsSimplex₂ W.cof W.weq A)
  (hB : IsSimplex₂ W.cof W.weq B)
example (τ : m ⟶ ⦋1⦌) : IsSimplex₂ W.cof W.weq (nerveCylinderDiagram η τ) :=
  nerveCylinderDiagram_isSimplex₂ W η hη hA hB τ
example : nerveCylinderDiagram η (SimplexCategory.const m ⦋1⦌ 0) = A :=
  nerveCylinderDiagram_zero η
example : nerveCylinderDiagram η (SimplexCategory.const m ⦋1⦌ 1) = B :=
  nerveCylinderDiagram_one η
example {n' m' : SimplexCategory} (α : n' ⟶ n) (β : m' ⟶ m) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (whiskerLeft (gridMap₂ α β) η) (β ≫ τ) =
      gridMap₂ α β ⋙ nerveCylinderDiagram η τ := nerveCylinderDiagram_precomp η α β τ
end Cylinder

section Family
variable {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f g : X ⟶ bisimplicialSSet W)
  (η : ∀ n m (x : (X.obj n).obj m), (((f.app n).app m) x).1 ⟶ (((g.app n).app m) x).1)
  (hη : ∀ n m x p, W.weq ((η n m x).app p))
  (hcompat : ∀ {n n'} (α : n ⟶ n') (x : (TheoremA.diagonalSSet X).obj n)
    (p : Grid₂ n'.unop n'.unop),
    HEq ((η n' n' ((TheoremA.diagonalSSet X).map α x)).app p)
      ((η n n x).app ((gridMap₂ α.unop α.unop).obj p)))
example : SSet.Homotopy (TheoremA.diagonalMap f) (TheoremA.diagonalMap g) :=
  diagonalWeakGridHomotopy W f g η hη hcompat
example : (SSet.toTop.map (TheoremA.diagonalMap f)).hom.Homotopy
    (SSet.toTop.map (TheoremA.diagonalMap g)).hom :=
  diagonalWeakGridRealizationHomotopy W f g η hη hcompat
example (n : SimplexCategoryᵒᵖ)
    (z : (TheoremA.diagonalSSet X ⊗ Δ[1]).obj n) :
    ((diagonalWeakGridHomotopy W f g η hη hcompat).h.app n z).1 =
      nerveCylinderDiagram (η n n z.1) z.2.down := rfl
end Family

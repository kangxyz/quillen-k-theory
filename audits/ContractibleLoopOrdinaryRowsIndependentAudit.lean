import Quillen.Topology.HomotopyFiber.ContractibleSource
import Quillen.Waldhausen.Fibration.AllWeak.RelativeContractible
import Lean.Util.CollectAxioms
import Quillen.Waldhausen.Fibration.AllWeak.OrdinaryRows
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.HomotopyFiber.ContractibleSource,
    `Quillen.Waldhausen.Fibration.AllWeak.OrdinaryRows]
  let mut counts : Array Nat := #[0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (· + 1)
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless counts == #[25,17] do throwError "Expected42 origins, found {counts}"
  logInfo m!"FIXED42: {counts}"
namespace IndependentLoopRows0
noncomputable section

open Quillen Quillen.HomotopyFiber
open scoped Topology unitInterval Simplicial
universe u v
section Generic
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ContractibleSpace X] (f : C(X,Y)) (y : Y) (x : X) (h : f x = y)
example : (ContinuousMap.id X).Homotopy (ContinuousMap.const X x) := contractibleSourceContraction x
example : (sourcePointEquiv x).toFun = ContinuousMap.const Unit x := rfl
example : (sourcePointEquiv x).invFun = ContinuousMap.const X () := rfl
example : HomotopyFiber (f.comp (ContinuousMap.const Unit x)) y ≃ₜ Path y y :=
  pointSourceFiberHomeomorph f y x h
example (γ : Path y y) : ((pointSourceFiberHomeomorph f y x h).symm γ).1.2 =
    γ.toContinuousMap := rfl
example : (loopInclusionEquivOfContractibleSource f y x h).toFun = loopInclusion f y x h :=
  loopInclusionEquivOfContractibleSource_toFun f y x h
example (γ : Path y y) : ((loopInclusionEquivOfContractibleSource f y x h) γ).1.1 = x := rfl
example (γ : Path y y) : ((loopInclusionEquivOfContractibleSource f y x h) γ).1.2 =
    γ.toContinuousMap := rfl
example : loopInclusionEquivOfContractibleSource f y x h (Path.refl y) =
    basepoint f y x h := rfl
example : Function.Bijective (homotopyGroupMap (N := Fin 0) (loopInclusion f y x h)
    (x := Path.refl y) (y := basepoint f y x h) rfl) :=
  loopInclusion_bijective_of_contractibleSource f y x h 0
example (n : ℕ) : Function.Bijective (homotopyGroupMap (N := Fin n) (loopInclusion f y x h)
    (x := Path.refl y) (y := basepoint f y x h) rfl) :=
  loopInclusion_bijective_of_contractibleSource f y x h n
end Generic
section ActualRelative
open CategoryTheory Waldhausen Waldhausen.Fibration
variable {C : Type u} [SmallCategory C] (W : Structure C)
example : let f := (SSet.toTop.map (TheoremA.diagonalMap (RelativeRows.tailSRows (AllWeak.nested W)))).hom
    let x := RelativeRows.totalBasepoint (AllWeak.nested W)
    ContinuousMap.HomotopyEquiv (Path (f x) (f x)) (HomotopyFiber f (f x)) :=
  loopInclusionEquivOfContractibleSource _ _ _ rfl
example : let f := (SSet.toTop.map (TheoremA.diagonalMap (RelativeRows.tailSRows (AllWeak.nested W)))).hom
    let x := RelativeRows.totalBasepoint (AllWeak.nested W)
    (loopInclusionEquivOfContractibleSource f (f x) x rfl).toFun = loopInclusion f (f x) x rfl :=
  loopInclusionEquivOfContractibleSource_toFun _ _ _ rfl
end ActualRelative

end
end IndependentLoopRows0

namespace IndependentLoopRows1
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Simplicial
universe u
variable {C : Type u} [SmallCategory C] (W : Structure C)
example : RelativeRows.ordinarySRows (acyclicStructure (AllWeak.nested W)) ≅
    RelativeRows.ordinarySRows W := AllWeak.ordinaryRowsIso W
example : (AllWeak.ordinaryRowsIso W).hom = AllWeak.ordinaryRowsInclusion W := rfl
example : (AllWeak.ordinaryRowsIso W).inv = AllWeak.ordinaryRowsLift W := rfl
example : AllWeak.ordinaryRowsInclusion W ≫ AllWeak.ordinaryRowsLift W = 𝟙 _ :=
  (AllWeak.ordinaryRowsIso W).hom_inv_id
example : AllWeak.ordinaryRowsLift W ≫ AllWeak.ordinaryRowsInclusion W = 𝟙 _ :=
  (AllWeak.ordinaryRowsIso W).inv_hom_id
example {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    (RelativeRows.ordinarySRows (acyclicStructure (AllWeak.nested W))).map α ≫
      (AllWeak.ordinaryRowsInclusion W).app n =
      (AllWeak.ordinaryRowsInclusion W).app m ≫ (RelativeRows.ordinarySRows W).map α :=
  (AllWeak.ordinaryRowsInclusion W).naturality α
example {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    (RelativeRows.ordinarySRows W).map α ≫ (AllWeak.ordinaryRowsLift W).app n =
      (AllWeak.ordinaryRowsLift W).app m ≫
        (RelativeRows.ordinarySRows (acyclicStructure (AllWeak.nested W))).map α :=
  (AllWeak.ordinaryRowsLift W).naturality α
example (n k : SimplexCategory)
    (F : ((RelativeRows.ordinarySRows (acyclicStructure (AllWeak.nested W))).obj (op n)).obj (op k))
    {a b : Grid k} (f : a ⟶ b) (p : Interval n) :
    (((((AllWeak.ordinaryRowsInclusion W).app (op n)).app (op k) F).val.map f).hom.app p) =
      ((F.val.map f).hom.app p).hom := rfl
example (n k : SimplexCategory)
    (F : ((RelativeRows.ordinarySRows W).obj (op n)).obj (op k))
    {a b : Grid k} (f : a ⟶ b) (p : Interval n) :
    ((((((AllWeak.ordinaryRowsLift W).app (op n)).app (op k) F).val.map f).hom.app p).hom) =
      (F.val.map f).hom.app p := rfl
example (n k : SimplexCategory) :
    (((AllWeak.ordinaryRowsInclusion W).app (op n)).app (op k)
      (zeroSimplex (QuotientRows.waldhausenStructure (acyclicStructure (AllWeak.nested W)) n).cof
        (QuotientRows.waldhausenStructure (acyclicStructure (AllWeak.nested W)) n).weq
        (QuotientRows.zero (acyclicStructure (AllWeak.nested W)) n)
        (QuotientRows.isZero (acyclicStructure (AllWeak.nested W)) n) (op k))) =
      zeroSimplex (QuotientRows.waldhausenStructure W n).cof
        (QuotientRows.waldhausenStructure W n).weq
        (QuotientRows.zero W n) (QuotientRows.isZero W n) (op k) :=
  AllWeak.ordinaryRowsInclusion_zero W n k
example : (AllWeak.ordinaryDiagonalIso W).hom =
    TheoremA.diagonalMap (AllWeak.ordinaryRowsInclusion W) := rfl
example (F : ((RelativeRows.ordinarySRows (acyclicStructure (AllWeak.nested W))).obj (op ⦋0⦌)).obj (op ⦋0⦌))
    (p : Interval ⦋0⦌) :
    (((((AllWeak.ordinaryRowsInclusion W).app (op ⦋0⦌)).app (op ⦋0⦌) F).val.obj
      (grid 0 0 0 le_rfl)).obj.obj p) = ((F.val.obj (grid 0 0 0 le_rfl)).obj.obj p).obj := rfl

end
end IndependentLoopRows1

noncomputable section
open CategoryTheory Opposite Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u v
section Loops
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ContractibleSpace X] (f : C(X,Y)) (y : Y) (x : X) (h : f x = y)
example (γ : Path y y) : ((HomotopyFiber.pointSourceFiberHomeomorph f y x h).symm γ).1.1 = () := rfl
example : (HomotopyFiber.loopInclusionEquivOfContractibleSource f y x h).invFun.comp
    (HomotopyFiber.loopInclusion f y x h) |>.Homotopic (.id _) := by
  rw [← HomotopyFiber.loopInclusionEquivOfContractibleSource_toFun]
  exact (HomotopyFiber.loopInclusionEquivOfContractibleSource f y x h).left_inv
end Loops
section Rows
variable {C : Type u} [SmallCategory C] (W : Structure C)
example : (AllWeak.ordinaryDiagonalIso W).hom ≫ (AllWeak.ordinaryDiagonalIso W).inv = 𝟙 _ :=
  (AllWeak.ordinaryDiagonalIso W).hom_inv_id
example (n : SimplexCategory)
    (F : (TheoremA.diagonalSSet (RelativeRows.ordinarySRows (acyclicStructure (AllWeak.nested W)))).obj (op n))
    (q : Grid n) (p : Interval n) :
    (((((AllWeak.ordinaryDiagonalIso W).hom.app (op n) F).val.obj q).obj.obj p)) =
      ((F.val.obj q).obj.obj p).obj := rfl
end Rows
end

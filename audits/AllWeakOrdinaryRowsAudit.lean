import Quillen.Waldhausen.Fibration.AllWeak.OrdinaryRows
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Waldhausen.Fibration.AllWeak.OrdinaryRows
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
  unless count == 17 do throwError "Expected17 origins, got {count}"
  logInfo m!"Audited all{count} original all-weak ordinary-row declarations."
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

import Quillen.Waldhausen.Fibration.RelativeRows.ProductSection
import Lean.Util.CollectAxioms
noncomputable section
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless #[`Quillen.Waldhausen.Fibration.RelativeRows.TailQuotient,
      `Quillen.Waldhausen.Fibration.RelativeRows.ProductSection].contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 26 do
    throwError "Expected 26 actual relative quotient/section origins, found {count}"
  logInfo m!"Audited {count} actual relative quotient/section origins; only standard3."

universe u v
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
open Quillen.Waldhausen.Fibration Quillen.Waldhausen.Fibration.RelativeRows
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (n : SimplexCategory)

-- Independent universes, only genuine nested weak-equivalence structure.
example : Additivity.IsCofibrationSequence (waldhausenStructure N n) (waldhausenStructure N n)
    (cutToId N n) (tailProjection N n) := cut_tail_isCofibrationSequence N n
example : tailQuotientFunctor N n = tailFunctor N n ⋙ tailSection N n := rfl
example (X : Obj N n) (p : Interval (addInitial.obj n)) :
    (((tailProjection N n).app X).hom.hom.app p) = X.obj.obj.map ((idToRaiseIndex n).app p) := rfl
example (X : Obj N n) : IsPushout ((cutToId N n).app X)
    ((isZero N n).from_ ((cutFunctor N n).obj X))
    ((tailProjection N n).app X) ((isZero N n).to_ ((tailQuotientFunctor N n).obj X)) :=
  cut_tail_cofiber N n X
example (X : Obj N n) (p : Interval (addInitial.obj n))
    (g : ((cutFunctor N n).obj X).obj.obj.obj p ⟶ V.zero)
    (j : V.zero ⟶ ((tailQuotientFunctor N n).obj X).obj.obj.obj p) :
    IsPushout (((cutToId N n).app X).hom.hom.app p) g
      (((tailProjection N n).app X).hom.hom.app p) j := cut_tail_cofiber_component N n X p g j

-- Any chosen coproducts work; their existence follows from the actual Waldhausen structure.
section
variable [HasBinaryCoproducts (Obj N n)]
example : IsExact (ExtensionCategory.productStructure V
      (QuotientRows.waldhausenStructure (acyclicStructure N) n)).cof
    (ExtensionCategory.productStructure V
      (QuotientRows.waldhausenStructure (acyclicStructure N) n)).weq
    (waldhausenStructure N n).cof (waldhausenStructure N n).weq (splitFunctor N n) :=
  splitFunctor_exact N n
example (X : C × QuotientRows.Obj (acyclicStructure N) n) :
    (splitFunctor N n).obj X = ((tailSection N n).obj X.2 ⨿ (fiber N n).obj X.1) := rfl
example {X Y : C × QuotientRows.Obj (acyclicStructure N) n} (f : X ⟶ Y) :
    (splitFunctor N n).map f = coprod.map ((tailSection N n).map f.2) ((fiber N n).map f.1) := rfl
example : splitFunctor N n ⋙ firstTail N n ≅ 𝟭 (C × QuotientRows.Obj (acyclicStructure N) n) :=
  splitFirstTailIso N n
example (X : C × QuotientRows.Obj (acyclicStructure N) n) :
    (splitFirstTailIso N n).inv.app X =
      ((first N n).map (coprod.inr : (fiber N n).obj X.1 ⟶ (splitFunctor N n).obj X),
      (tailFunctor N n).map (coprod.inl : (tailSection N n).obj X.2 ⟶ (splitFunctor N n).obj X)) := rfl
example (X : C × QuotientRows.Obj (acyclicStructure N) n) :
    (splitFirstTailIso N n).inv.app X ≫ (splitFirstTailIso N n).hom.app X = 𝟙 X :=
  (splitFirstTailIso N n).inv_hom_id_app X
example (X : C × QuotientRows.Obj (acyclicStructure N) n) :
    (splitFirstTailIso N n).hom.app X ≫ (splitFirstTailIso N n).inv.app X =
      𝟙 ((firstTail N n).obj ((splitFunctor N n).obj X)) :=
  (splitFirstTailIso N n).hom_inv_id_app X
example : firstTail N n ⋙ splitFunctor N n =
    Additivity.sumFunctor (tailQuotientFunctor N n) (first N n ⋙ fiber N n) := firstTail_splitFunctor N n
end

-- No extra categorical existence assumption is needed to instantiate the section.
example : letI := Additivity.hasBinaryCoproducts (waldhausenStructure N n)
    splitFunctor N n ⋙ firstTail N n ≅ 𝟭 (C × QuotientRows.Obj (acyclicStructure N) n) := by
  letI := Additivity.hasBinaryCoproducts (waldhausenStructure N n)
  exact splitFirstTailIso N n
-- The degree-zero relative row is included.
example : Additivity.IsCofibrationSequence (waldhausenStructure N ⦋0⦌) (waldhausenStructure N ⦋0⦌)
    (cutToId N ⦋0⦌) (tailProjection N ⦋0⦌) := cut_tail_isCofibrationSequence N ⦋0⦌

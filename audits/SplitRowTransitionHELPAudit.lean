import Lean.Util.CollectAxioms
import Quillen.Waldhausen.Fibration.RelativeRows.TransitionHELP
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.Topology.Realization.SplitFiberTransitionHELP,
    `Quillen.Waldhausen.Fibration.RelativeRows.TransitionHELP]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    count := count + 1
    seen := seen.insert origin
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless seen.size == 2 do throwError "Missing defining module"
  unless count == 4 do throwError "Expected 4 declarations, found {count}"
  logInfo m!"Audited all {count} origins of original split-row transition HELP."
noncomputable section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Quillen
open scoped Simplicial Topology
universe u
section Generic
variable {A B E B' E' : SSet.{u}}
  (χ : E ⟶ A ⊗ B) (χ' : E' ⟶ A ⊗ B')
  (s : A ⟶ E) (s' : A ⟶ E') (y : B _⦋0⦌) (y' : B' _⦋0⦌)
  (hs : s ≫ χ = ProductRealization.vertexSection A B y)
  (hs' : s' ≫ χ' = ProductRealization.vertexSection A B' y')
  (a : E ⟶ E') (b : B ⟶ B')
  (sq : a ≫ χ' ≫ snd A B' = χ ≫ snd A B ≫ b)
  (ha : s ≫ a = s')
  (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
  (he : e.toFun = (SSet.toTop.map χ).hom)
  (e' : ContinuousMap.HomotopyEquiv |E'| |A ⊗ B'|)
  (he' : e'.toFun = (SSet.toTop.map χ').hom)
open SplitRealizationFiber
example : CompactHomotopyExtensionLiftingProperty
    (HomotopyPullback.transitionFiber (projection χ) (projection χ')
      (SSet.toTop.map a).hom (SSet.toTop.map b).hom
      (transitionSquare χ χ' a b sq) (realizationPoint y)) :=
  transition_compactHELP_of_natural_split χ χ' s s' y y' hs hs' a b sq ha e he e' he'
example : (firstProjection χ' (SSet.toTop.map b (realizationPoint y))).comp
    ((HomotopyPullback.transitionFiber (projection χ) (projection χ')
      (SSet.toTop.map a).hom (SSet.toTop.map b).hom
      (transitionSquare χ χ' a b sq) (realizationPoint y)).comp (inclusion χ s y hs)) =
    ContinuousMap.id |A| :=
  firstProjection_transition_inclusion χ χ' s s' y y' hs hs' a b sq ha
example [IsEmpty |A|] : CompactHomotopyExtensionLiftingProperty
    (HomotopyPullback.transitionFiber (projection χ) (projection χ')
      (SSet.toTop.map a).hom (SSet.toTop.map b).hom
      (transitionSquare χ χ' a b sq) (realizationPoint y)) :=
  transition_compactHELP_of_natural_split χ χ' s s' y y' hs hs' a b sq ha e he e' he'
end Generic
section Actual
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{u} C] {V : Structure C} (N : NestedWeakEquivalences V)
  {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)
example : CompactHomotopyExtensionLiftingProperty (rowTransitionFiber N α) :=
  rowTransitionFiber_compactHELP N α
example (z : HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom
    (realizationPoint (tailZeroVertex N m.unop))) :
    (rowTransitionFiber N α z).val.1 = SSet.toTop.map ((relativeSRows N).map α) z.val.1 := rfl
example (z : HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom
    (realizationPoint (tailZeroVertex N m.unop))) :
    (rowTransitionFiber N α z).val.2 =
      (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom.comp z.val.2 := rfl
example (P Q : TopCat.{u}) [CompactSpace P] [CompactSpace Q]
    (i : P ⟶ Q) (hi : TheoremA.homotopyExtensionProperty i)
    (a : C(P, HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom
      (realizationPoint (tailZeroVertex N m.unop))))
    (b : C(Q, HomotopyFiber (SSet.toTop.map ((tailSRows N).app n)).hom
      (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)
        (realizationPoint (tailZeroVertex N m.unop)))))
    (H : ((rowTransitionFiber N α).comp a).Homotopy (b.comp i.hom)) :
    ∃ c : C(Q, HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom
      (realizationPoint (tailZeroVertex N m.unop))), c.comp i.hom = a ∧
      ∃ K : ((rowTransitionFiber N α).comp c).Homotopy b,
        ∀ t x, K (t, i x) = H (t,x) :=
  rowTransitionFiber_compactHELP N α P Q i hi a b H
end Actual

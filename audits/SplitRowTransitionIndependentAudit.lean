import Lean.Util.CollectAxioms
import Quillen.Waldhausen.Fibration.RelativeRows.TransitionCartesian
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.Topology.Realization.SplitFiberCartesian,
    `Quillen.Waldhausen.Fibration.RelativeRows.TransitionCartesian]
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
  unless count == 11 do throwError "Expected 11 declarations, found {count}"
  logInfo m!"Audited all {count} origins of original split-row transition cartesianness."
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
  (he' : e'.toFun = (SSet.toTop.map χ').hom) (x : |A|)
open SplitRealizationFiber
example : IsWeakHomotopyEquivalence
    (HomotopyPullback.transitionFiber (projection χ) (projection χ')
      (SSet.toTop.map a).hom (SSet.toTop.map b).hom
      (transitionSquare χ χ' a b sq) (realizationPoint y)) :=
  transition_isWeakHomotopyEquivalence χ χ' s s' y y' hs hs' a b sq ha e he e' he' x
example (z : HomotopyFiber (projection χ) (realizationPoint y)) :
    (HomotopyPullback.transitionFiber (projection χ) (projection χ')
      (SSet.toTop.map a).hom (SSet.toTop.map b).hom
      (transitionSquare χ χ' a b sq) (realizationPoint y) z).1.2 =
    (SSet.toTop.map b).hom.comp z.1.2 := rfl
example (z : HomotopyFiber (projection χ) (realizationPoint y)) :
    (HomotopyPullback.transitionFiber (projection χ) (projection χ')
      (SSet.toTop.map a).hom (SSet.toTop.map b).hom
      (transitionSquare χ χ' a b sq) (realizationPoint y) z).1.1 =
    SSet.toTop.map a z.1.1 := rfl
example (z : HomotopyFiber (projection χ) (realizationPoint y)) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (HomotopyPullback.transitionFiber (projection χ) (projection χ')
        (SSet.toTop.map a).hom (SSet.toTop.map b).hom
        (transitionSquare χ χ' a b sq) (realizationPoint y)) (x := z) rfl) :=
  (transition_isWeakHomotopyEquivalence χ χ' s s' y y' hs hs' a b sq ha e he e' he' x).homotopy_bijective z 0
example [PathConnectedSpace |A|] [PathConnectedSpace |E|] [PathConnectedSpace |B|] :
    IsWeakHomotopyEquivalence (HomotopyPullback.comparison (projection χ')
      (SSet.toTop.map b).hom (projection χ) (SSet.toTop.map a).hom
      (transitionSquare χ χ' a b sq)) :=
  comparison_isWeakHomotopyEquivalence χ χ' s s' y y' hs hs' a b sq ha e he e' he' x
end Generic
section Actual
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{u} C] {V : Structure C} (N : NestedWeakEquivalences V)
  {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)
example : IsWeakHomotopyEquivalence (rowTransitionComparison N α) :=
  rowTransitionComparison_isWeakHomotopyEquivalence N α
example (x : |(relativeSRows N).obj m|) :
    (rowTransitionComparison N α x).1.1 = SSet.toTop.map ((tailSRows N).app m) x := rfl
example (x : |(relativeSRows N).obj m|) :
    (rowTransitionComparison N α x).1.2.1 = SSet.toTop.map ((relativeSRows N).map α) x := rfl
example (x : |(relativeSRows N).obj m|) :
    (rowTransitionComparison N α x).1.2.2 = ContinuousMap.const _
      (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)
        (SSet.toTop.map ((tailSRows N).app m) x)) := rfl
example (x : |(relativeSRows N).obj m|) (k : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin k) (rowTransitionComparison N α) (x := x) rfl) :=
  rowTransitionComparison_bijective N α x k
example (x : |(relativeSRows N).obj m|) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (rowTransitionComparison N α) (x := x) rfl) :=
  rowTransitionComparison_bijective N α x 0
example (z : HomotopyPullback (SSet.toTop.map ((tailSRows N).app n)).hom
    (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom) :
    ∃ x, Joined (rowTransitionComparison N α x) z :=
  (rowTransitionComparison_isWeakHomotopyEquivalence N α).component_surjective z
end Actual

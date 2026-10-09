import Quillen.Waldhausen.Fibration.RelativeRows.RealizationLifting
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.RelativeRows.FiberTransport,
    `Quillen.Topology.HELP.SquareRealizationLifting,
    `Quillen.Waldhausen.Fibration.RelativeRows.RealizationLifting]
  let mut count : Nat := 0
  for origin in targets do
    let mut subtotal : Nat := 0
    for (name, _) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      unless env.header.moduleNames[index.toNat]! == origin do continue
      count := count + 1
      subtotal := subtotal + 1
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{origin}: {name} depends on unsupported assumption {dependency}"
      logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
    logInfo m!"ORIGIN_COUNT {origin}: {subtotal}"
  unless count == 9 do throwError "Expected 9 row-realization-lifting origins, found {count}"
  logInfo m!"Audited all {count} row-realization-lifting origins."
noncomputable section
open CategoryTheory Opposite Quillen Quillen.Waldhausen
open Quillen.Waldhausen.Fibration Quillen.Waldhausen.Fibration.RelativeRows
open scoped Simplicial Topology unitInterval
universe u
section Generic
variable {E F B B' : Type u} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace B] [TopologicalSpace B']
    {p : C(E,B)} {q : C(F,B')} (f : C(E,F)) (v : C(B,B')) (w : q.comp f = v.comp p)
example (b : B) (h : CompactHomotopyExtensionLiftingProperty (HomotopyFiber.map f v w.symm b)) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (MappingPath.endpoint p)
        (HomotopyPullback.strictBaseProjection (MappingPath.endpoint q) v)
        (MappingPath.strictComparison f v w) rfl b) :=
  MappingPath.strictComparison_fiber_compactHELP f v w b h
example (h : ∀ b : B, CompactHomotopyExtensionLiftingProperty (HomotopyFiber.map f v w.symm b))
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i)
      (TopCat.ofHom (MappingPath.endpoint (MappingPath.strictComparison f v w))) :=
  MappingPath.strictComparison_endpoint_realization_mono f v w h i
end Generic
section Rows
variable {C : Type u} [Category.{u} C] {V : Structure C}
    (N : NestedWeakEquivalences V) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)
example (b : |(ordinarySRows (acyclicStructure N)).obj m|)
    (z : HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom b) :
    (rowTransitionFiberAt N α b z).val.1 = SSet.toTop.map ((relativeSRows N).map α) z.val.1 := rfl
example (b : |(ordinarySRows (acyclicStructure N)).obj m|)
    (z : HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom b) :
    (rowTransitionFiberAt N α b z).val.2 =
      (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom.comp z.val.2 := rfl
example : rowTransitionFiberAt N α (realizationPoint (tailZeroVertex N m.unop)) =
    rowTransitionFiber N α := rfl
example (b : |(ordinarySRows (acyclicStructure N)).obj m|) :
    CompactHomotopyExtensionLiftingProperty (rowTransitionFiberAt N α b) :=
  rowTransitionFiberAt_compactHELP N α b
example (b : |(ordinarySRows (acyclicStructure N)).obj m|)
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (a : C(A, HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom b))
    (d : C(D, HomotopyFiber (SSet.toTop.map ((tailSRows N).app n)).hom
      (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α) b)))
    (H : ((rowTransitionFiberAt N α b).comp a).Homotopy (d.comp i.hom)) :
    ∃ c : C(D, HomotopyFiber (SSet.toTop.map ((tailSRows N).app m)).hom b),
      c.comp i.hom = a ∧ ∃ K : ((rowTransitionFiberAt N α b).comp c).Homotopy d,
        ∀ t x, K (t,i x) = H (t,x) := rowTransitionFiberAt_compactHELP N α b A D i hi a d H
example (z : MappingPath (SSet.toTop.map ((tailSRows N).app m)).hom) :
    (rowNormalizedComparison N α z).val.1 = MappingPath.endpoint
      (SSet.toTop.map ((tailSRows N).app m)).hom z := rfl
example (z : MappingPath (SSet.toTop.map ((tailSRows N).app m)).hom) :
    (rowNormalizedComparison N α z).val.2.val.2 =
      (SSet.toTop.map ((ordinarySRows (acyclicStructure N)).map α)).hom.comp z.val.2 := rfl
example {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i)
      (TopCat.ofHom (MappingPath.endpoint (rowNormalizedComparison N α))) :=
  rowNormalizedComparison_endpoint_realization_mono N α i
example (k : ℕ) : HasLiftingProperty (SSet.toTop.map (∂Δ[k].ι : _ ⟶ (Δ[k] : SSet.{u})))
    (TopCat.ofHom (MappingPath.endpoint (rowNormalizedComparison N α))) :=
  rowNormalizedComparison_endpoint_realization_mono N α _
example : HasLiftingProperty (SSet.toTop.map (∂Δ[0].ι : _ ⟶ (Δ[0] : SSet.{u})))
    (TopCat.ofHom (MappingPath.endpoint (rowNormalizedComparison N α))) :=
  rowNormalizedComparison_endpoint_realization_mono N α _
end Rows

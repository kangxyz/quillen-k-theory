import Lean.Util.CollectAxioms
import Quillen.Topology.Realization.ProductFiberHELP
import Quillen.Topology.HomotopyFiber.FiberDetection
import Quillen.Topology.HomotopyFiber.Connected

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`Quillen.Topology.Realization.SplitFiber,
    `Quillen.Topology.HELP.CompactLifting,
    `Quillen.Topology.Realization.ProductCompactHELP,
    `Quillen.Topology.HELP.Composition,
    `Quillen.Topology.HomotopyFiber.CompactHELP,
    `Quillen.Topology.HomotopyFiber.GroupDetection,
    `Quillen.Topology.HomotopyGroups.ZeroDetection,
    `Quillen.Topology.Realization.ProductFiberHELP,
    `Quillen.Topology.HomotopyFiber.FiberDetection,
    `Quillen.Topology.HomotopyFiber.Connected]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    seen := seen.insert origin
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}"
  unless seen.size == 10 do throwError "Missing defining module"
  unless count == 39 do throwError "Expected 39 relative-fiber calculus origins, got {count}"
  logInfo m!"Audited all {count} origins of the ten relative-fiber calculus modules."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Quillen
open scoped Simplicial Topology
universe u v w
section Product
variable (A B : SSet.{u})
example : CompactHomotopyExtensionLiftingProperty (ProductRealization.comparison A B) :=
  ProductRealization.comparison_compactHELP A B
example (T : Type v) [TopologicalSpace T] [CompactSpace T] (f : C(T, |A| × |B|)) :
    ∃ g : C(T, |A ⊗ B|), (ProductRealization.comparison A B).comp g = f :=
  ProductRealization.comparison_compact_lifts_universe A B T f
example (b : |B|) : CompactHomotopyExtensionLiftingProperty (ProductRealization.fiberProjection A B b) :=
  ProductRealization.fiberProjection_compactHELP A B b
end Product
section Split
open SplitRealizationFiber
variable {A B E : SSet.{u}} (χ : E ⟶ A ⊗ B) (s : A ⟶ E) (y : B _⦋0⦌)
  (hs : s ≫ χ = ProductRealization.vertexSection A B y)
  (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|) (he : e.toFun = (SSet.toTop.map χ).hom)
example (x : |A|) (n : ℕ) : Function.Bijective
    (homotopyGroupMap (N := Fin n) (inclusion χ s y hs) (x := x) rfl) :=
  inclusion_bijective χ s y hs e he x n
example (x : |A|) : Function.Bijective
    (homotopyGroupMap (N := Fin 0) (inclusion χ s y hs) (x := x) rfl) :=
  inclusion_bijective χ s y hs e he x 0
example (x : |A|) : (inclusion χ s y hs x).1.2 = ContinuousMap.const _ (realizationPoint y) := rfl
example (b : |B|) : CompactHomotopyExtensionLiftingProperty (firstProjection χ b) :=
  firstProjection_compactHELP χ e he b
example [PathConnectedSpace |A|] (b : |B|) (p : HomotopyFiber (projection χ) b) :
    PathConnectedSpace (HomotopyFiber (projection χ) b) := fiber_pathConnected χ e he b p
end Split
section Detection
open HomotopyFiber
variable {X : Type u} {Y : Type v} {B : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (f : C(X, B)) (g : C(Y, B)) (m : C(X, Y)) (sq : g.comp m = f)
  (x : X) (b : B) (hx : f x = b)
example (h₁ : Function.Bijective (homotopyGroupMap (N := Fin 1)
    (mapOver f g m sq b) (mapOver_basepoint f g m sq x b hx)))
    (h₀ : Function.Injective (homotopyGroupMap (N := Fin 0)
      (mapOver f g m sq b) (mapOver_basepoint f g m sq x b hx))) :
    Function.Bijective (piMap 0 m (x := x) rfl) :=
  piMap_bijective_of_fiberMap f g m sq x b hx 0 h₁ h₀
example [PathConnectedSpace X] [PathConnectedSpace Y]
    (h : ∀ n, Function.Bijective (homotopyGroupMap (N := Fin n)
      (mapOver f g m sq b) (mapOver_basepoint f g m sq x b hx))) (x' : X) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) m (x := x') rfl) :=
  homotopyGroupMap_bijective_at_all_points_of_fiberMap f g m sq x b hx h x' n
end Detection

section ExactHELP
open scoped unitInterval
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (e : C(X, Y)) (he : Function.Injective e)
  (hl : ∀ (T : Type u) [TopologicalSpace T] [CompactSpace T] (g : C(T,Y)),
    ∃ h : C(T,X), e.comp h = g)
example (A B : TopCat.{u}) [CompactSpace A] [CompactSpace B] (i : A ⟶ B)
    (hi : TheoremA.homotopyExtensionProperty i) (a : C(A,X)) (b : C(B,Y))
    (H : (e.comp a).Homotopy (b.comp i.hom)) :
    ∃ c : C(B,X), c.comp i.hom = a ∧
      ∃ K : (e.comp c).Homotopy b, ∀ t x, K (t,i x) = H (t,x) :=
  compactHELP_of_injective_compact_lifts e he hl A B i hi a b H
example (f : C(X,Y)) (g : C(Y,Z))
    (hf : CompactHomotopyExtensionLiftingProperty f)
    (hg : CompactHomotopyExtensionLiftingProperty g)
    (A B : TopCat.{u}) [CompactSpace A] [CompactSpace B] (i : A ⟶ B)
    (hi : TheoremA.homotopyExtensionProperty i) (a : C(A,X)) (b : C(B,Z))
    (H : ((g.comp f).comp a).Homotopy (b.comp i.hom)) :
    ∃ c : C(B,X), c.comp i.hom = a ∧
      ∃ K : ((g.comp f).comp c).Homotopy b, ∀ t x, K (t,i x) = H (t,x) :=
  hg.comp hf A B i hi a b H
example (f : C(Y,Z)) (z : Z) :
    CompactHomotopyExtensionLiftingProperty (HomotopyFiber.sourceMap f e z) :=
  HomotopyFiber.sourceMap_compactHELP f e he hl z
example (p : C(X,Y)) (hp : HomotopyLiftingProperty p) (y : Y)
    [PathConnectedSpace Y] [PathConnectedSpace {x : X // p x = y}] :
    PathConnectedSpace X := pathConnectedSpace_of_fibration p hp y
example (f : C(X,Z)) (g : C(Y,Z)) (y : Y)
    [PathConnectedSpace Y] [PathConnectedSpace (HomotopyFiber f (g y))] :
    PathConnectedSpace (HomotopyPullback f g) := HomotopyPullback.pathConnectedSpace f g y
end ExactHELP

section ActualPaths
universe t
variable {X : Type u} {Y : Type v} {Z : Type w} {T : Type t}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace T] [CompactSpace T]
  (f : C(Y,Z)) (e : C(X,Y)) (z : Z)
example (p : HomotopyFiber (f.comp e) z) :
    (HomotopyFiber.sourceMap f e z p).1 = (e p.1.1, p.1.2) := rfl
example (hl : ∀ g : C(T,Y), ∃ h : C(T,X), e.comp h = g)
    (g : C(T, HomotopyFiber f z)) :
    ∃ h : C(T, HomotopyFiber (f.comp e) z),
      (HomotopyFiber.sourceMap f e z).comp h = g ∧ ∀ t, (h t).1.2 = (g t).1.2 := by
  obtain ⟨h, hh⟩ := HomotopyFiber.sourceMap_compact_lifts_universe f e T hl z g
  refine ⟨h, hh, fun t => ?_⟩
  exact congrArg (fun q : HomotopyFiber f z => q.1.2) (ContinuousMap.congr_fun hh t)
end ActualPaths

section ActualSplitMaps
open SplitRealizationFiber
variable {A B E : SSet.{u}} (χ : E ⟶ A ⊗ B)
  (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|) (he : e.toFun = (SSet.toTop.map χ).hom)
example (y : |B|) (p : HomotopyFiber (projection χ) y) :
    (comparison χ y p).1 = (SSet.toTop.map χ p.1.1, p.1.2) := rfl
example (y : |B|) : (comparisonHomotopyEquiv χ e he y).toFun = comparison χ y := rfl
example (y : |B|) (p : HomotopyFiber (projection χ) y) :
    firstProjection χ y p = SSet.toTop.map (χ ≫ fst A B) p.1.1 :=
  firstProjection_apply χ y p
example (s : A ⟶ E) (y : B _⦋0⦌) (hs : s ≫ χ = ProductRealization.vertexSection A B y)
    (x : |A|) : (inclusion χ s y hs x).1.1 = SSet.toTop.map s x := rfl
example (s : A ⟶ E) (y : B _⦋0⦌) (hs : s ≫ χ = ProductRealization.vertexSection A B y) :
    (comparison χ (realizationPoint y)).comp (inclusion χ s y hs) =
      ProductRealization.fiberInclusion A B y := comparison_inclusion χ s y hs
end ActualSplitMaps

section ActualDetectionMaps
open HomotopyFiber
variable {X : Type u} {Y : Type v} {B : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (f : C(X,B)) (g : C(Y,B)) (m : C(X,Y)) (sq : g.comp m = f)
  (x : X) (b : B) (hx : f x = b)
example : mapOver f g m sq b = HomotopyFiber.map m (ContinuousMap.id B) sq.symm b := rfl
example (p : HomotopyFiber f b) : (mapOver f g m sq b p).1.1 = m p.1.1 := rfl
example (p : HomotopyFiber f b) : (mapOver f g m sq b p).1.2 = p.1.2 := rfl
example (a : HomotopyGroup.Pi 1 B b) :
    connectingMap f b x hx 0 a =
      homotopyGroupMap (loopInclusion f b x hx) (loopInclusion_refl f b x hx)
        (loopShiftEquiv 0 a) := rfl
example [PathConnectedSpace X] [PathConnectedSpace Y]
    (h : ∀ n, Function.Bijective (homotopyGroupMap (N := Fin n)
      (mapOver f g m sq b) (mapOver_basepoint f g m sq x b hx))) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) m (x := x) rfl) :=
  homotopyGroupMap_bijective_of_fiberMap f g m sq x b hx h 0
end ActualDetectionMaps

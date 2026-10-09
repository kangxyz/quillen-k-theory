import Quillen.Topology.Realization.SplitFiberCompactHELP
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Topology.HELP.StrictCompact,
    `Quillen.Topology.HELP.RetraceBoundary, `Quillen.Topology.HELP.CancelFirst,
    `Quillen.Topology.HELP.CylinderBoundary, `Quillen.Topology.HELP.CancelSecond,
    `Quillen.Topology.HELP.HomotopyInvariance, `Quillen.Topology.HELP.TwoOfThree,
    `Quillen.Topology.Realization.SplitFiberCompactHELP]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.moduleNames[index.toNat]! do continue
    count := count + 1
    let axioms ← collectAxioms name
    for a in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Unsupported {a}: {name}"
    logInfo m!"ACCEPTED {env.header.moduleNames[index.toNat]!} {name}: {axioms}"
  unless count == 43 do throwError "Expected 43 compact HELP origins, got {count}"
  logInfo m!"Audited all {count} compact HELP two-of-three origins."
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen
open scoped Topology unitInterval
universe u v
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable (f : C(X, Y)) (g : C(Y, Z))
example (hf : CompactHomotopyExtensionLiftingProperty f) : CompactStrictHELP f := hf.strict
example (hf : CompactStrictHELP f) : CompactHomotopyExtensionLiftingProperty f := hf.full
example : CompactHomotopyExtensionLiftingProperty f ↔ CompactStrictHELP f := compactHELP_iff_strict f
example (hf : CompactHomotopyExtensionLiftingProperty f)
    (A B : TopCat.{u}) [CompactSpace A] [CompactSpace B] (i : A ⟶ B)
    (hi : TheoremA.homotopyExtensionProperty i) (a : C(A, X)) (b : C(B, Y))
    (w : f.comp a = b.comp i.hom) :
    ∃ c : C(B, X), c.comp i.hom = a ∧ Nonempty ((f.comp c).HomotopyRel b (Set.range i)) :=
  hf.strict A B i hi a b w
example (hf : CompactStrictHELP f)
    (A B : TopCat.{u}) [CompactSpace A] [CompactSpace B] (i : A ⟶ B)
    (hi : TheoremA.homotopyExtensionProperty i) (a : C(A, X)) (b : C(B, Y))
    (H : (f.comp a).Homotopy (b.comp i.hom)) :
    ∃ c : C(B, X), c.comp i.hom = a ∧ ∃ K : (f.comp c).Homotopy b,
      ∀ t x, K (t, i x) = H (t, x) := hf.full A B i hi a b H
example (hf : CompactHomotopyExtensionLiftingProperty f)
    (A : TopCat.{u}) [CompactSpace A] (a : C(A, Y)) :
    ∃ c : C(A, X), Nonempty ((f.comp c).Homotopy a) := hf.lift_compact A a
example (hf : CompactHomotopyExtensionLiftingProperty f)
    (hgf : CompactHomotopyExtensionLiftingProperty (g.comp f)) :
    CompactHomotopyExtensionLiftingProperty g := hgf.cancel_first hf
example (hg : CompactHomotopyExtensionLiftingProperty g)
    (hgf : CompactHomotopyExtensionLiftingProperty (g.comp f)) :
    CompactHomotopyExtensionLiftingProperty f := hgf.cancel_second hg
example (hf : CompactHomotopyExtensionLiftingProperty f) :
    CompactHomotopyExtensionLiftingProperty (g.comp f) ↔ CompactHomotopyExtensionLiftingProperty g :=
  compactHELP_comp_iff_of_first hf
example (hg : CompactHomotopyExtensionLiftingProperty g) :
    CompactHomotopyExtensionLiftingProperty (g.comp f) ↔ CompactHomotopyExtensionLiftingProperty f :=
  compactHELP_comp_iff_of_second hg
example {f' : C(X, Y)} (hf : CompactHomotopyExtensionLiftingProperty f) (H : f.Homotopy f') :
    CompactHomotopyExtensionLiftingProperty f' := hf.of_homotopy H
example {f' : C(X, Y)} (H : f.Homotopic f') :
    CompactHomotopyExtensionLiftingProperty f ↔ CompactHomotopyExtensionLiftingProperty f' :=
  compactHELP_iff_of_homotopic H
example (p : C(Y, X)) (s : C(X, Y)) (hp : CompactHomotopyExtensionLiftingProperty p)
    (hps : p.comp s = ContinuousMap.id X) : CompactHomotopyExtensionLiftingProperty s :=
  compactHELP_section hp hps
example (s₀ : C(X, Y)) (s₁ : C(X, Z)) (t : C(Y, Z))
    (h₀ : CompactHomotopyExtensionLiftingProperty s₀)
    (h₁ : CompactHomotopyExtensionLiftingProperty s₁) (ht : t.comp s₀ = s₁) :
    CompactHomotopyExtensionLiftingProperty t := compactHELP_transition h₀ h₁ ht
example (s₀ : C(X, Y)) (s₁ : C(X, Z)) (t : C(Y, Z))
    (h₀ : CompactHomotopyExtensionLiftingProperty s₀)
    (h₁ : CompactHomotopyExtensionLiftingProperty s₁) (ht : (t.comp s₀).Homotopic s₁) :
    CompactHomotopyExtensionLiftingProperty t := compactHELP_transition_of_homotopy h₀ h₁ ht
section Cylinder
variable {A B : TopCat.{u}} (i : A ⟶ B)
example : IsPushout (TheoremA.cylinderBoundaryEnds A) (TheoremA.cylinderBoundarySumMap i)
    (TheoremA.cylinderBoundarySide i) (TheoremA.cylinderBoundaryCaps i) :=
  TheoremA.cylinderBoundary_isPushout i
example : TheoremA.cylinderBoundarySide i ≫ TheoremA.cylinderBoundaryMap i =
    TheoremA.cylinderBoundarySideMap i := TheoremA.cylinderBoundarySide_map i
example : TheoremA.cylinderBoundaryCaps i ≫ TheoremA.cylinderBoundaryMap i =
    TheoremA.cylinderBoundaryEnds B := TheoremA.cylinderBoundaryCaps_map i
example [CompactSpace A] [CompactSpace B] : CompactSpace (TheoremA.CylinderBoundary i) := inferInstance
example (hi : TheoremA.homotopyExtensionProperty i) :
    TheoremA.homotopyExtensionProperty (TheoremA.cylinderBoundaryMap i) :=
  TheoremA.homotopyExtensionProperty_cylinderBoundaryMap i hi
end Cylinder
section Retrace
variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
variable {a b : C(A, B)} (L : a.Homotopy b)
example : (L.symm.trans L).toContinuousMap.HomotopyRel
    (ContinuousMap.Homotopy.refl b).toContinuousMap
    {z : unitInterval × A | z.1 = 0 ∨ z.1 = 1} := retraceHomotopy L
example (x : A) (s : unitInterval) : retraceHomotopy L (s, (0, x)) = b x :=
  ((retraceHomotopy L).prop s (0, x) (Or.inl rfl)).trans ((L.symm.trans L).map_zero_left x)
example (x : A) (s : unitInterval) : retraceHomotopy L (s, (1, x)) = b x :=
  ((retraceHomotopy L).prop s (1, x) (Or.inr rfl)).trans ((L.symm.trans L).map_one_left x)
end Retrace

section ActualSplit
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped Simplicial
variable {A B E : SSet.{u}} (χ : E ⟶ A ⊗ B) (s : A ⟶ E) (y : B _⦋0⦌)
    (hs : s ≫ χ = ProductRealization.vertexSection A B y)
    (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
    (he : e.toFun = (SSet.toTop.map χ).hom)
example : (SplitRealizationFiber.firstProjection χ (realizationPoint y)).comp
    (SplitRealizationFiber.inclusion χ s y hs) = ContinuousMap.id |A| :=
  SplitRealizationFiber.firstProjection_inclusion χ s y hs
example : CompactHomotopyExtensionLiftingProperty (SplitRealizationFiber.inclusion χ s y hs) :=
  SplitRealizationFiber.inclusion_compactHELP χ s y hs e he
example (x : |A|) : (SplitRealizationFiber.inclusion χ s y hs x).1.2 =
    ContinuousMap.const _ (realizationPoint y) := rfl
example (x : |A|) : (SplitRealizationFiber.inclusion χ s y hs x).1.1 = SSet.toTop.map s x := rfl
example {B' E' : SSet.{u}} (χ' : E' ⟶ A ⊗ B') (s' : A ⟶ E') (y' : B' _⦋0⦌)
    (hs' : s' ≫ χ' = ProductRealization.vertexSection A B' y')
    (e' : ContinuousMap.HomotopyEquiv |E'| |A ⊗ B'|)
    (he' : e'.toFun = (SSet.toTop.map χ').hom)
    (t : C(HomotopyFiber (SplitRealizationFiber.projection χ) (realizationPoint y),
      HomotopyFiber (SplitRealizationFiber.projection χ') (realizationPoint y')))
    (ht : t.comp (SplitRealizationFiber.inclusion χ s y hs) =
      SplitRealizationFiber.inclusion χ' s' y' hs') :
    CompactHomotopyExtensionLiftingProperty t :=
  SplitRealizationFiber.transition_compactHELP χ s y hs χ' s' y' hs' e he e' he' t ht
end ActualSplit

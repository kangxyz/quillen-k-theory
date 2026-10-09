import Quillen.Topology.FiberwiseMappingPath.Locality

/-! # A local fiberwise HELP criterion for the original map

The hypotheses are actual Hurewicz lifting and full compact HELP for the
original strict-fiber maps of the displayed restrictions. They are not a
fiber conclusion for a global mapping-path replacement.
-/
noncomputable section
open scoped Topology unitInterval
universe u v
namespace Quillen.FiberwiseMappingPath
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- Local HLP and original strict-fiber HELP give exact global vertical endpoint lifts. -/
theorem endpoint_boundaryLifting_of_local_fiberHELP (q : C(F,B)) (f : C(E,F))
    {J : Type v} (U : J → Set B) (hU : ∀ j,IsOpen (U j))
    (hcover : ∀ b : B,∃ j,b ∈ U j)
    (hp : ∀ j,HomotopyLiftingProperty (restrictedProjection (q.comp f) (U j)))
    (hq : ∀ j,HomotopyLiftingProperty (restrictedProjection q (U j)))
    (hf : ∀ (j : J) (b : U j),CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (restrictedProjection (q.comp f) (U j))
        (restrictedProjection q (U j)) (restrictedMap q f (U j)) rfl b)) :
    CubicalSubdivision.BoundaryLifting (endpoint q f) := by
  apply endpoint_boundaryLifting_of_open_cover q f U hU hcover
  intro j
  exact endpoint_boundaryLifting_of_fiberHELP (restrictedProjection (q.comp f) (U j))
    (restrictedProjection q (U j)) (restrictedMap q f (U j)) rfl (hp j) (hq j) (hf j)

/-- The actual map is weak, including all zero-dimensional components and empty cases. -/
theorem isWeakHomotopyEquivalence_of_local_fiberHELP (q : C(F,B)) (f : C(E,F))
    {J : Type v} (U : J → Set B) (hU : ∀ j,IsOpen (U j))
    (hcover : ∀ b : B,∃ j,b ∈ U j)
    (hp : ∀ j,HomotopyLiftingProperty (restrictedProjection (q.comp f) (U j)))
    (hq : ∀ j,HomotopyLiftingProperty (restrictedProjection q (U j)))
    (hf : ∀ (j : J) (b : U j),CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (restrictedProjection (q.comp f) (U j))
        (restrictedProjection q (U j)) (restrictedMap q f (U j)) rfl b)) :
    IsWeakHomotopyEquivalence f := by
  have he := (endpoint_boundaryLifting_of_local_fiberHELP q f U hU hcover hp hq hf).isWeakHomotopyEquivalence
  exact he.comp (isWeakHomotopyEquivalence_of_homotopyEquiv (inclusionHomotopyEquiv q f))

end Quillen.FiberwiseMappingPath

import Quillen.Topology.CubicalSubdivision.BoundaryLifting
import Quillen.Topology.HELP.ContractibleTestFull
import Quillen.Topology.HELP.PairLifting
import Quillen.Topology.HELP.SquareRealizationLifting

/-! # Actual cubical endpoint lifting from full HELP on original fibers

Only the compact lifted cube and its entire actual boundary are used as tests.
The total spaces are arbitrary spaces in the stated common universe.
-/
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.MappingPath
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- Genuine compact fiber HELP gives literal finite cube-boundary RLP for
this original comparison's mapping-path endpoint. -/
theorem endpoint_boundaryLifting_of_fiberHELP
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq b)) :
    CubicalSubdivision.BoundaryLifting (endpoint f) := by
  apply CubicalSubdivision.boundaryLifting_of_hasLiftingProperty
  intro n
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} n).space :=
    (CubicalTests.boundaryPresentation n).compact
  let : CompactSpace (CubicalTests.boundary.{u} n) :=
    (CubicalTests.boundaryPresentationHomeomorph n).compactSpace
  apply endpoint_hasLiftingProperty_of_pairHELP f
  intro a b H
  exact fullHELP_on_contracted_test p q f sq hp hq hf _ _ _
    (CubicalTests.boundaryInclusion_hep n) (CubicalTests.zero n)
    (CubicalTests.contraction n) a b H

variable {B' : Type u} [TopologicalSpace B']

/-- The original strict square's full homotopy-fiber HELP supplies the same
literal RLP for its normalized comparison, retaining the original paths. -/
theorem strictComparison_endpoint_boundaryLifting
    {p : C(E,B)} {q : C(F,B')} (f : C(E,F)) (v : C(B,B'))
    (w : q.comp f = v.comp p)
    (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.map f v w.symm b)) :
    CubicalSubdivision.BoundaryLifting (endpoint (strictComparison f v w)) :=
  endpoint_boundaryLifting_of_fiberHELP (endpoint p)
    (HomotopyPullback.strictBaseProjection (endpoint q) v) (strictComparison f v w) rfl
    (endpoint_homotopyLiftingProperty p)
    (HomotopyLiftingProperty.baseChange (endpoint q) v (endpoint_homotopyLiftingProperty q))
    (fun b ↦ strictComparison_fiber_compactHELP f v w b (hf b))

end Quillen.MappingPath

import Quillen.Topology.HomotopyLifting.OverBaseCorrection
import Quillen.Topology.HomotopyLifting.CubeDuration
import Quillen.Topology.HELP.ContractibleTestOverBase

/-! # Genuine whole-boundary cubical HELP over the displayed base

Ordinary contracted HELP is first proved from actual strict-fiber HELP. Its
base coordinate is then corrected by genuine stationary lifting, and the
comparison homotopy is straightened vertically. Every original boundary
value is retained throughout the two corrections.
-/
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- Strict cubical HELP over the actual prescribed base map, derived from
full compact HELP on the original strict fibers of genuine fibrations. -/
theorem strictHELP_over_cube_of_fiberHELP
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq b))
    (n : ℕ) (a : C(CubicalTests.boundary.{u} n,E)) (b : C(CubicalTests.cube.{u} n,F))
    (w : f.comp a = b.comp (CubicalTests.boundaryInclusion n).hom) :
    ∃ c : C(CubicalTests.cube.{u} n,E),
      c.comp (CubicalTests.boundaryInclusion n).hom = a ∧ p.comp c = q.comp b ∧
      ∃ V : (f.comp c).Homotopy b,
        HomotopyOver (q.comp b) q V ∧
        ∀ (t : unitInterval) (x : CubicalTests.boundary.{u} n),V (t,x.val) = f (a x) := by
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} n).space :=
    (CubicalTests.boundaryPresentation n).compact
  let : CompactSpace (CubicalTests.boundary.{u} n) :=
    (CubicalTests.boundaryPresentationHomeomorph n).compactSpace
  apply strictHELP_over_contracted_test p q f sq hp hq hf _ _
    (CubicalTests.boundaryInclusion n) (CubicalTests.boundaryInclusion_hep n)
    (CubicalTests.zero n) (CubicalTests.contraction n) (CubicalTests.boundaryDuration n) _ a b w
  intro x
  rw [CubicalTests.boundaryDuration_eq_zero_iff]
  constructor
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩
  · rintro ⟨y,rfl⟩
    exact y.property

end Quillen

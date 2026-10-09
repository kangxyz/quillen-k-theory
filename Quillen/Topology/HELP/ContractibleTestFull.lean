import Quillen.Topology.HELP.ContractibleTest
import Quillen.Topology.HELP.StrictPair

/-! # Full boundary homotopies on genuinely compact contracted tests -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- For actual fibrations with compact HELP on all original strict-fiber maps,
full prescribed-boundary HELP holds on this actual compact contracted test.
The target map can change during the HEP reduction, so all its possible fiber
points are covered by the displayed structural premise. -/
theorem fullHELP_on_contracted_test
    (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b : B, CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq b))
    (A D : TopCat.{u}) [CompactSpace A] [CompactSpace D]
    (i : A ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (d : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d))
    (a : C(A,E)) (b : C(D,F)) (H : (f.comp a).Homotopy (b.comp i.hom)) :
    ∃ c : C(D,E), c.comp i.hom = a ∧ ∃ K : (f.comp c).Homotopy b,
      ∀ t x, K (t, i x) = H (t,x) :=
  fullHELP_at_pair_of_strict f A D i hi
    (fun a b w ↦ strictHELP_on_contracted_test_of_all_fibers p q f sq hp hq hf A D i hi d HD a b w)
    a b H

end Quillen

import Quillen.Waldhausen.Fibration.RelativeRows.FiltrationRealization
import Quillen.Waldhausen.Fibration.MixedNerves.TotalEvaluation
import Quillen.Waldhausen.Fibration.CanonicalFiberMap
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RelativeRows.IndependentZero
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse)

/-- The actual forward composite preserves the actual original chosen zero simplex. -/
theorem original_composite_zero (n : SimplexCategory) :
    (MixedNerves.totalCofEvaluation N).app (op n)
      ((relativeFiltrationTotalMap N he).app (op n)
        (zeroSimplex (waldhausenStructure N n).cof (waldhausenStructure N n).weq
          (zero N n) (isZero N n) (op n))) =
      zeroSimplex N.coarse.cof N.coarse.weq N.coarse.zero N.coarse.isZero (op n) := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ N.zero_eq.symm) ?_
  intro i j f
  exact V.isZero.eq_of_src _ _

/-- The original split-fiber map preserves the actual inherited relative zero. -/
theorem original_fiber_zero (n : SimplexCategory) :
    (TheoremA.diagonalMap (fiberSRows N)).app (op n)
      (zeroSimplex V.cof V.weq V.zero V.isZero (op n)) =
      zeroSimplex (waldhausenStructure N n).cof (waldhausenStructure N n).weq
        (zero N n) (isZero N n) (op n) := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ fiber_zero N n) ?_
  intro i j f
  exact ((fiber_exact N n).zero V.isZero).eq_of_src _ _

/-- The canonical original change-of-weak-class map uses that same original zero equality. -/
theorem original_changeWeak_zero (n : SimplexCategory) :
    (sSetMap (changeWeak_exact N)).app (op n) (zeroSimplex V.cof V.weq V.zero V.isZero (op n)) =
      zeroSimplex N.coarse.cof N.coarse.weq N.coarse.zero N.coarse.isZero (op n) := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ N.zero_eq.symm) ?_
  intro i j f
  exact V.isZero.eq_of_src _ _

end Quillen.Waldhausen.Fibration.RelativeRows.IndependentZero

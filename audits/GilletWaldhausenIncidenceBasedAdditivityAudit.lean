import Quillen.Waldhausen.GilletWaldhausen.CycleEvaluationSequence
import Quillen.Waldhausen.Additivity.BasedAdditivity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
open Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
variable {A : Type u} [SmallCategory A] [Abelian A] (P : ObjectProperty A)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]
local instance : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The public normalized term K-map is the public normalized sum-functor K-map. -/
theorem incidence_KMap_additivity (i : ℤ) (n : ℕ) :
    KMap (boundedAcyclicEvaluationExactFunctor P i).waldhausenExact n =
      KMap (Additivity.sumFunctor_isExact
        (ofExactCategory (boundedAcyclicExactStructure P))
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P))
        (boundedAcyclicCyclesExactFunctor P (i + 1)).waldhausenExact
        (boundedAcyclicCyclesExactFunctor P i).waldhausenExact) n :=
  Additivity.KMap_additivity _ _ (boundedAcyclicCycleInclusion P i)
    (boundedAcyclicCycleProjection P i) (boundedAcyclicCycleEvaluation_isCofibrationSequence P i) n

#print axioms incidence_KMap_additivity

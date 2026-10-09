import Quillen.Waldhausen.GilletWaldhausen.CyclesExact
import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence

/-! # The actual cycle-to-term incidence cofibration sequence

On bounded acyclic termwise-P complexes, the original cycle inclusion and
original differential factorization give a genuine cofibration sequence of
exact functors `Z_n → E_n → Z_(n+1)` into P. Quotient exactness supplies the
relative-pushout cofibration condition. The weak maps here are isomorphisms:
cycles and terms do not generally send quasi-isomorphisms to isomorphisms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A)

/-- Evaluation at an actual term, as a functor into the original term subcategory. -/
def boundedAcyclicEvaluationFunctor (n : ℤ) :
    (boundedAcyclic P).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((boundedAcyclic P).ι ⋙ eval A (ComplexShape.up ℤ) n)
    (fun K ↦ K.property.2.1 n)

@[simp]
theorem boundedAcyclicEvaluationFunctor_map (n : ℤ)
    {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    ((boundedAcyclicEvaluationFunctor P n).map f).hom = f.hom.f n := rfl

instance boundedAcyclicEvaluationFunctor_additive (n : ℤ) :
    (boundedAcyclicEvaluationFunctor P n).Additive :=
  inferInstanceAs (Functor.Additive (P.lift _ _))

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

local instance : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The actual evaluation functor preserves inherited conflations.
Kernel closure is not required for evaluation. -/
def boundedAcyclicEvaluationExactFunctor (n : ℤ) :
    ExactFunctor (boundedAcyclicExactStructure P)
      (ExactSubcategory.exactStructure (abelianExactStructure A) P) where
  toFunctor := boundedAcyclicEvaluationFunctor P n
  map_conflation S hS :=
    (shortExact_iff_degreewise_shortExact (S.map (boundedAcyclic P).ι)).1 hS n

variable [(abelianExactStructure A).IsKernelClosed P]

/-- The original cycle inclusions, natural in every actual chain map. -/
def boundedAcyclicCycleInclusion (n : ℤ) :
    boundedAcyclicCyclesFunctor P n ⟶ boundedAcyclicEvaluationFunctor P n where
  app K := P.homMk (K.obj.iCycles n)
  naturality _ _ f := ObjectProperty.hom_ext _ (cyclesMap_i f.hom n)

/-- The original differential factorizations onto the next cycles. -/
def boundedAcyclicCycleProjection (n : ℤ) :
    boundedAcyclicEvaluationFunctor P n ⟶ boundedAcyclicCyclesFunctor P (n + 1) where
  app K := P.homMk (K.obj.toCycles n (n + 1))
  naturality _ _ f := ObjectProperty.hom_ext _ (toCycles_naturality f.hom n (n + 1)).symm

omit [P.ContainsZero] [(abelianExactStructure A).IsExtensionClosed P] in
@[simp]
theorem boundedAcyclicCycleInclusion_hom (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    ((boundedAcyclicCycleInclusion P n).app K).hom = K.obj.iCycles n := rfl

omit [P.ContainsZero] [(abelianExactStructure A).IsExtensionClosed P] in
@[simp]
theorem boundedAcyclicCycleProjection_hom (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    ((boundedAcyclicCycleProjection P n).app K).hom = K.obj.toCycles n (n + 1) := rfl

omit [P.ContainsZero] [(abelianExactStructure A).IsExtensionClosed P] in
@[reassoc]
theorem boundedAcyclicCycle_comp_zero (n : ℤ) :
    boundedAcyclicCycleInclusion P n ≫ boundedAcyclicCycleProjection P n = 0 := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _ (iCycles_toCycles K.obj n)

/-- Every component is the original actual cycle short exact sequence. -/
theorem boundedAcyclicCycleEvaluation_conflation (n : ℤ)
    (K : (boundedAcyclic P).FullSubcategory) :
    (ExactSubcategory.exactStructure (abelianExactStructure A) P).conflation
      (ShortComplex.mk ((boundedAcyclicCycleInclusion P n).app K)
        ((boundedAcyclicCycleProjection P n).app K)
        (NatTrans.congr_app (boundedAcyclicCycle_comp_zero P n) K)) :=
  cycleSequence_shortExact K.obj n (K.property.2.2 (n + 1))

/-- The relative pushout comparison is genuinely admissible, derived from
exactness of the next-cycle functor rather than assumed. -/
theorem boundedAcyclicCycleEvaluation_cofibration (n : ℤ) :
    Additivity.IsCofibrationTransformation
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P))
      (boundedAcyclicCycleInclusion P n) (ofExactCategory (boundedAcyclicExactStructure P)) :=
  exactFunctorSequence_cofibration _ _ _ _ (boundedAcyclicCycle_comp_zero P n)
    (boundedAcyclicCycleEvaluation_conflation P n)
    (boundedAcyclicCyclesExactFunctor P (n + 1)).map_inflation

/-- The genuine incidence cofibration sequence in the isomorphism models,
retaining the original term evaluation and original cycle arrows. -/
theorem boundedAcyclicCycleEvaluation_isCofibrationSequence (n : ℤ) :
    Additivity.IsCofibrationSequence (ofExactCategory (boundedAcyclicExactStructure P))
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P))
      (boundedAcyclicCycleInclusion P n) (boundedAcyclicCycleProjection P n) :=
  exactFunctorSequence_isCofibrationSequence _ _ _ _ (boundedAcyclicCycle_comp_zero P n)
    (boundedAcyclicCycleEvaluation_conflation P n)
    (boundedAcyclicCyclesExactFunctor P n) (boundedAcyclicEvaluationExactFunctor P n)
    (boundedAcyclicCyclesExactFunctor P (n + 1)) rfl rfl rfl

end Quillen.Waldhausen.GilletWaldhausen

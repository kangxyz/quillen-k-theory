import Quillen.Library

/-! Consumers of the original degreewise relative-row maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory Quillen Quillen.Waldhausen
open Quillen.Waldhausen.Fibration Quillen.Waldhausen.Fibration.RelativeRows
open scoped Simplicial Topology
universe u
namespace Consumer
variable {C : Type u} [Category.{u} C] {V : Structure C}
    (N : NestedWeakEquivalences V) (n : SimplexCategory)

def actual_first_tail_equivalence : ContinuousMap.HomotopyEquiv
    |(relativeSRows N).obj (op n)|
    |sSet V.cof V.weq ⊗ (ordinarySRows (acyclicStructure N)).obj (op n)| :=
  firstTailSSetRealizationHomotopyEquiv N n

theorem actual_first_tail_forward :
    (actual_first_tail_equivalence N n).toFun = (SSet.toTop.map (firstTailSSet N n)).hom :=
  firstTailSSetRealizationHomotopyEquiv_toFun N n

theorem actual_tail_projection :
    rowFiberProjection N n = (SSet.toTop.map ((tailSRows N).app (op n))).hom :=
  rowFiberProjection_eq N n

theorem actual_relative_fiber_map (x : |sSet V.cof V.weq|) :
    (rowFiberInclusion N n x).1 =
      (SSet.toTop.map ((fiberSRows N).app (op n)) x,
        ContinuousMap.const _ (realizationPoint (tailZeroVertex N n))) := rfl

theorem actual_relative_fiber_bijective (x : |sSet V.cof V.weq|) (k : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin k) (rowFiberInclusion N n) (x := x) rfl) :=
  rowFiberInclusion_bijective N n x k

theorem actual_relative_fiber_zero (x : |sSet V.cof V.weq|) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (rowFiberInclusion N ⦋0⦌) (x := x) rfl) :=
  rowFiberInclusion_bijective N ⦋0⦌ x 0


/-- The actual original coarse-weak cofibration chain is completed by genuine cofibers. -/
def actual_chain_completion (F : ComposableArrows C n.len)
    (hF : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), V.cof (F.map f))
    (hw : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), N.coarse.weq (F.map f)) : Obj N n :=
  relativeCompletion N F hF hw

def actual_chain_recovery (F : ComposableArrows C n.len)
    (hF : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), V.cof (F.map f))
    (hw : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), N.coarse.weq (F.map f)) :
    F ≅ (initialFiltrationFunctor N n).obj (actual_chain_completion N n F hF hw) :=
  relativeCompletionInitialIso N F hF hw

theorem actual_chain_recovery_forward (F : ComposableArrows C n.len)
    (hF : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), V.cof (F.map f))
    (hw : ∀ {i j : Fin (n.len+1)} (f : i ⟶ j), N.coarse.weq (F.map f))
    (i : Fin (n.len+1)) :
    (actual_chain_recovery N n F hF hw).hom.app i =
      QuotientRows.completionQuotient V (zeroAugment V F) (zeroAugment_map_cof V F hF)
        (interval 0 i.succ (Fin.zero_le _)) := rfl

def actual_row_factorization (D : RowFactorization.JointData N) :
    FunctorialFactorization (RowWeakEquivalences.coarseStructure N n) :=
  RowFactorization.factorization N D n

theorem actual_row_first_factor_cof (D : RowFactorization.JointData N)
    (f : Arrow (QuotientRows.Obj V n)) :
    QuotientRows.cof V n ((actual_row_factorization N n D).inclusion.app f) :=
  (actual_row_factorization N n D).cofibration f

theorem actual_row_extension (he : ExtensionAxiom N.coarse) :
    ExtensionAxiom (RowWeakEquivalences.coarseStructure N n) :=
  RowWeakEquivalences.extensionAxiom N he n

theorem actual_normalized_row_lifting {m : SimplexCategoryᵒᵖ} (α : m ⟶ op n)
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i)
      (TopCat.ofHom (MappingPath.endpoint (rowNormalizedComparison N α))) :=
  rowNormalizedComparison_endpoint_realization_mono N α i


def actual_weak_filtration_equivalence (he : ExtensionAxiom N.coarse) :
    FineWeakRows N n ≌ FineWeakChains N n := weakFiltrationEquivalence N he n

theorem actual_weak_filtration_forward (he : ExtensionAxiom N.coarse) :
    (weakFiltrationClassifyingHomotopyEquiv N he n).toFun =
      (classifyingSpaceMap (weakFiltrationPresentation N he n)).hom := rfl

theorem actual_weak_filtration_inverse (he : ExtensionAxiom N.coarse) :
    (weakFiltrationClassifyingHomotopyEquiv N he n).invFun =
      (classifyingSpaceMap (weakCompletionFunctor N n)).hom := rfl

section FiberwiseOriginalMaps
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  (p : C(E,B)) (q : C(F,B)) (f : C(E,F)) (sq : q.comp f = p)
  (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
  (hf : ∀ b, CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b))

include p q sq hp hq hf in
theorem actual_total_map_weak : IsWeakHomotopyEquivalence f :=
  isWeakHomotopyEquivalence_of_fiberHELP p q f sq hp hq hf

include p q sq hp hq hf in
theorem actual_total_map_degree_zero (x : E) : Function.Bijective
    (homotopyGroupMap (N := Fin 0) f (x := x) rfl) :=
  (actual_total_map_weak p q f sq hp hq hf).homotopy_bijective x 0
end FiberwiseOriginalMaps

end Consumer

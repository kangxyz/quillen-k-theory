import Quillen.Waldhausen.Fibration.RelativeRows.ProductSection
import Quillen.Waldhausen.Fibration.RelativeRows.InitialCutIso
import Quillen.Waldhausen.Fibration.RelativeRows.FirstTailSSet
import Quillen.Waldhausen.ExtensionCategory.Realization

/-! # Genuine degreewise relative-row additivity

The original first-object/tail functor realizes to a homotopy equivalence.
The inverse is the actual tail-section/fiber coproduct. The difficult inverse
composite follows from the genuine cutoff/identity/tail cofibration sequence,
including its proved Reedy cofibration condition, and actual functor additivity.

Realization is stated in the honest common-universe case. The simplicial
product endpoint uses the genuine product-S isomorphism, without asserting
that ordinary topological realization preserves arbitrary products. No
diagonal homotopy-fiber theorem is claimed here.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RelativeRows

section Categorical
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (n : SimplexCategory)
variable [HasBinaryCoproducts (Obj N n)]

/-- The actual cutoff sum is the original first/tail followed by its split section. -/
def internalSumSplitIso :
    Additivity.sumFunctor (tailQuotientFunctor N n) (cutFunctor N n) ≅
      firstTail N n ⋙ splitFunctor N n := by
  let e : Additivity.sumFunctor (tailQuotientFunctor N n) (cutFunctor N n) ≅
      Additivity.sumFunctor (tailQuotientFunctor N n) (first N n ⋙ fiber N n) :=
    NatIso.ofComponents (fun X ↦
      coprod.mapIso (Iso.refl ((tailQuotientFunctor N n).obj X))
        ((firstFiberCutIso N n).symm.app X)) (by
      intro X Y f
      apply coprod.hom_ext
      · simp only [Additivity.sumFunctor, coprod.mapIso_hom, Iso.refl_hom,
          coprod.inl_map_assoc, coprod.inl_map, Category.id_comp]
      · simp only [Additivity.sumFunctor, coprod.mapIso_hom, coprod.inr_map_assoc, coprod.inr_map]
        simpa only [Category.assoc] using! congrArg (fun a ↦ a ≫ coprod.inr)
          ((firstFiberCutIso N n).inv.naturality f))
  exact e ≪≫ eqToIso (firstTail_splitFunctor N n).symm

end Categorical

variable {C : Type u} [Category.{u} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (n : SimplexCategory)

section ChosenCoproducts
variable [HasBinaryCoproducts (Obj N n)]

/-- Actual relative additivity supplies the original left inverse homotopy. -/
theorem firstTail_split_homotopic :
    ((deloopingMap (splitFunctor_exact N n)).hom.comp
      (deloopingMap (firstTail_exact N n)).hom).Homotopic
      (ContinuousMap.id (waldhausenStructure N n).Delooping) := by
  let W := waldhausenStructure N n
  let P := ExtensionCategory.productStructure V
    (QuotientRows.waldhausenStructure (acyclicStructure N) n)
  have hs := cut_tail_isCofibrationSequence N n
  have ha := Additivity.deloopingMap_additivity W W (cutToId N n) (tailProjection N n) hs
  have hi := ExtensionCategory.deloopingMap_homotopic_of_iso W W
    (Additivity.sumFunctor_isExact W W hs.exactH hs.exactF)
    ((firstTail_exact N n).comp (splitFunctor_exact N n)) (internalSumSplitIso N n)
  have h := (ha.trans hi).symm
  rw [ExtensionCategory.deloopingMap_composition W P W,
    ExtensionCategory.deloopingMap_identity W] at h
  exact h

/-- The original right inverse homotopy is induced by the actual split-pair isomorphism. -/
theorem split_firstTail_homotopic :
    ((deloopingMap (firstTail_exact N n)).hom.comp
      (deloopingMap (splitFunctor_exact N n)).hom).Homotopic
      (ContinuousMap.id (ExtensionCategory.productStructure V
        (QuotientRows.waldhausenStructure (acyclicStructure N) n)).Delooping) := by
  let W := waldhausenStructure N n
  let P := ExtensionCategory.productStructure V
    (QuotientRows.waldhausenStructure (acyclicStructure N) n)
  have h := ExtensionCategory.deloopingMap_homotopic_of_iso P P
    ((splitFunctor_exact N n).comp (firstTail_exact N n))
    (IsExact.id P.cof P.weq) (splitFirstTailIso N n)
  rw [ExtensionCategory.deloopingMap_composition P W P,
    ExtensionCategory.deloopingMap_identity P] at h
  exact h
end ChosenCoproducts

/-- The actual inverse realization map, with coproducts derived from the genuine structure. -/
def splitRealizationMap : C((ExtensionCategory.productStructure V
    (QuotientRows.waldhausenStructure (acyclicStructure N) n)).Delooping,
    (waldhausenStructure N n).Delooping) := by
  letI := Additivity.hasBinaryCoproducts (waldhausenStructure N n)
  exact (deloopingMap (splitFunctor_exact N n)).hom

/-- The original first-object/tail map is a genuine realization homotopy equivalence. -/
def firstTailRealizationHomotopyEquiv : ContinuousMap.HomotopyEquiv
    (waldhausenStructure N n).Delooping
    (ExtensionCategory.productStructure V
      (QuotientRows.waldhausenStructure (acyclicStructure N) n)).Delooping := by
  letI := Additivity.hasBinaryCoproducts (waldhausenStructure N n)
  exact {
    toFun := (deloopingMap (firstTail_exact N n)).hom
    invFun := (deloopingMap (splitFunctor_exact N n)).hom
    left_inv := firstTail_split_homotopic N n
    right_inv := split_firstTail_homotopic N n }

@[simp] theorem firstTailRealizationHomotopyEquiv_toFun :
    (firstTailRealizationHomotopyEquiv N n).toFun =
      (deloopingMap (firstTail_exact N n)).hom := rfl

@[simp] theorem firstTailRealizationHomotopyEquiv_invFun :
    (firstTailRealizationHomotopyEquiv N n).invFun = splitRealizationMap N n := rfl

/-- Degreewise relative additivity into the genuine simplicial product. -/
def firstTailSSetRealizationHomotopyEquiv : ContinuousMap.HomotopyEquiv
    |(relativeSRows N).obj (Opposite.op n)|
    |sSet V.cof V.weq ⊗ (ordinarySRows (acyclicStructure N)).obj (Opposite.op n)| :=
  (firstTailRealizationHomotopyEquiv N n).trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (Product.sSetIso V
      (QuotientRows.waldhausenStructure (acyclicStructure N) n)))).toHomotopyEquiv

/-- The forward map is exactly the originally specified first/tail simplicial map. -/
@[simp] theorem firstTailSSetRealizationHomotopyEquiv_toFun :
    (firstTailSSetRealizationHomotopyEquiv N n).toFun =
      (SSet.toTop.map (firstTailSSet N n)).hom := by
  simp only [firstTailSSetRealizationHomotopyEquiv, firstTailSSet, Functor.map_comp]
  rfl

end Quillen.Waldhausen.Fibration.RelativeRows

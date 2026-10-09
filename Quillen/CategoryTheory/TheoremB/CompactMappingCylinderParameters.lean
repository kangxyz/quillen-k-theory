import Quillen.CategoryTheory.TheoremB.CompactMappingCylinderFibers
import Quillen.Topology.Pushout.CompactParameter
import Quillen.Topology.Maps.SumSubtype

/-! # Exact finite-parameter presentations of mapping cylinders -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology unitInterval
universe u
namespace Quillen.TheoremB.CompactMappingCylinder
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)
  {D : Type u} [TopologicalSpace D] (b : C(D,T))

abbrev SourceStart := {z : A × D // (f ≫ base) z.1 = b z.2}
abbrev TargetStart := {z : C × D // base z.1 = b z.2}
abbrev CylinderStart := {z : M × D // projection sq base z.1 = b z.2}
abbrev StartPieces := (SourceStart (f := f) base b × TopCat.I) ⊕ TargetStart base b

/-- Literal sum presentation of the mapping cylinder matched with a test. -/
def parameterQuotient : C(StartPieces (f := f) base b,CylinderStart sq base b) where
  toFun := Sum.elim
    (fun z ↦ ⟨(l (z.1.1.1,z.2),z.1.1.2),
      (ConcreteCategory.congr_hom (TheoremA.mappingCylinderProjection_cylinder_assoc sq base)
        (z.1.1.1,z.2)).trans z.1.2⟩)
    (fun z ↦ ⟨(c z.1.1,z.1.2),
      (ConcreteCategory.congr_hom (TheoremA.mappingCylinderProjection_target_assoc sq base)
        z.1.1).trans z.2⟩)
  continuous_toFun := by
    apply Continuous.sumElim <;> fun_prop

/-- The sum presentation has the actual pullback topology under the explicit
closed matching-locus hypothesis and a locally compact parameter. -/
theorem parameterQuotient_isQuotientMap [LocallyCompactSpace D]
    (hc : IsClosed (Set.ofPred (fun z : M × D ↦ projection sq base z.1 = b z.2))) :
    IsQuotientMap (parameterQuotient sq base b) := by
  let P := {z : ((A × TopCat.I) ⊕ C) × D //
    projection sq base (Sum.elim l c z.1) = b z.2}
  let pred : ((A × TopCat.I) × D) ⊕ (C × D) → Prop :=
    Sum.elim (fun z ↦ (f ≫ base) z.1.1 = b z.2) (fun z ↦ base z.1 = b z.2)
  let e : C(P,{z // pred z}) := {
    toFun z := ⟨Homeomorph.sumProdDistrib z.1,by
      rcases z with ⟨⟨z | z,d⟩,h⟩
      · exact (ConcreteCategory.congr_hom
          (TheoremA.mappingCylinderProjection_cylinder_assoc sq base) z).symm.trans h
      · exact (ConcreteCategory.congr_hom
          (TheoremA.mappingCylinderProjection_target_assoc sq base) z).symm.trans h⟩
    continuous_toFun := by dsimp only [P]; fun_prop }
  let e' : C(P,({z : (A × TopCat.I) × D // (f ≫ base) z.1.1 = b z.2}) ⊕ TargetStart base b) :=
    ⟨fun z ↦ sumSubtypeHomeomorph pred (e z),
      (sumSubtypeHomeomorph pred).continuous.comp e.continuous⟩
  let left : C({z : (A × TopCat.I) × D // (f ≫ base) z.1.1 = b z.2},
      SourceStart (f := f) base b × TopCat.I) :=
    ⟨fun z ↦ (⟨(z.1.1.1,z.1.2),z.2⟩,z.1.1.2),by fun_prop⟩
  let split : C(P,StartPieces (f := f) base b) :=
    ⟨(Sum.map left id) ∘ e',by fun_prop⟩
  have hQ := pushout_parameter_pullback_quotient_of_isClosed sq (projection sq base) b hc
  have heq : ((parameterQuotient sq base b) : StartPieces (f := f) base b → _ ) ∘ split =
      (fun z : P ↦ (⟨(Sum.elim l c z.1.1,z.1.2),z.2⟩ : CylinderStart sq base b)) := by
    funext z
    rcases z with ⟨⟨z | z,d⟩,h⟩ <;> rfl
  exact IsQuotientMap.of_comp split.continuous (parameterQuotient sq base b).continuous
    (heq.symm ▸ hQ)

end Quillen.TheoremB.CompactMappingCylinder

import Quillen.CategoryTheory.TheoremB.CompactMappingCylinderLiftDescent

/-! # Actual compact-parameter lifting of a fiberwise mapping cylinder

Only the original source/target projections have unrestricted HLP. The
mapping cylinder obtains the displayed compact, locally compact parameter
lifting property by quotient descent over each closed graph separately.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology unitInterval Simplicial
universe u
namespace Quillen.TheoremB.CompactMappingCylinder
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)

/-- Compact locally compact test lifting on the original quotient projection,
assuming the actual relevant test graphs are closed in the unchanged base. -/
theorem compactHomotopyLiftingProperty_of_closedGraphs
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (hgraph : ∀ (D : Type u) [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D]
      (b : C(D,T)),IsClosed (Set.ofPred (fun z : D × T ↦ b z.1 = z.2))) :
    CompactHomotopyLiftingProperty (projection sq base).hom := by
  intro D _ _ _ a H h₀
  let b : C(D,T) := ⟨fun d ↦ H (0,d),by fun_prop⟩
  apply homotopy_lift_of_closed_matching sq base hp hq a H h₀
  have hc := (hgraph D b).preimage
    (continuous_snd.prodMk ((projection sq base).hom.continuous.comp continuous_fst))
  convert hc using 1
  ext z
  exact eq_comm

/-- A genuine homeomorphism of the base to an actual realization supplies
all required compact closed graphs. A mere homotopy equivalence is not used. -/
theorem compactHomotopyLiftingProperty_of_realizationModel
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (X : SSet.{u}) (e : T ≃ₜ |X|) :
    CompactHomotopyLiftingProperty (projection sq base).hom := by
  apply compactHomotopyLiftingProperty_of_closedGraphs sq base hp hq
  intro D _ _ _ b
  have hc := (realization_compactMap_isClosed_graph X ((e : C(T,|X|)).comp b)).preimage
    (continuous_fst.prodMk (e.continuous.comp continuous_snd))
  convert hc using 1
  ext z
  exact e.injective.eq_iff.symm

end Quillen.TheoremB.CompactMappingCylinder

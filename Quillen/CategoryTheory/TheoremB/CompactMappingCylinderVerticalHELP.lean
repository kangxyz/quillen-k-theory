import Quillen.CategoryTheory.TheoremB.CompactMappingCylinderLifting
import Quillen.Topology.HELP.CompactVerticalCancellation
import Quillen.Topology.HELP.ContractibleTestFullOverBase

/-! # Full finite vertical HELP of the original mapping-cylinder source end

The original attaching map supplies the first vertical comparison. The
actual target collapse supplies ordinary compact HELP, and finite base
correction lifts that comparison while preserving the complete side/caps
boundary. No whole-cylinder source deformation is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval Simplicial
universe u
namespace Quillen.TheoremB.CompactMappingCylinder
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)

/-- Full vertical HELP on the displayed compact contracted test, using the
actual finite lifting property of the original cylinder projection. -/
theorem source_fullHELP_over_contracted_test
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (hM : CompactHomotopyLiftingProperty (projection sq base).hom)
    (hf : ∀ t : T,CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t))
    (K D : TopCat.{u}) [CompactSpace K] [CompactSpace D] [LocallyCompactSpace D]
    (i : K ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (d₀ : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d₀))
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (a : C(K,A)) (b : C(D,M))
    (H : (((TopCat.ι₀ ≫ l).hom).comp a).Homotopy (b.comp i.hom))
    (hH : ∀ t x,projection sq base (H (t,x)) = projection sq base (b (i x))) :
    ∃ a' : C(D,A),a'.comp i.hom = a ∧
      (f ≫ base).hom.comp a' = (projection sq base).hom.comp b ∧
      ∃ V : (((TopCat.ι₀ ≫ l).hom).comp a').Homotopy b,
        HomotopyOver ((projection sq base).hom.comp b) (projection sq base).hom V ∧
          ∀ t x,V (t,i x) = H (t,x) := by
  let r : C(M,C) := (TheoremA.mappingCylinderProjection sq).hom
  let j : C(A,M) := (TopCat.ι₀ ≫ l).hom
  have hrj : r.comp j = f.hom := congrArg TopCat.Hom.hom (TheoremA.mappingCylinderProjection_start sq)
  let Hf : (f.hom.comp a).Homotopy ((r.comp b).comp i.hom) :=
    ((ContinuousMap.Homotopy.refl r).comp H).cast (by rw [← hrj]; rfl) rfl
  obtain ⟨a',ha',hbase,J,hJ,hJa⟩ := fullHELP_over_contracted_test
    (f ≫ base).hom base.hom f.hom rfl hp hq hf K D i hi d₀ HD duration hzero
    a (r.comp b) Hf hH
  let H' : ((j.comp a').comp i.hom).Homotopy (b.comp i.hom) :=
    H.cast (by rw [ContinuousMap.comp_assoc,ha']) rfl
  let J' : (r.comp (j.comp a')).Homotopy (r.comp b) :=
    J.cast (by rw [← ContinuousMap.comp_assoc,hrj]) rfl
  have hr : CompactHomotopyExtensionLiftingProperty r := compactHELP_of_homotopyEquiv
    (TheoremA.mappingCylinderTargetStrongDeformationRetract sq).toHomotopyEquiv.symm
  obtain ⟨V,hV,hVa⟩ := compact_vertical_homotopy_lift
    (projection sq base).hom base.hom r rfl hM hq.compact hr
    K D i hi duration hzero (j.comp a') b H' J' hJ hJa
  exact ⟨a',ha',hbase,V,hV,hVa⟩

/-- The geometric realization model discharges the cylinder finite-lifting
input. The forward source map and full prescribed track remain unchanged. -/
theorem source_fullHELP_over_contracted_test_of_realizationModel
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (X : SSet.{u}) (e : T ≃ₜ |X|)
    (hf : ∀ t : T,CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t))
    (K D : TopCat.{u}) [CompactSpace K] [CompactSpace D] [LocallyCompactSpace D]
    (i : K ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (d₀ : D) (HD : (ContinuousMap.id D).Homotopy (ContinuousMap.const D d₀))
    (duration : C(D,unitInterval)) (hzero : ∀ x,duration x = 0 ↔ x ∈ Set.range i)
    (a : C(K,A)) (b : C(D,M))
    (H : (((TopCat.ι₀ ≫ l).hom).comp a).Homotopy (b.comp i.hom))
    (hH : ∀ t x,projection sq base (H (t,x)) = projection sq base (b (i x))) :
    ∃ a' : C(D,A),a'.comp i.hom = a ∧
      (f ≫ base).hom.comp a' = (projection sq base).hom.comp b ∧
      ∃ V : (((TopCat.ι₀ ≫ l).hom).comp a').Homotopy b,
        HomotopyOver ((projection sq base).hom.comp b) (projection sq base).hom V ∧
          ∀ t x,V (t,i x) = H (t,x) :=
  source_fullHELP_over_contracted_test sq base hp hq
    (compactHomotopyLiftingProperty_of_realizationModel sq base hp hq X e)
    hf K D i hi d₀ HD duration hzero a b H hH

end Quillen.TheoremB.CompactMappingCylinder

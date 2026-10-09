import Quillen.CategoryTheory.TheoremB.HomotopyPullbackRestriction
import Quillen.CategoryTheory.TheoremB.RetractionPullback

/-! Homotopy pullbacks over retraction-coordinate charts. -/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.HomotopyPullback

variable {E D T B : TopCat.{u}} (q : E ⟶ T) (p : D ⟶ T) (S : Set D)
  {i : B ⟶ TopCat.of S} (R : TheoremA.CylinderStrongDeformationRetract i)
  (hR : R.H ≫ R.r = fst (TopCat.of S) TopCat.I ≫ R.r)
  (b : B ⟶ T) (hr : restrictedParameter p.hom S = b.hom.comp R.r.hom)

/-- In retraction coordinates, the endpoint homotopy pullback is homotopy
 equivalent to the entire restricted homotopy pullback. -/
def restrictionRetractionHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (HomotopyPullback q.hom b.hom)
      {z : HomotopyPullback q.hom p.hom // baseProjection q.hom p.hom z ∈ S} :=
  (RetractionPullback.homotopyEquiv R
    (TopCat.ofHom (baseProjection q.hom b.hom)) hR).trans
      (retractionChartHomeomorph q.hom p.hom S R.r.hom b.hom hr).symm.toHomotopyEquiv

@[simp] theorem restrictionRetractionHomotopyEquiv_apply
    (z : HomotopyPullback q.hom b.hom) :
    ((restrictionRetractionHomotopyEquiv q p S R hR b hr).toFun z).1.1 =
      ((i z.1.1).1, z.1.2) := rfl

end Quillen.HomotopyPullback

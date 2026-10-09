import Quillen.CategoryTheory.TheoremB.HomotopyPullbackDoubleCylinderMap
import Quillen.CategoryTheory.TheoremB.HomotopyPullbackRetraction
import Quillen.CategoryTheory.TheoremB.OpenCoverInvariance
import Quillen.CategoryTheory.TheoremB.HeightOpenCover

/-! Fixed-target homotopy pullbacks commute, up to a genuine ordinary
homotopy equivalence, with an actual double mapping cylinder. The forward
map retains the source and compact-open path coordinates exactly. -/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.HomotopyPullbackDoubleCylinder
open DoubleCylinder

variable {A B C D E T : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
  (q : E ⟶ T) (b : B ⟶ T) (c : C ⟶ T) (w : f ≫ b = g ≫ c)
  {Z : TopCat.{u}} {lh : HA f q b ⊗ TopCat.I ⟶ Z}
  {eh : TopCat.of (HB q b ⊕ HC q c) ⟶ Z}
  (sqH : IsPushout (TheoremA.intervalEndpoints (HA f q b))
    (DoubleCylinder.endMap (leftLeg f q b) (rightLeg f g q b c w)) lh eh)
  (cut : I)

/-- The fixed parameter on a left collar factors exactly through its retraction. -/
theorem left_parameter_factor (hcut : 0 < cut) :
    HomotopyPullback.restrictedParameter (parameter f g sq b c w).hom
        (leftCollarSet f g sq cut) =
      b.hom.comp (leftCollarProjection f g sq cut hcut).hom := by
  ext x
  rcases Types.eq_or_eq_of_isPushout
    ((leftCollar_isPushout f g sq cut hcut).map (forget TopCat)) x with ⟨z, hz⟩ | ⟨y, hy⟩
  · change leftCollarCylinderInclusion f g sq cut z = x at hz
    subst x
    change parameter f g sq b c w (l z.1) =
      b (leftCollarProjection f g sq cut hcut (leftCollarCylinderInclusion f g sq cut z))
    rw [leftCollarProjection_cylinder]
    exact parameter_cylinder f g sq b c w z.1.1 z.1.2
  · change leftCollarInclusion f g sq cut hcut y = x at hy
    subst x
    change parameter f g sq b c w (e (Sum.inl y)) =
      b (leftCollarProjection f g sq cut hcut (leftCollarInclusion f g sq cut hcut y))
    rw [leftCollarProjection_end, parameter_left]

/-- The fixed parameter on a right collar factors exactly through its retraction. -/
theorem right_parameter_factor (hcut : cut < 1) :
    HomotopyPullback.restrictedParameter (parameter f g sq b c w).hom
        (rightCollarSet f g sq cut) =
      c.hom.comp (rightCollarProjection f g sq cut hcut).hom := by
  ext x
  rcases Types.eq_or_eq_of_isPushout
    ((rightCollar_isPushout f g sq cut hcut).map (forget TopCat)) x with ⟨z, hz⟩ | ⟨y, hy⟩
  · change rightCollarCylinderInclusion f g sq cut z = x at hz
    subst x
    change parameter f g sq b c w (l z.1) =
      c (rightCollarProjection f g sq cut hcut (rightCollarCylinderInclusion f g sq cut z))
    rw [rightCollarProjection_cylinder]
    exact (parameter_cylinder f g sq b c w z.1.1 z.1.2).trans
      (ConcreteCategory.congr_hom w z.1.1)
  · change rightCollarInclusion f g sq cut hcut y = x at hy
    subst x
    change parameter f g sq b c w (e (Sum.inr y)) =
      c (rightCollarProjection f g sq cut hcut (rightCollarInclusion f g sq cut hcut y))
    rw [rightCollarProjection_end, parameter_right]

abbrev LeftTarget :=
  {z : Target f g sq q b c w // z.1.1 ∈ leftCollarSet f g sq cut}
abbrev RightTarget :=
  {z : Target f g sq q b c w // z.1.1 ∈ rightCollarSet f g sq cut}

/-- The actual canonical comparison restricted to the left height collar. -/
def leftRestriction :
    C(LeftCollar (leftLeg f q b) (rightLeg f g q b c w) sqH cut,
      LeftTarget f g sq q b c w cut) :=
  ⟨fun x ↦ ⟨comparison f g sq q b c w sqH x.1, by
    change height f g sq (comparison f g sq q b c w sqH x.1).1.1 < cut
    rw [height_comparison]
    exact x.2⟩, by fun_prop⟩

/-- The actual canonical comparison restricted to the right height collar. -/
def rightRestriction :
    C(RightCollar (leftLeg f q b) (rightLeg f g q b c w) sqH cut,
      RightTarget f g sq q b c w cut) :=
  ⟨fun x ↦ ⟨comparison f g sq q b c w sqH x.1, by
    change cut < height f g sq (comparison f g sq q b c w sqH x.1).1.1
    rw [height_comparison]
    exact x.2⟩, by fun_prop⟩

/-- The canonical left collar restriction is an actual homotopy equivalence. -/
def leftRestrictionHomotopyEquiv (hcut : 0 < cut) :
    ContinuousMap.HomotopyEquiv
      (LeftCollar (leftLeg f q b) (rightLeg f g q b c w) sqH cut)
      (LeftTarget f g sq q b c w cut) := by
  let S := leftCollarStrongDeformationRetract
    (leftLeg f q b) (rightLeg f g q b c w) sqH cut hcut
  let R := leftCollarStrongDeformationRetract f g sq cut hcut
  let eT := HomotopyPullback.restrictionRetractionHomotopyEquiv
    q (parameter f g sq b c w) (leftCollarSet f g sq cut) R
    (leftCollarDeformation_projection sq cut hcut) b
    (left_parameter_factor f g sq b c w cut hcut)
  apply TheoremA.homotopyEquivOfTriangle S.toHomotopyEquiv eT
    (leftRestriction f g sq q b c w sqH cut)
  have h : (leftRestriction f g sq q b c w sqH cut).comp S.toHomotopyEquiv.toFun =
      eT.toFun := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    exact comparison_left f g sq q b c w sqH z
  rw [h]

/-- The canonical right collar restriction is an actual homotopy equivalence. -/
def rightRestrictionHomotopyEquiv (hcut : cut < 1) :
    ContinuousMap.HomotopyEquiv
      (RightCollar (leftLeg f q b) (rightLeg f g q b c w) sqH cut)
      (RightTarget f g sq q b c w cut) := by
  let S := rightCollarStrongDeformationRetract
    (leftLeg f q b) (rightLeg f g q b c w) sqH cut hcut
  let R := rightCollarStrongDeformationRetract f g sq cut hcut
  let eT := HomotopyPullback.restrictionRetractionHomotopyEquiv
    q (parameter f g sq b c w) (rightCollarSet f g sq cut) R
    (rightCollarDeformation_projection sq cut hcut) c
    (right_parameter_factor f g sq b c w cut hcut)
  apply TheoremA.homotopyEquivOfTriangle S.toHomotopyEquiv eT
    (rightRestriction f g sq q b c w sqH cut)
  have h : (rightRestriction f g sq q b c w sqH cut).comp S.toHomotopyEquiv.toFun =
      eT.toFun := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    exact comparison_right f g sq q b c w sqH z
  rw [h]

@[simp] theorem leftRestrictionHomotopyEquiv_toFun (hcut : 0 < cut) :
    (leftRestrictionHomotopyEquiv f g sq q b c w sqH cut hcut).toFun =
      leftRestriction f g sq q b c w sqH cut := rfl

@[simp] theorem rightRestrictionHomotopyEquiv_toFun (hcut : cut < 1) :
    (rightRestrictionHomotopyEquiv f g sq q b c w sqH cut hcut).toFun =
      rightRestriction f g sq q b c w sqH cut := rfl

/-- Fixed-target homotopy pullback commutes with a double mapping cylinder.
The proof uses the genuine collar retractions and the exact middle-band
homeomorphism, then glues the canonical restrictions over a two-open cover. -/
def comparisonHomotopyEquiv :
    ContinuousMap.HomotopyEquiv Z (Target f g sq q b c w) := by
  let hi : I := ⟨3 / 4, by constructor <;> norm_num⟩
  let lo : I := ⟨1 / 4, by constructor <;> norm_num⟩
  let k := (comparison f g sq q b c w sqH).hom
  let P := TwoOpenPartition.ofHeight ((height f g sq).comp
    (HomotopyPullback.baseProjection q.hom (parameter f g sq b c w).hom))
  let sL : (P.pullback k).Left ≃ₜ
      LeftCollar (leftLeg f q b) (rightLeg f g q b c w) sqH hi :=
    Homeomorph.setCongr (by
      ext x
      change (height f g sq (comparison f g sq q b c w sqH x).1.1 : ℝ) < 3 / 4 ↔ _
      rw [height_comparison]
      rfl)
  let sR : (P.pullback k).Right ≃ₜ
      RightCollar (leftLeg f q b) (rightLeg f g q b c w) sqH lo :=
    Homeomorph.setCongr (by
      ext x
      change 1 / 4 < (height f g sq (comparison f g sq q b c w sqH x).1.1 : ℝ) ↔ _
      rw [height_comparison]
      rfl)
  let sO : (P.pullback k).Overlap ≃ₜ
      BandSpace (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi :=
    Homeomorph.setCongr (by
      ext x
      change ((height f g sq (comparison f g sq q b c w sqH x).1.1 : ℝ) < 3 / 4 ∧
        1 / 4 < (height f g sq (comparison f g sq q b c w sqH x).1.1 : ℝ)) ↔ _
      rw [height_comparison]
      exact and_comm)
  let tO : TargetBand f g sq q b c w lo hi ≃ₜ P.Overlap :=
    Homeomorph.setCongr (by
      ext x
      exact and_comm)
  let eL : ContinuousMap.HomotopyEquiv (P.pullback k).Left P.Left :=
    sL.toHomotopyEquiv.trans
      (leftRestrictionHomotopyEquiv f g sq q b c w sqH hi (by change (0 : ℝ) < 3 / 4; norm_num))
  let eR : ContinuousMap.HomotopyEquiv (P.pullback k).Right P.Right :=
    sR.toHomotopyEquiv.trans
      (rightRestrictionHomotopyEquiv f g sq q b c w sqH lo (by change (1 : ℝ) / 4 < 1; norm_num))
  let eO : ContinuousMap.HomotopyEquiv (P.pullback k).Overlap P.Overlap :=
    sO.toHomotopyEquiv.trans
      ((bandComparisonHomotopyEquiv f g sq q b c w sqH lo hi).trans tO.toHomotopyEquiv)
  apply P.homotopyEquivOfRestrictions k eL (by rfl) eR (by rfl) eO
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change ((bandComparisonHomotopyEquiv f g sq q b c w sqH lo hi).toFun (sO x)).1 = k x.1
  rw [bandComparisonHomotopyEquiv_toFun]
  rfl

@[simp] theorem comparisonHomotopyEquiv_toFun :
    (comparisonHomotopyEquiv f g sq q b c w sqH).toFun =
      (comparison f g sq q b c w sqH).hom := rfl

end Quillen.HomotopyPullbackDoubleCylinder

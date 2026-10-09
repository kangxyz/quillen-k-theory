import Quillen.CategoryTheory.TheoremB.MappingCylinderTargetCollar
import Quillen.CategoryTheory.TheoremB.NormalizedFibrationSpan

/-! # The original target-end open collar of a two-cylinder bridge

A height on the first cylinder, extended by zero across the second, isolates
an actual open target collar. Its SDR is the unchanged restricted target
cylinder deformation, transported through an actual open-pushout chart.
No equivalence or lifting property of either attaching map is required.
-/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.TheoremB.FiberwiseBridgeTargetCollar

/-- An open pushout chart whose other corner is empty is the original left
corner, with its actual subspace topology. -/
private def leftOnlyHomeomorph {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (U : Set D) (hU : IsOpen U) (hj : ∀ x,j x ∉ U) :
    OpenPushout.left (g := g) U ≃ₜ U := by
  let empty (x : OpenPushout.right (j := j) U) : False := hj x.val x.property
  let e : OpenPushout.right (j := j) U ⟶ OpenPushout.left (g := g) U :=
    TopCat.ofHom ⟨fun x ↦ False.elim (empty x),
      continuous_iff_continuousAt.mpr (fun x ↦ False.elim (empty x))⟩
  let R := OpenPushout.desc sq U (𝟙 _) e (by
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim (empty (OpenPushout.rightLeg sq U x))) hU
  have hl : OpenPushout.leftInclusion (g := g) U ≫ R = 𝟙 _ := OpenPushout.left_desc _ _ _ _ _ _
  have hr : R ≫ OpenPushout.leftInclusion (g := g) U = 𝟙 _ := by
    apply OpenPushout.hom_ext sq U
    · rw [← Category.assoc,hl,Category.id_comp,Category.comp_id]
    · apply ConcreteCategory.hom_ext
      intro x
      exact False.elim (empty x)
  exact TopCat.homeoOfIso {
    hom := OpenPushout.leftInclusion (g := g) U
    inv := R
    hom_inv_id := hl
    inv_hom_id := hr }

variable {A B C M N Z T : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {lM : A ⊗ TopCat.I ⟶ M} {cM : B ⟶ M}
  {lN : A ⊗ TopCat.I ⟶ N} {cN : C ⟶ N}
  (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f lM cM)
  {m : M ⟶ Z} {n : N ⟶ Z}
  (sq : IsPushout (TopCat.ι₀ ≫ lM) (TopCat.ι₀ ≫ lN) m n)

def heightMap : Z ⟶ TopCat.I := sq.desc (MappingCylinderTargetCollar.heightMap sqM)
  (TopCat.ofHom (ContinuousMap.const N (ULift.up (0 : I)))) (by
    apply ConcreteCategory.hom_ext
    intro a
    apply ULift.ext
    exact MappingCylinderTargetCollar.height_start sqM a)

def height : C(Z,I) := ⟨fun z ↦ (heightMap sqM sq z).down,by fun_prop⟩

@[reassoc (attr := simp)] theorem heightMap_left :
    m ≫ heightMap sqM sq = MappingCylinderTargetCollar.heightMap sqM := sq.inl_desc _ _ _
@[reassoc (attr := simp)] theorem heightMap_right :
    n ≫ heightMap sqM sq = TopCat.ofHom (ContinuousMap.const N (ULift.up (0 : I))) := sq.inr_desc _ _ _
@[simp] theorem height_left (x : M) : height sqM sq (m x) = MappingCylinderTargetCollar.height sqM x :=
  congrArg ULift.down (ConcreteCategory.congr_hom (heightMap_left sqM sq) x)
@[simp] theorem height_right (x : N) : height sqM sq (n x) = 0 :=
  congrArg ULift.down (ConcreteCategory.congr_hom (heightMap_right sqM sq) x)
@[simp] theorem height_target (x : B) : height sqM sq ((cM ≫ m) x) = 1 := by
  change height sqM sq (m (cM x)) = 1
  rw [height_left,MappingCylinderTargetCollar.height_target]

variable (cut : I)
def collarSet : Set Z := {z | cut < height sqM sq z}
theorem collar_isOpen : IsOpen (collarSet sqM sq cut) :=
  isOpen_lt continuous_const (height sqM sq).continuous
abbrev Collar : TopCat.{u} := TopCat.of (collarSet sqM sq cut)
def inclusion : Collar sqM sq cut ⟶ Z := TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

def collarHomeomorph : MappingCylinderTargetCollar.Collar sqM cut ≃ₜ Collar sqM sq cut :=
  (Homeomorph.setCongr (by
    ext x
    change cut < MappingCylinderTargetCollar.height sqM x ↔ cut < height sqM sq (m x)
    rw [height_left])).trans
  (leftOnlyHomeomorph sq (collarSet sqM sq cut) (collar_isOpen sqM sq cut) (by
    intro x hx
    change cut < height sqM sq (n x) at hx
    rw [height_right] at hx
    exact (not_lt_of_ge cut.property.1) hx))

@[simp] theorem collarHomeomorph_val (x : MappingCylinderTargetCollar.Collar sqM cut) :
    (collarHomeomorph sqM sq cut x).val = m x.val := rfl

/-- The original left target inclusion, now landing in its actual open collar. -/
def target (hcut : cut < 1) : B ⟶ Collar sqM sq cut :=
  MappingCylinderTargetCollar.target sqM cut hcut ≫
    (TopCat.isoOfHomeo (collarHomeomorph sqM sq cut)).hom
@[simp] theorem target_val (hcut : cut < 1) (b : B) :
    (target sqM sq cut hcut b).val = m (cM b) := rfl
@[reassoc (attr := simp)] theorem target_inclusion (hcut : cut < 1) :
    target sqM sq cut hcut ≫ inclusion sqM sq cut = cM ≫ m := rfl

/-- Genuine SDR of the collar onto the original left target. -/
def strongDeformationRetract (hcut : cut < 1) :
    TheoremA.CylinderStrongDeformationRetract (target sqM sq cut hcut) where
  r := (TopCat.isoOfHomeo (collarHomeomorph sqM sq cut)).inv ≫
    (MappingCylinderTargetCollar.strongDeformationRetract sqM cut hcut).r
  retract := by
    simp only [target,Category.assoc,← Category.assoc (TopCat.isoOfHomeo _).hom,
      Iso.hom_inv_id,Category.id_comp]
    exact (MappingCylinderTargetCollar.strongDeformationRetract sqM cut hcut).retract
  H := TopCat.ofHom ⟨fun z ↦ collarHomeomorph sqM sq cut
    ((MappingCylinderTargetCollar.strongDeformationRetract sqM cut hcut).H
      ((collarHomeomorph sqM sq cut).symm z.1,z.2)),by fun_prop⟩
  H₀ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (collarHomeomorph sqM sq cut)
      (ConcreteCategory.congr_hom (MappingCylinderTargetCollar.strongDeformationRetract sqM cut hcut).H₀
        ((collarHomeomorph sqM sq cut).symm x))
  H₁ := by
    apply ConcreteCategory.hom_ext
    intro x
    change collarHomeomorph sqM sq cut
      ((MappingCylinderTargetCollar.strongDeformationRetract sqM cut hcut).H
        ((collarHomeomorph sqM sq cut).symm x,ULift.up 1)) = x
    exact (congrArg (collarHomeomorph sqM sq cut)
      (ConcreteCategory.congr_hom (MappingCylinderTargetCollar.strongDeformationRetract sqM cut hcut).H₁
        ((collarHomeomorph sqM sq cut).symm x))).trans
      ((collarHomeomorph sqM sq cut).apply_symm_apply x)
  fixed := by
    apply ConcreteCategory.hom_ext
    rintro ⟨b,t⟩
    change collarHomeomorph sqM sq cut
      ((MappingCylinderTargetCollar.strongDeformationRetract sqM cut hcut).H
        ((collarHomeomorph sqM sq cut).symm (collarHomeomorph sqM sq cut
          (MappingCylinderTargetCollar.target sqM cut hcut b)),t)) = _
    rw [(collarHomeomorph sqM sq cut).symm_apply_apply]
    exact congrArg (collarHomeomorph sqM sq cut)
      (ConcreteCategory.congr_hom (MappingCylinderTargetCollar.strongDeformationRetract sqM cut hcut).fixed (b,t))

variable (sqN : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) g lN cN)
  (b : B ⟶ T) (c : C ⟶ T) (w : f ≫ b = g ≫ c)

/-- The entire original collar deformation remains over the unchanged bridge base. -/
theorem deformation_over (hcut : cut < 1) :
    (strongDeformationRetract sqM sq cut hcut).H ≫ inclusion sqM sq cut ≫
        FiberwiseBridge.projection sqM sqN sq b c w =
      fst (Collar sqM sq cut) TopCat.I ≫ inclusion sqM sq cut ≫
        FiberwiseBridge.projection sqM sqN sq b c w := by
  apply ConcreteCategory.hom_ext
  rintro ⟨z,t⟩
  let x := (collarHomeomorph sqM sq cut).symm z
  have hz : m x.val = z.val := congrArg Subtype.val ((collarHomeomorph sqM sq cut).apply_symm_apply z)
  change FiberwiseBridge.projection sqM sqN sq b c w
    (m (((MappingCylinderTargetCollar.strongDeformationRetract sqM cut hcut).H (x,t)).val)) =
      FiberwiseBridge.projection sqM sqN sq b c w z.val
  rw [← hz]
  exact (ConcreteCategory.congr_hom (FiberwiseBridge.projection_left sqM sqN sq b c w) _).trans
    ((ConcreteCategory.congr_hom (MappingCylinderTargetCollar.deformation_over sqM cut hcut b) (x,t)).trans
      (ConcreteCategory.congr_hom (FiberwiseBridge.projection_left sqM sqN sq b c w) _).symm)

end Quillen.TheoremB.FiberwiseBridgeTargetCollar


namespace Quillen.NormalizedFibrationSpan.Data
open TheoremB
variable {T : TopCat.{u}} {U V : Set T} (d : NormalizedFibrationSpan.Data T U V)

/-- Actual left target height, zero on the entire right cylinder. -/
def bridgeTargetHeight : C(d.Bridge,I) :=
  FiberwiseBridgeTargetCollar.height d.cylinder0 d.bridge_isPushout
@[simp] theorem bridgeTargetHeight_left (x : d.M0) :
    d.bridgeTargetHeight (d.bridge0 x) = MappingCylinderTargetCollar.height d.cylinder0 x :=
  FiberwiseBridgeTargetCollar.height_left d.cylinder0 d.bridge_isPushout x
@[simp] theorem bridgeTargetHeight_right (x : d.M1) : d.bridgeTargetHeight (d.bridge1 x) = 0 :=
  FiberwiseBridgeTargetCollar.height_right d.cylinder0 d.bridge_isPushout x
@[simp] theorem bridgeTargetHeight_target (x : d.Q0) :
    d.bridgeTargetHeight (d.normalized.i0 x) = 1 :=
  FiberwiseBridgeTargetCollar.height_target d.cylinder0 d.bridge_isPushout x

abbrev BridgeTargetCollar (cut : I) : TopCat.{u} :=
  FiberwiseBridgeTargetCollar.Collar d.cylinder0 d.bridge_isPushout cut
abbrev bridgeTargetCollarInclusion (cut : I) : d.BridgeTargetCollar cut ⟶ d.Bridge :=
  FiberwiseBridgeTargetCollar.inclusion d.cylinder0 d.bridge_isPushout cut
abbrev bridgeTargetCollarTarget (cut : I) (hcut : cut < 1) : d.Q0 ⟶ d.BridgeTargetCollar cut :=
  FiberwiseBridgeTargetCollar.target d.cylinder0 d.bridge_isPushout cut hcut
@[simp] theorem bridgeTargetCollarTarget_val (cut : I) (hcut : cut < 1) (x : d.Q0) :
    (d.bridgeTargetCollarTarget cut hcut x).val = d.normalized.i0 x := rfl
@[reassoc (attr := simp)] theorem bridgeTargetCollarTarget_inclusion (cut : I) (hcut : cut < 1) :
    d.bridgeTargetCollarTarget cut hcut ≫ d.bridgeTargetCollarInclusion cut = d.normalized.i0 := rfl

theorem bridgeTargetCollar_isOpen (cut : I) : IsOpen {z : d.Bridge | cut < d.bridgeTargetHeight z} :=
  FiberwiseBridgeTargetCollar.collar_isOpen d.cylinder0 d.bridge_isPushout cut

def bridgeTargetCollarSDR (cut : I) (hcut : cut < 1) :
    TheoremA.CylinderStrongDeformationRetract (d.bridgeTargetCollarTarget cut hcut) :=
  FiberwiseBridgeTargetCollar.strongDeformationRetract d.cylinder0 d.bridge_isPushout cut hcut

theorem bridgeTargetCollarSDR_over (cut : I) (hcut : cut < 1) :
    (d.bridgeTargetCollarSDR cut hcut).H ≫ d.bridgeTargetCollarInclusion cut ≫ d.bridgeProjection =
      fst (d.BridgeTargetCollar cut) TopCat.I ≫ d.bridgeTargetCollarInclusion cut ≫ d.bridgeProjection :=
  FiberwiseBridgeTargetCollar.deformation_over d.cylinder0 d.bridge_isPushout cut
    d.cylinder1 d.q0 d.q1 d.square hcut
end Quillen.NormalizedFibrationSpan.Data

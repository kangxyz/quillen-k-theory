import Quillen.CategoryTheory.TheoremB.FiberwiseBridgeTargetCollar
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.CategoryTheory.TheoremB.MappingCylinderTargetCollar,
    `Quillen.CategoryTheory.TheoremB.FiberwiseBridgeTargetCollar]
  let mut counts := #[0,0]
  for (name,_) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some k := targets.toList.idxOf? env.header.moduleNames[index.toNat]! | continue
    counts := counts.modify k (· + 1)
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless counts == #[37,57] do
    throwError "Unexpected target bridge collar origin counts: {counts}"
  logInfo m!"Audited all 94 target bridge collar origins: {counts}."
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Quillen
open scoped Topology unitInterval
open unitInterval
universe u
section Cylinder
open Quillen.TheoremB.MappingCylinderTargetCollar
variable {A B M T : TopCat.{u}} {f : A ⟶ B}
  {l : A ⊗ TopCat.I ⟶ M} {c : B ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
  (cut : I) (hc : cut < 1)
example (a : A) (t : I) : height sq (l (a,ULift.up t)) = t := height_cylinder sq _
example (b : B) : height sq (c b) = 1 := height_target sq b
example (a : A) : height sq ((TopCat.ι₀ ≫ l) a) = 0 := height_start sq a
example (x : M) (t : I) :
    height sq ((TheoremA.mappingCylinderTargetStrongDeformationRetract sq).H (x,ULift.up t)) =
      TheoremA.intervalSlide (σ t) (height sq x) := height_deformation sq x _
example (x : M) (t : I) :
    height sq x ≤ height sq ((TheoremA.mappingCylinderTargetStrongDeformationRetract sq).H (x,ULift.up t)) :=
  height_le_deformation sq x _
example : IsOpen (collarSet sq cut) := collar_isOpen sq cut
example (b : B) : (target sq cut hc b).val = c b := rfl
example (x : Collar sq cut) :
    (strongDeformationRetract sq cut hc).r x = TheoremA.mappingCylinderProjection sq x.val := rfl
example (x : Collar sq cut) (t : I) :
    ((strongDeformationRetract sq cut hc).H (x,ULift.up t)).val =
      (TheoremA.mappingCylinderTargetStrongDeformationRetract sq).H (x.val,ULift.up t) := rfl
example (base : B ⟶ T) :
    (strongDeformationRetract sq cut hc).H ≫ inclusion sq cut ≫ TheoremA.mappingCylinderProjection sq ≫ base =
      fst (Collar sq cut) TopCat.I ≫ inclusion sq cut ≫ TheoremA.mappingCylinderProjection sq ≫ base :=
  deformation_over sq cut hc base
example : (strongDeformationRetract sq cut hc).toHomotopyEquiv.toFun = (target sq cut hc).hom := rfl
end Cylinder
section Bridge
open Quillen.TheoremB.FiberwiseBridgeTargetCollar
variable {A B C M N Z T : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {lM : A ⊗ TopCat.I ⟶ M} {cM : B ⟶ M}
  {lN : A ⊗ TopCat.I ⟶ N} {cN : C ⟶ N}
  (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f lM cM)
  {m : M ⟶ Z} {n : N ⟶ Z}
  (sq : IsPushout (TopCat.ι₀ ≫ lM) (TopCat.ι₀ ≫ lN) m n)
  (cut : I) (hc : cut < 1)
example (b : B) : height sqM sq ((cM ≫ m) b) = 1 := height_target sqM sq b
example (x : N) : height sqM sq (n x) = 0 := height_right sqM sq x
example (x : TheoremB.MappingCylinderTargetCollar.Collar sqM cut) :
    (collarHomeomorph sqM sq cut x).val = m x.val := rfl
example (x : Collar sqM sq cut) :
    collarHomeomorph sqM sq cut ((collarHomeomorph sqM sq cut).symm x) = x :=
  (collarHomeomorph sqM sq cut).apply_symm_apply x
example (b : B) : (target sqM sq cut hc b).val = m (cM b) := rfl
example : target sqM sq cut hc ≫ (strongDeformationRetract sqM sq cut hc).r = 𝟙 B :=
  (strongDeformationRetract sqM sq cut hc).retract
example (x : N) : n x ∉ collarSet sqM sq cut := by
  intro h
  change cut < height sqM sq (n x) at h
  rw [height_right] at h
  exact (not_lt_of_ge cut.property.1) h
example (sqN : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) g lN cN)
    (b : B ⟶ T) (c : C ⟶ T) (w : f ≫ b = g ≫ c) :
    (strongDeformationRetract sqM sq cut hc).H ≫ inclusion sqM sq cut ≫
        TheoremB.FiberwiseBridge.projection sqM sqN sq b c w =
      fst (Collar sqM sq cut) TopCat.I ≫ inclusion sqM sq cut ≫
        TheoremB.FiberwiseBridge.projection sqM sqN sq b c w :=
  deformation_over sqM sq cut sqN b c w hc
end Bridge
section Normalized
variable {T : TopCat.{u}} {U V : Set T} (d : NormalizedFibrationSpan.Data T U V)
  (cut : I) (hc : cut < 1)
example (x : d.M1) : d.bridgeTargetHeight (d.bridge1 x) = 0 := d.bridgeTargetHeight_right x
example (x : d.Q0) : d.bridgeTargetHeight (d.normalized.i0 x) = 1 := d.bridgeTargetHeight_target x
example : d.bridgeTargetCollarTarget cut hc ≫ d.bridgeTargetCollarInclusion cut = d.normalized.i0 := rfl
example : IsOpen {z : d.Bridge | cut < d.bridgeTargetHeight z} := d.bridgeTargetCollar_isOpen cut
example : (d.bridgeTargetCollarSDR cut hc).toHomotopyEquiv.toFun =
    (d.bridgeTargetCollarTarget cut hc).hom := rfl
example : (d.bridgeTargetCollarSDR cut hc).H ≫ d.bridgeTargetCollarInclusion cut ≫ d.bridgeProjection =
    fst (d.BridgeTargetCollar cut) TopCat.I ≫ d.bridgeTargetCollarInclusion cut ≫ d.bridgeProjection :=
  d.bridgeTargetCollarSDR_over cut hc
example [IsEmpty d.Q0] : IsEmpty (d.BridgeTargetCollar cut) :=
  ⟨fun x ↦ isEmptyElim ((d.bridgeTargetCollarSDR cut hc).r x)⟩
example (x : d.Q0) : (d.bridgeTargetCollarTarget 0 (by norm_num) x).val = d.normalized.i0 x := rfl
end Normalized

section IndependentCylinderEndpoints
open Quillen.TheoremB.MappingCylinderTargetCollar
variable {A B M : TopCat.{u}} {f : A ⟶ B}
  {l : A ⊗ TopCat.I ⟶ M} {c : B ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c)
  (cut : I) (hc : cut < 1)
example (b : B) : heightMap sq (c b) = ULift.up (1 : I) :=
  ConcreteCategory.congr_hom (heightMap_target sq) b
example (x : Collar sq cut) :
    (strongDeformationRetract sq cut hc).H (x,ULift.up (0 : I)) =
      target sq cut hc ((strongDeformationRetract sq cut hc).r x) :=
  ConcreteCategory.congr_hom (strongDeformationRetract sq cut hc).H₀ x
example (x : Collar sq cut) :
    (strongDeformationRetract sq cut hc).H (x,ULift.up (1 : I)) = x :=
  ConcreteCategory.congr_hom (strongDeformationRetract sq cut hc).H₁ x
example (b : B) (t : I) :
    (strongDeformationRetract sq cut hc).H (target sq cut hc b,ULift.up t) =
      target sq cut hc b :=
  ConcreteCategory.congr_hom (strongDeformationRetract sq cut hc).fixed (b,ULift.up t)
end IndependentCylinderEndpoints
section IndependentNormalizedEndpoints
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : TopCat.{u}} {U V : Set T} (d : NormalizedFibrationSpan.Data T U V)
  (cut : I) (hc : cut < 1)
example (x : d.M1) : ¬ cut < d.bridgeTargetHeight (d.bridge1 x) := by
  rw [d.bridgeTargetHeight_right]
  exact not_lt_of_ge cut.property.1
example : IsEmpty (d.BridgeTargetCollar 1) := by
  constructor
  intro z
  exact (not_lt_of_ge (d.bridgeTargetHeight z.val).property.2) z.property
example (x : d.BridgeTargetCollar cut) (t : I) :
    d.bridgeProjection (((d.bridgeTargetCollarSDR cut hc).H (x,ULift.up t)).val) =
      d.bridgeProjection x.val := by
  have h := ConcreteCategory.congr_hom (d.bridgeTargetCollarSDR_over cut hc) (x,ULift.up t)
  exact h
example (x : d.Q0) :
    d.bridgeTargetCollarInclusion cut ((d.bridgeTargetCollarSDR cut hc).toHomotopyEquiv.toFun x) =
      d.normalized.i0 x := rfl
example (x : d.BridgeTargetCollar cut) :
    d.bridge0 ((TheoremB.FiberwiseBridgeTargetCollar.collarHomeomorph
      d.cylinder0 d.bridge_isPushout cut).symm x).val = x.val :=
  congrArg Subtype.val ((TheoremB.FiberwiseBridgeTargetCollar.collarHomeomorph
    d.cylinder0 d.bridge_isPushout cut).apply_symm_apply x)
end IndependentNormalizedEndpoints

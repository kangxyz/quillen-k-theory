import Quillen.CategoryTheory.TheoremB.HomotopyPullbackRestriction
import Quillen.CategoryTheory.TheoremB.DoubleCylinderLocalComparison
import Quillen.CategoryTheory.TheoremB.DoubleCylinderBand

/-! The fixed-target homotopy-pullback comparison for actual double cylinders,
retaining the entire compact-open path coordinate. -/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.HomotopyPullbackDoubleCylinder

variable {A B C D E T : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
  (q : E ⟶ T) (b : B ⟶ T) (c : C ⟶ T) (w : f ≫ b = g ≫ c)

def parameterEnds : TopCat.of (B ⊕ C) ⟶ T :=
  TopCat.ofHom ⟨Sum.elim b c, continuous_sum_dom.mpr ⟨b.hom.continuous, c.hom.continuous⟩⟩

include w in
theorem parameter_square :
    TheoremA.intervalEndpoints A ≫ (fst A TopCat.I ≫ f ≫ b) =
      DoubleCylinder.endMap f g ≫ parameterEnds b c := by
  apply ConcreteCategory.hom_ext
  intro x
  cases x with
  | inl a => rfl
  | inr a => exact ConcreteCategory.congr_hom w a

/-- The common parameter map, constant along each cylinder segment. -/
def parameter : D ⟶ T :=
  sq.desc (fst A TopCat.I ≫ f ≫ b) (parameterEnds b c) (parameter_square f g b c w)

@[simp] theorem parameter_cylinder (a : A) (t : TopCat.I) :
    parameter f g sq b c w (l (a, t)) = b (f a) :=
  ConcreteCategory.congr_hom (sq.inl_desc _ _ _) (a, t)

@[simp] theorem parameter_left (x : B) :
    parameter f g sq b c w (e (Sum.inl x)) = b x :=
  ConcreteCategory.congr_hom (sq.inr_desc _ _ _) (Sum.inl x)

@[simp] theorem parameter_right (x : C) :
    parameter f g sq b c w (e (Sum.inr x)) = c x :=
  ConcreteCategory.congr_hom (sq.inr_desc _ _ _) (Sum.inr x)

abbrev HA : TopCat.{u} := TopCat.of (HomotopyPullback q.hom (f ≫ b).hom)
abbrev HB : TopCat.{u} := TopCat.of (HomotopyPullback q.hom b.hom)
abbrev HC : TopCat.{u} := TopCat.of (HomotopyPullback q.hom c.hom)

/-- The left leg leaves the source and path coordinates unchanged. -/
def leftLeg : HA f q b ⟶ HB q b :=
  TopCat.ofHom ⟨fun z ↦ ⟨(f z.1.1, z.1.2), z.2⟩, by fun_prop⟩

/-- The right leg leaves the source and path coordinates unchanged. -/
def rightLeg : HA f q b ⟶ HC q c :=
  TopCat.ofHom ⟨fun z ↦ ⟨(g z.1.1, z.1.2), z.2.1,
    z.2.2.trans (ConcreteCategory.congr_hom w z.1.1)⟩, by fun_prop⟩

@[simp] theorem leftLeg_val (z : HA f q b) : (leftLeg f q b z).1 =
    (f z.1.1, z.1.2) := rfl

@[simp] theorem rightLeg_val (z : HA f q b) : (rightLeg f g q b c w z).1 =
    (g z.1.1, z.1.2) := rfl

abbrev Target : TopCat.{u} :=
  TopCat.of (HomotopyPullback q.hom (parameter f g sq b c w).hom)

def cylinderComparison : HA f q b ⊗ TopCat.I ⟶ Target f g sq q b c w :=
  TopCat.ofHom ⟨fun z ↦ ⟨(l (z.1.1.1, z.2), z.1.1.2), z.1.2.1,
    z.1.2.2.trans (parameter_cylinder f g sq b c w z.1.1.1 z.2).symm⟩, by fun_prop⟩

def leftComparison : HB q b ⟶ Target f g sq q b c w :=
  TopCat.ofHom ⟨fun z ↦ ⟨(e (Sum.inl z.1.1), z.1.2), z.2.1,
    z.2.2.trans (parameter_left f g sq b c w z.1.1).symm⟩, by fun_prop⟩

def rightComparison : HC q c ⟶ Target f g sq q b c w :=
  TopCat.ofHom ⟨fun z ↦ ⟨(e (Sum.inr z.1.1), z.1.2), z.2.1,
    z.2.2.trans (parameter_right f g sq b c w z.1.1).symm⟩, by fun_prop⟩

def endsComparison : TopCat.of (HB q b ⊕ HC q c) ⟶ Target f g sq q b c w :=
  TopCat.ofHom ⟨Sum.elim (leftComparison f g sq q b c w) (rightComparison f g sq q b c w),
    continuous_sum_dom.mpr ⟨(leftComparison f g sq q b c w).hom.continuous,
      (rightComparison f g sq q b c w).hom.continuous⟩⟩

theorem comparison_square :
    TheoremA.intervalEndpoints (HA f q b) ≫ cylinderComparison f g sq q b c w =
      DoubleCylinder.endMap (leftLeg f q b) (rightLeg f g q b c w) ≫
        endsComparison f g sq q b c w := by
  apply ConcreteCategory.hom_ext
  intro z
  cases z with
  | inl z =>
    apply Subtype.ext
    apply Prod.ext
    · exact ConcreteCategory.congr_hom sq.w (Sum.inl z.1.1)
    · rfl
  | inr z =>
    apply Subtype.ext
    apply Prod.ext
    · exact ConcreteCategory.congr_hom sq.w (Sum.inr z.1.1)
    · rfl

variable {Z : TopCat.{u}} {lh : HA f q b ⊗ TopCat.I ⟶ Z}
  {eh : TopCat.of (HB q b ⊕ HC q c) ⟶ Z}
  (sqH : IsPushout (TheoremA.intervalEndpoints (HA f q b))
    (DoubleCylinder.endMap (leftLeg f q b) (rightLeg f g q b c w)) lh eh)

/-- The canonical comparison to the homotopy pullback over the total base. -/
def comparison : Z ⟶ Target f g sq q b c w :=
  sqH.desc (cylinderComparison f g sq q b c w) (endsComparison f g sq q b c w)
    (comparison_square f g sq q b c w)

@[simp] theorem comparison_cylinder (z : HA f q b) (t : TopCat.I) :
    (comparison f g sq q b c w sqH (lh (z, t))).1 = (l (z.1.1, t), z.1.2) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (sqH.inl_desc (cylinderComparison f g sq q b c w)
    (endsComparison f g sq q b c w) (comparison_square f g sq q b c w)) (z, t))

@[simp] theorem comparison_left (z : HB q b) :
    (comparison f g sq q b c w sqH (eh (Sum.inl z))).1 = (e (Sum.inl z.1.1), z.1.2) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (sqH.inr_desc (cylinderComparison f g sq q b c w)
    (endsComparison f g sq q b c w) (comparison_square f g sq q b c w)) (Sum.inl z))

@[simp] theorem comparison_right (z : HC q c) :
    (comparison f g sq q b c w sqH (eh (Sum.inr z))).1 = (e (Sum.inr z.1.1), z.1.2) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (sqH.inr_desc (cylinderComparison f g sq q b c w)
    (endsComparison f g sq q b c w) (comparison_square f g sq q b c w)) (Sum.inr z))

/-- The comparison lies over the canonical map of double cylinders. -/
theorem comparison_base :
    comparison f g sq q b c w sqH ≫
        TopCat.ofHom (HomotopyPullback.baseProjection q.hom (parameter f g sq b c w).hom) =
      DoubleCylinder.map sqH sq
        (TopCat.ofHom (HomotopyPullback.baseProjection q.hom (f ≫ b).hom))
        (TopCat.ofHom (HomotopyPullback.baseProjection q.hom b.hom))
        (TopCat.ofHom (HomotopyPullback.baseProjection q.hom c.hom)) rfl rfl := by
  apply ConcreteCategory.hom_ext
  intro x
  rcases Types.eq_or_eq_of_isPushout (sqH.map (forget TopCat)) x with
    ⟨⟨z, t⟩, h⟩ | ⟨z | z, h⟩
  · change lh (z, t) = x at h
    subst x
    change (comparison f g sq q b c w sqH (lh (z, t))).1.1 = _
    rw [DoubleCylinder.map_cylinder_apply]
    exact congrArg Prod.fst (comparison_cylinder f g sq q b c w sqH z t)
  · change eh (Sum.inl z) = x at h
    subst x
    change (comparison f g sq q b c w sqH (eh (Sum.inl z))).1.1 = _
    rw [DoubleCylinder.map_left]
    exact congrArg Prod.fst (comparison_left f g sq q b c w sqH z)
  · change eh (Sum.inr z) = x at h
    subst x
    change (comparison f g sq q b c w sqH (eh (Sum.inr z))).1.1 = _
    rw [DoubleCylinder.map_right]
    exact congrArg Prod.fst (comparison_right f g sq q b c w sqH z)

@[simp] theorem height_comparison (x : Z) :
    DoubleCylinder.height f g sq (comparison f g sq q b c w sqH x).1.1 =
      DoubleCylinder.height (leftLeg f q b) (rightLeg f g q b c w) sqH x := by
  have h := ConcreteCategory.congr_hom (comparison_base f g sq q b c w sqH) x
  change (comparison f g sq q b c w sqH x).1.1 = _ at h
  rw [h, DoubleCylinder.height_map]


variable (lo hi : I)

/-- The homotopy-pullback target restricted to the same open height band. -/
abbrev TargetBand :=
  {z : Target f g sq q b c w //
    lo < DoubleCylinder.height f g sq z.1.1 ∧ DoubleCylinder.height f g sq z.1.1 < hi}

/-- The exact product chart for the target's middle band. -/
def targetBandHomeomorph : HA f q b × DoubleCylinder.Band lo hi ≃ₜ
    TargetBand f g sq q b c w lo hi := by
  let S : Set D := {d | lo < DoubleCylinder.height f g sq d ∧
    DoubleCylinder.height f g sq d < hi}
  let h := HomotopyPullback.parameterProductHomeomorph q.hom
    (HomotopyPullback.restrictedParameter (parameter f g sq b c w).hom S)
    (f ≫ b).hom (DoubleCylinder.bandHomeomorph f g sq lo hi)
    (fun a t ↦ parameter_cylinder f g sq b c w a (ULift.up t.1))
  exact h.trans (HomotopyPullback.restrictionHomeomorph q.hom
    (parameter f g sq b c w).hom S).symm

@[simp] theorem targetBandHomeomorph_val (z : HA f q b × DoubleCylinder.Band lo hi) :
    (targetBandHomeomorph f g sq q b c w lo hi z).1.1 =
      (l (z.1.1.1, ULift.up z.2.1), z.1.1.2) := rfl

/-- The canonical comparison restricted to the open middle band. -/
def bandComparison :
    C(DoubleCylinder.BandSpace (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi,
      TargetBand f g sq q b c w lo hi) :=
  ⟨fun z ↦ ⟨comparison f g sq q b c w sqH z.1, by
    simpa only [height_comparison f g sq q b c w sqH] using z.2⟩, by fun_prop⟩

/-- The middle-band restriction is an actual homeomorphism, because both
sides have the identical homotopy-pullback-times-band coordinates. -/
def bandComparisonHomeomorph :
    DoubleCylinder.BandSpace (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi ≃ₜ
      TargetBand f g sq q b c w lo hi :=
  (DoubleCylinder.bandHomeomorph (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi).symm.trans
    (targetBandHomeomorph f g sq q b c w lo hi)

@[simp] theorem bandComparisonHomeomorph_apply
    (z : DoubleCylinder.BandSpace (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi) :
    bandComparisonHomeomorph f g sq q b c w sqH lo hi z =
      bandComparison f g sq q b c w sqH lo hi z := by
  obtain ⟨x, rfl⟩ :=
    (DoubleCylinder.bandHomeomorph (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi).surjective z
  apply Subtype.ext
  apply Subtype.ext
  change (targetBandHomeomorph f g sq q b c w lo hi
    ((DoubleCylinder.bandHomeomorph (leftLeg f q b) (rightLeg f g q b c w)
      sqH lo hi).symm
      (DoubleCylinder.bandHomeomorph (leftLeg f q b) (rightLeg f g q b c w)
        sqH lo hi x))).1.1 = _
  rw [Homeomorph.symm_apply_apply, targetBandHomeomorph_val]
  exact (comparison_cylinder f g sq q b c w sqH x.1 (ULift.up x.2.1)).symm

def bandComparisonHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (DoubleCylinder.BandSpace (leftLeg f q b) (rightLeg f g q b c w) sqH lo hi)
      (TargetBand f g sq q b c w lo hi) :=
  (bandComparisonHomeomorph f g sq q b c w sqH lo hi).toHomotopyEquiv

@[simp] theorem bandComparisonHomotopyEquiv_toFun :
    (bandComparisonHomotopyEquiv f g sq q b c w sqH lo hi).toFun =
      bandComparison f g sq q b c w sqH lo hi := by
  apply ContinuousMap.ext
  intro z
  exact bandComparisonHomeomorph_apply f g sq q b c w sqH lo hi z

end Quillen.HomotopyPullbackDoubleCylinder

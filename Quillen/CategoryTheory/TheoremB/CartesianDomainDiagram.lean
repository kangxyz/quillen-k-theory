import Quillen.CategoryTheory.TheoremB.HomotopyPullbackDoubleCylinderMap
import Quillen.CategoryTheory.TheoremB.DoubleCylinderCollapse

/-! The strict diagram of canonical corner comparisons used in
fixed-target homotopy-cartesian pushout descent. -/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.CartesianDomainPushout
open HomotopyPullbackDoubleCylinder
variable {A B C P A' B' C' P' E T : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ P} {j : C ⟶ P}
  {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ P'} {j' : C' ⟶ P'}
  (sq : IsPushout f g i j) (sq' : IsPushout f' g' i' j')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (wi : i ≫ p = b ≫ i') (wj : j ≫ p = c ≫ j')
  (q : E ⟶ T) (s : P' ⟶ T) (t : P ⟶ E) (w : t ≫ q = p ≫ s)

abbrev baseLeft : B' ⟶ T := i' ≫ s
abbrev baseRight : C' ⟶ T := j' ≫ s
include sq' in
theorem baseSquare : f' ≫ baseLeft (i' := i') s = g' ≫ baseRight (j' := j') s := sq'.w_assoc s

include wi w in
theorem leftSquare : (i ≫ t) ≫ q = b ≫ baseLeft (i' := i') s := by
  rw [Category.assoc, w, ← Category.assoc, wi, Category.assoc]
include wj w in
theorem rightSquare : (j ≫ t) ≫ q = c ≫ baseRight (j' := j') s := by
  rw [Category.assoc, w, ← Category.assoc, wj, Category.assoc]
include wf wi w in
theorem sourceSquare : (f ≫ i ≫ t) ≫ q = a ≫ f' ≫ baseLeft (i' := i') s := by
  rw [Category.assoc, leftSquare b p wi q s t w, ← Category.assoc, wf, Category.assoc]

def comparisonA : A ⟶ HA f' q (baseLeft (i' := i') s) := TopCat.ofHom
  (HomotopyPullback.comparison q.hom (f' ≫ baseLeft (i' := i') s).hom a.hom (f ≫ i ≫ t).hom
    (congrArg TopCat.Hom.hom (sourceSquare a b p wf wi q s t w)))
def comparisonB : B ⟶ HB q (baseLeft (i' := i') s) := TopCat.ofHom
  (HomotopyPullback.comparison q.hom (baseLeft (i' := i') s).hom b.hom (i ≫ t).hom
    (congrArg TopCat.Hom.hom (leftSquare b p wi q s t w)))
def comparisonC : C ⟶ HC q (baseRight (j' := j') s) := TopCat.ofHom
  (HomotopyPullback.comparison q.hom (baseRight (j' := j') s).hom c.hom (j ≫ t).hom
    (congrArg TopCat.Hom.hom (rightSquare c p wj q s t w)))

include wf in
theorem comparison_left : f ≫ comparisonB b p wi q s t w =
    comparisonA a b p wf wi q s t w ≫ leftLeg f' q (baseLeft (i' := i') s) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  exact Prod.ext (ConcreteCategory.congr_hom wf x) (Prod.ext rfl
    (ContinuousMap.ext fun _ ↦ congrArg (baseLeft (i' := i') s) (ConcreteCategory.congr_hom wf x)))

include sq wg in
theorem comparison_right : g ≫ comparisonC c p wj q s t w =
    comparisonA a b p wf wi q s t w ≫ rightLeg f' g' q (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare sq' s) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact ConcreteCategory.congr_hom wg x
  · apply Prod.ext
    · exact congrArg t (ConcreteCategory.congr_hom sq.w x).symm
    · apply ContinuousMap.ext
      intro r
      exact (congrArg (baseRight (j' := j') s) (ConcreteCategory.congr_hom wg x)).trans
        (ConcreteCategory.congr_hom (baseSquare sq' s) (a x)).symm

abbrev HPLeft := leftLeg f' q (baseLeft (i' := i') s)
abbrev HPRight := rightLeg f' g' q (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare sq' s)
abbrev HPCylinder := CartesianPushout.Cylinder (HPLeft (f' := f') (i' := i') q s) (HPRight sq' q s)
abbrev HPCylinderSquare := CartesianPushout.cylinderSquare (HPLeft (f' := f') (i' := i') q s) (HPRight sq' q s)

/-- The strict map of spans whose three components are the given canonical
homotopy-cartesian corner comparisons. -/
abbrev cylinderComparison : CartesianPushout.Cylinder f g ⟶ HPCylinder sq' q s :=
  DoubleCylinder.map (CartesianPushout.cylinderSquare f g) (HPCylinderSquare sq' q s)
    (comparisonA a b p wf wi q s t w) (comparisonB b p wi q s t w) (comparisonC c p wj q s t w)
    (comparison_left a b p wf wi q s t w) (comparison_right sq sq' a b c p wf wg wi wj q s t w)

/-- Actual componentwise equivalences glue on their ordinary double cylinders. -/
def cylinderComparisonHomotopyEquiv
    (EA : ContinuousMap.HomotopyEquiv A (HA f' q (baseLeft (i' := i') s)))
    (hEA : EA.toFun = (comparisonA a b p wf wi q s t w).hom)
    (EB : ContinuousMap.HomotopyEquiv B (HB q (baseLeft (i' := i') s)))
    (hEB : EB.toFun = (comparisonB b p wi q s t w).hom)
    (EC : ContinuousMap.HomotopyEquiv C (HC q (baseRight (j' := j') s)))
    (hEC : EC.toFun = (comparisonC c p wj q s t w).hom) :
    ContinuousMap.HomotopyEquiv (CartesianPushout.Cylinder f g) (HPCylinder sq' q s) :=
  DoubleCylinder.mapHomotopyEquiv (CartesianPushout.cylinderSquare f g) (HPCylinderSquare sq' q s)
    (comparisonA a b p wf wi q s t w) (comparisonB b p wi q s t w) (comparisonC c p wj q s t w)
    (comparison_left a b p wf wi q s t w) (comparison_right sq sq' a b c p wf wg wi wj q s t w)
    EA hEA EB hEB EC hEC

abbrev baseParameter : CartesianPushout.Cylinder f' g' ⟶ T :=
  parameter f' g' (CartesianPushout.cylinderSquare f' g') (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare sq' s)

/-- The fixed-target parameter on the base double cylinder is exactly the
ordinary collapse followed by the specified base map. -/
theorem baseParameter_eq : baseParameter sq' s = CartesianPushout.collapseBase sq' ≫ s := by
  apply (CartesianPushout.cylinderSquare f' g').hom_ext
  · apply ConcreteCategory.hom_ext
    intro z
    exact (parameter_cylinder f' g' (CartesianPushout.cylinderSquare f' g')
      (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare sq' s) z.1 z.2).trans
        (congrArg s (DoubleCylinder.collapse_cylinder_apply (CartesianPushout.cylinderSquare f' g') sq' z.1 z.2)).symm
  · apply ConcreteCategory.hom_ext
    intro z
    cases z with
    | inl x =>
      exact (parameter_left f' g' (CartesianPushout.cylinderSquare f' g')
        (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare sq' s) x).trans
          (congrArg s (DoubleCylinder.collapse_left (CartesianPushout.cylinderSquare f' g') sq' x)).symm
    | inr x =>
      exact (parameter_right f' g' (CartesianPushout.cylinderSquare f' g')
        (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare sq' s) x).trans
          (congrArg s (DoubleCylinder.collapse_right (CartesianPushout.cylinderSquare f' g') sq' x)).symm

/-- Collapse only the parameter coordinate, retaining the source and the
entire compact-open path in the fixed target. -/
def parameterCollapse : C(HomotopyPullback q.hom (baseParameter sq' s).hom,
    HomotopyPullback q.hom s.hom) where
  toFun z := ⟨(CartesianPushout.collapseBase sq' z.1.1, z.1.2), z.2.1,
    z.2.2.trans (ConcreteCategory.congr_hom (baseParameter_eq sq' s) z.1.1)⟩
  continuous_toFun := by fun_prop

@[simp] theorem parameterCollapse_val (z : HomotopyPullback q.hom (baseParameter sq' s).hom) :
    (parameterCollapse sq' q s z).1 = (CartesianPushout.collapseBase sq' z.1.1, z.1.2) := rfl

/-- The actual parameter collapse is HE when the base attachment has HEP. -/
def parameterCollapseHomotopyEquiv (hf' : TheoremA.homotopyExtensionProperty f') :
    ContinuousMap.HomotopyEquiv (HomotopyPullback q.hom (baseParameter sq' s).hom)
      (HomotopyPullback q.hom s.hom) := by
  let e0 := (CartesianPushout.baseMapCongr q.hom (baseParameter sq' s).hom
    (s.hom.comp (CartesianPushout.collapseBase sq').hom)
    (congrArg TopCat.Hom.hom (baseParameter_eq sq' s))).toHomotopyEquiv
  let e1 := HomotopyPullback.parameterEquiv q.hom s.hom
    (DoubleCylinder.collapseHomotopyEquiv (CartesianPushout.cylinderSquare f' g') sq' hf')
  let E := e0.trans e1
  have hE : E.toFun = parameterCollapse sq' q s := by ext z; rfl
  exact { E with toFun := parameterCollapse sq' q s
                 left_inv := by simpa only [hE] using E.left_inv
                 right_inv := by simpa only [hE] using E.right_inv }

@[simp] theorem parameterCollapseHomotopyEquiv_toFun (hf' : TheoremA.homotopyExtensionProperty f') :
    (parameterCollapseHomotopyEquiv sq' q s hf').toFun = parameterCollapse sq' q s := rfl

/-- The path-space comparison for the base double cylinder followed by
the actual base collapse. -/
def HPComparison : HPCylinder sq' q s ⟶ TopCat.of (HomotopyPullback q.hom s.hom) :=
  HomotopyPullbackDoubleCylinder.comparison f' g' (CartesianPushout.cylinderSquare f' g') q
    (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare sq' s) (HPCylinderSquare sq' q s) ≫
      TopCat.ofHom (parameterCollapse sq' q s)

/-- The prescribed canonical comparison on the ordinary pushout vertex. -/
def totalComparison : P ⟶ TopCat.of (HomotopyPullback q.hom s.hom) := TopCat.ofHom
  (HomotopyPullback.comparison q.hom s.hom p.hom t.hom (congrArg TopCat.Hom.hom w))

include sq sq' wf wg wi wj in
/-- All constructions retain the actual global canonical comparison. -/
theorem comparison_naturality :
    CartesianPushout.collapse sq ≫ totalComparison p q s t w =
      cylinderComparison sq sq' a b c p wf wg wi wj q s t w ≫ HPComparison sq' q s := by
  apply (CartesianPushout.cylinderSquare f g).hom_ext
  · apply ConcreteCategory.hom_ext
    rintro ⟨x, r⟩
    change totalComparison p q s t w (CartesianPushout.collapse sq
      (CartesianPushout.cylinderLine f g (x, r))) =
      HPComparison sq' q s (cylinderComparison sq sq' a b c p wf wg wi wj q s t w
        (CartesianPushout.cylinderLine f g (x, r)))
    rw [DoubleCylinder.collapse_cylinder_apply, DoubleCylinder.map_cylinder_apply]
    apply Subtype.ext
    have hk := HomotopyPullbackDoubleCylinder.comparison_cylinder f' g'
      (CartesianPushout.cylinderSquare f' g') q (baseLeft (i' := i') s)
      (baseRight (j' := j') s) (baseSquare sq' s) (HPCylinderSquare sq' q s)
      (comparisonA a b p wf wi q s t w x) r
    have hk' := congrArg (fun z : CartesianPushout.Cylinder f' g' × (E × C(unitInterval, T)) ↦
      (CartesianPushout.collapseBase sq' z.1, z.2)) hk
    apply Eq.trans _ hk'.symm
    change (p (i (f x)), t (i (f x)), ContinuousMap.const unitInterval (s (p (i (f x))))) =
      (CartesianPushout.collapseBase sq' (CartesianPushout.cylinderLine f' g' (a x, r)),
        t (i (f x)), ContinuousMap.const unitInterval (s (i' (f' (a x)))))
    rw [DoubleCylinder.collapse_cylinder_apply]
    have hx : p (i (f x)) = i' (f' (a x)) :=
      (ConcreteCategory.congr_hom wi (f x)).trans (congrArg i' (ConcreteCategory.congr_hom wf x))
    exact Prod.ext hx (Prod.ext rfl (ContinuousMap.ext (fun _ ↦ congrArg s hx)))
  · apply ConcreteCategory.hom_ext
    intro z
    cases z with
    | inl x =>
      change totalComparison p q s t w (CartesianPushout.collapse sq
        (CartesianPushout.cylinderEnd f g (Sum.inl x))) =
        HPComparison sq' q s (cylinderComparison sq sq' a b c p wf wg wi wj q s t w
          (CartesianPushout.cylinderEnd f g (Sum.inl x)))
      rw [DoubleCylinder.collapse_left, DoubleCylinder.map_left]
      apply Subtype.ext
      have hk := HomotopyPullbackDoubleCylinder.comparison_left f' g'
        (CartesianPushout.cylinderSquare f' g') q (baseLeft (i' := i') s)
        (baseRight (j' := j') s) (baseSquare sq' s) (HPCylinderSquare sq' q s)
        (comparisonB b p wi q s t w x)
      have hk' := congrArg (fun z : CartesianPushout.Cylinder f' g' × (E × C(unitInterval, T)) ↦
        (CartesianPushout.collapseBase sq' z.1, z.2)) hk
      apply Eq.trans _ hk'.symm
      change (p (i x), t (i x), ContinuousMap.const unitInterval (s (p (i x)))) =
        (CartesianPushout.collapseBase sq' (CartesianPushout.cylinderEnd f' g' (Sum.inl (b x))),
          t (i x), ContinuousMap.const unitInterval (s (i' (b x))))
      rw [DoubleCylinder.collapse_left]
      exact Prod.ext (ConcreteCategory.congr_hom wi x) (Prod.ext rfl
        (ContinuousMap.ext (fun _ ↦ congrArg s (ConcreteCategory.congr_hom wi x))))
    | inr x =>
      change totalComparison p q s t w (CartesianPushout.collapse sq
        (CartesianPushout.cylinderEnd f g (Sum.inr x))) =
        HPComparison sq' q s (cylinderComparison sq sq' a b c p wf wg wi wj q s t w
          (CartesianPushout.cylinderEnd f g (Sum.inr x)))
      rw [DoubleCylinder.collapse_right, DoubleCylinder.map_right]
      apply Subtype.ext
      have hk := HomotopyPullbackDoubleCylinder.comparison_right f' g'
        (CartesianPushout.cylinderSquare f' g') q (baseLeft (i' := i') s)
        (baseRight (j' := j') s) (baseSquare sq' s) (HPCylinderSquare sq' q s)
        (comparisonC c p wj q s t w x)
      have hk' := congrArg (fun z : CartesianPushout.Cylinder f' g' × (E × C(unitInterval, T)) ↦
        (CartesianPushout.collapseBase sq' z.1, z.2)) hk
      apply Eq.trans _ hk'.symm
      change (p (j x), t (j x), ContinuousMap.const unitInterval (s (p (j x)))) =
        (CartesianPushout.collapseBase sq' (CartesianPushout.cylinderEnd f' g' (Sum.inr (c x))),
          t (j x), ContinuousMap.const unitInterval (s (j' (c x))))
      rw [DoubleCylinder.collapse_right]
      exact Prod.ext (ConcreteCategory.congr_hom wj x) (Prod.ext rfl
        (ContinuousMap.ext (fun _ ↦ congrArg s (ConcreteCategory.congr_hom wj x))))

end Quillen.CartesianDomainPushout

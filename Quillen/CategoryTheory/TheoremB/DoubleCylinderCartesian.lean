import Quillen.CategoryTheory.TheoremB.FiniteCartesian
import Quillen.CategoryTheory.TheoremB.MappingPathFunctor

/-!
# The genuine finite homotopy-cartesian double-cylinder theorem

No fibration hypothesis remains. Functorial mapping-path replacement turns
the two original homotopy-cartesian edge squares into actual strict
pullback equivalences of fibrations. The proved finite normalization then
applies, and source homotopy equivalence transports its canonical endpoint
comparisons back to the original ordinary double cylinders.
-/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.DoubleCylinder.Cartesian
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TheoremA.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

abbrev ReplacedA := TopCat.of (MappingPath a.hom)
abbrev ReplacedB := TopCat.of (MappingPath b.hom)
abbrev ReplacedC := TopCat.of (MappingPath c.hom)
abbrev endpointA : ReplacedA a ⟶ A' := TopCat.ofHom (MappingPath.endpoint a.hom)
abbrev endpointB : ReplacedB b ⟶ B' := TopCat.ofHom (MappingPath.endpoint b.hom)
abbrev endpointC : ReplacedC c ⟶ C' := TopCat.ofHom (MappingPath.endpoint c.hom)
abbrev inclusionA : A ⟶ ReplacedA a := TopCat.ofHom (MappingPath.inclusion a.hom)
abbrev inclusionB : B ⟶ ReplacedB b := TopCat.ofHom (MappingPath.inclusion b.hom)
abbrev inclusionC : C ⟶ ReplacedC c := TopCat.ofHom (MappingPath.inclusion c.hom)
abbrev replacedLeft : ReplacedA a ⟶ ReplacedB b :=
  TopCat.ofHom (MappingPath.map f.hom f'.hom (congrArg TopCat.Hom.hom wf))
abbrev replacedRight : ReplacedA a ⟶ ReplacedC c :=
  TopCat.ofHom (MappingPath.map g.hom g'.hom (congrArg TopCat.Hom.hom wg))

theorem inclusion_left : f ≫ inclusionB b = inclusionA a ≫ replacedLeft a b wf := by
  apply ConcreteCategory.hom_ext
  intro x
  exact (ContinuousMap.congr_fun (MappingPath.map_inclusion f.hom f'.hom
    (congrArg TopCat.Hom.hom wf)) x).symm

theorem inclusion_right : g ≫ inclusionC c = inclusionA a ≫ replacedRight a c wg := by
  apply ConcreteCategory.hom_ext
  intro x
  exact (ContinuousMap.congr_fun (MappingPath.map_inclusion g.hom g'.hom
    (congrArg TopCat.Hom.hom wg)) x).symm

abbrev ReplacedTotal : TopCat.{u} := pushout (TheoremA.intervalEndpoints (ReplacedA a))
  (endMap (replacedLeft a b wf) (replacedRight a c wg))
abbrev replacedLine : ReplacedA a ⊗ TopCat.I ⟶ ReplacedTotal a b c wf wg := pushout.inl _ _
abbrev replacedEnd : TopCat.of (ReplacedB b ⊕ ReplacedC c) ⟶ ReplacedTotal a b c wf wg := pushout.inr _ _
theorem replacedSquare : IsPushout (TheoremA.intervalEndpoints (ReplacedA a))
    (endMap (replacedLeft a b wf) (replacedRight a c wg))
    (replacedLine a b c wf wg) (replacedEnd a b c wf wg) := IsPushout.of_hasPushout _ _

abbrev replacedProjection : ReplacedTotal a b c wf wg ⟶ D' :=
  DoubleCylinder.map (replacedSquare a b c wf wg) sq'
    (endpointA a) (endpointB b) (endpointC c) rfl rfl
abbrev replacementMap : D ⟶ ReplacedTotal a b c wf wg :=
  DoubleCylinder.map sq (replacedSquare a b c wf wg)
    (inclusionA a) (inclusionB b) (inclusionC c)
    (inclusion_left a b wf) (inclusion_right a c wg)

/-- The actual map to the functorial replacement is an ordinary HE. -/
def replacementHomotopyEquiv : ContinuousMap.HomotopyEquiv D (ReplacedTotal a b c wf wg) :=
  DoubleCylinder.mapHomotopyEquiv sq (replacedSquare a b c wf wg)
    (inclusionA a) (inclusionB b) (inclusionC c)
    (inclusion_left a b wf) (inclusion_right a c wg)
    (MappingPath.inclusionHomotopyEquiv a.hom) rfl
    (MappingPath.inclusionHomotopyEquiv b.hom) rfl
    (MappingPath.inclusionHomotopyEquiv c.hom) rfl

theorem replacement_over :
    (replacedProjection sq' a b c wf wg).hom.comp (replacementHomotopyEquiv sq a b c wf wg).toFun =
      (DoubleCylinder.map sq sq' a b c wf wg).hom := by
  apply ContinuousMap.ext
  intro z
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) z with ⟨⟨x, t⟩, hz⟩ | ⟨x | x, hz⟩
  · change l (x, t) = z at hz
    rw [← hz]
    change replacedProjection sq' a b c wf wg (replacementMap sq a b c wf wg (l (x, t))) = _
    rw [DoubleCylinder.map_cylinder_apply, DoubleCylinder.map_cylinder_apply, DoubleCylinder.map_cylinder_apply]
    rfl
  · change e (Sum.inl x) = z at hz
    rw [← hz]
    change replacedProjection sq' a b c wf wg (replacementMap sq a b c wf wg (e (Sum.inl x))) = _
    rw [DoubleCylinder.map_left, DoubleCylinder.map_left, DoubleCylinder.map_left]
    rfl
  · change e (Sum.inr x) = z at hz
    rw [← hz]
    change replacedProjection sq' a b c wf wg (replacementMap sq a b c wf wg (e (Sum.inr x))) = _
    rw [DoubleCylinder.map_right, DoubleCylinder.map_right, DoubleCylinder.map_right]
    rfl

variable
  (EL : ContinuousMap.HomotopyEquiv A (HomotopyPullback b.hom f'.hom))
  (hEL : EL.toFun = HomotopyPullback.comparison b.hom f'.hom a.hom f.hom (congrArg TopCat.Hom.hom wf))
  (ER : ContinuousMap.HomotopyEquiv A (HomotopyPullback c.hom g'.hom))
  (hER : ER.toFun = HomotopyPullback.comparison c.hom g'.hom a.hom g.hom (congrArg TopCat.Hom.hom wg))

/-- The replaced left endpoint square is obtained from the fully proved
fibration-normalized finite gluing theorem. -/
def replacedLeftEndEquiv : ContinuousMap.HomotopyEquiv (ReplacedB b)
    (HomotopyPullback (replacedProjection sq' a b c wf wg).hom (Subdivision.leftEnd (e := e')).hom) :=
  FiniteNormalization.leftEndHomotopyEquiv (replacedSquare a b c wf wg) sq'
    (endpointA a) (endpointB b) (endpointC c) rfl rfl
    (MappingPath.endpoint_homotopyLiftingProperty a.hom)
    (MappingPath.endpoint_homotopyLiftingProperty b.hom)
    (MappingPath.endpoint_homotopyLiftingProperty c.hom)
    (MappingPath.strictComparisonHomotopyEquiv f.hom f'.hom (congrArg TopCat.Hom.hom wf) EL hEL) rfl
    (MappingPath.strictComparisonHomotopyEquiv g.hom g'.hom (congrArg TopCat.Hom.hom wg) ER hER) rfl

def replacedRightEndEquiv : ContinuousMap.HomotopyEquiv (ReplacedC c)
    (HomotopyPullback (replacedProjection sq' a b c wf wg).hom (Subdivision.rightEnd (e := e')).hom) :=
  FiniteNormalization.rightEndHomotopyEquiv (replacedSquare a b c wf wg) sq'
    (endpointA a) (endpointB b) (endpointC c) rfl rfl
    (MappingPath.endpoint_homotopyLiftingProperty a.hom)
    (MappingPath.endpoint_homotopyLiftingProperty b.hom)
    (MappingPath.endpoint_homotopyLiftingProperty c.hom)
    (MappingPath.strictComparisonHomotopyEquiv f.hom f'.hom (congrArg TopCat.Hom.hom wf) EL hEL) rfl
    (MappingPath.strictComparisonHomotopyEquiv g.hom g'.hom (congrArg TopCat.Hom.hom wg) ER hER) rfl

abbrev leftIntoReplacement : C(B, ReplacedTotal a b c wf wg) :=
  (Subdivision.leftEnd (e := replacedEnd a b c wf wg)).hom.comp (MappingPath.inclusion b.hom)
abbrev rightIntoReplacement : C(C, ReplacedTotal a b c wf wg) :=
  (Subdivision.rightEnd (e := replacedEnd a b c wf wg)).hom.comp (MappingPath.inclusion c.hom)

theorem leftIntoReplacement_square :
    (replacedProjection sq' a b c wf wg).hom.comp (leftIntoReplacement a b c wf wg) =
      (Subdivision.leftEnd (e := e')).hom.comp b.hom := by
  ext x
  exact DoubleCylinder.map_left (replacedSquare a b c wf wg) sq'
    (endpointA a) (endpointB b) (endpointC c) rfl rfl (MappingPath.inclusion b.hom x)

theorem rightIntoReplacement_square :
    (replacedProjection sq' a b c wf wg).hom.comp (rightIntoReplacement a b c wf wg) =
      (Subdivision.rightEnd (e := e')).hom.comp c.hom := by
  ext x
  exact DoubleCylinder.map_right (replacedSquare a b c wf wg) sq'
    (endpointA a) (endpointB b) (endpointC c) rfl rfl (MappingPath.inclusion c.hom x)

/-- General genuine finite homotopy-cartesian gluing, with no lifting or
normalization hypotheses: the canonical left endpoint comparison is HE. -/
def leftEndHomotopyEquiv : ContinuousMap.HomotopyEquiv B
    (HomotopyPullback (DoubleCylinder.map sq sq' a b c wf wg).hom (Subdivision.leftEnd (e := e')).hom) := by
  apply HomotopyPullback.comparisonEquivOfSourceEquiv
    (DoubleCylinder.map sq sq' a b c wf wg).hom (replacedProjection sq' a b c wf wg).hom
    (Subdivision.leftEnd (e := e')).hom b.hom (Subdivision.leftEnd (e := e)).hom
    (leftIntoReplacement a b c wf wg) (FiniteNormalization.left_square sq sq' a b c wf wg)
    (leftIntoReplacement_square sq' a b c wf wg) (replacementHomotopyEquiv sq a b c wf wg)
    (replacement_over sq sq' a b c wf wg)
    (by
      ext x
      exact DoubleCylinder.map_left sq (replacedSquare a b c wf wg)
        (inclusionA a) (inclusionB b) (inclusionC c) (inclusion_left a b wf) (inclusion_right a c wg) x)
    ((MappingPath.inclusionHomotopyEquiv b.hom).trans (replacedLeftEndEquiv sq' a b c wf wg EL hEL ER hER))
  apply ContinuousMap.ext
  intro x
  change (replacedLeftEndEquiv sq' a b c wf wg EL hEL ER hER).toFun (MappingPath.inclusion b.hom x) = _
  rw [replacedLeftEndEquiv, FiniteNormalization.leftEndHomotopyEquiv_toFun]
  rfl

/-- The matching right endpoint comparison, again for the original
ordinary double-cylinder map and its canonical constant-path comparison. -/
def rightEndHomotopyEquiv : ContinuousMap.HomotopyEquiv C
    (HomotopyPullback (DoubleCylinder.map sq sq' a b c wf wg).hom (Subdivision.rightEnd (e := e')).hom) := by
  apply HomotopyPullback.comparisonEquivOfSourceEquiv
    (DoubleCylinder.map sq sq' a b c wf wg).hom (replacedProjection sq' a b c wf wg).hom
    (Subdivision.rightEnd (e := e')).hom c.hom (Subdivision.rightEnd (e := e)).hom
    (rightIntoReplacement a b c wf wg) (FiniteNormalization.right_square sq sq' a b c wf wg)
    (rightIntoReplacement_square sq' a b c wf wg) (replacementHomotopyEquiv sq a b c wf wg)
    (replacement_over sq sq' a b c wf wg)
    (by
      ext x
      exact DoubleCylinder.map_right sq (replacedSquare a b c wf wg)
        (inclusionA a) (inclusionB b) (inclusionC c) (inclusion_left a b wf) (inclusion_right a c wg) x)
    ((MappingPath.inclusionHomotopyEquiv c.hom).trans (replacedRightEndEquiv sq' a b c wf wg EL hEL ER hER))
  apply ContinuousMap.ext
  intro x
  change (replacedRightEndEquiv sq' a b c wf wg EL hEL ER hER).toFun (MappingPath.inclusion c.hom x) = _
  rw [replacedRightEndEquiv, FiniteNormalization.rightEndHomotopyEquiv_toFun]
  rfl

@[simp] theorem leftEndHomotopyEquiv_toFun :
    (leftEndHomotopyEquiv sq sq' a b c wf wg EL hEL ER hER).toFun =
      HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
        (Subdivision.leftEnd (e := e')).hom b.hom (Subdivision.leftEnd (e := e)).hom
        (FiniteNormalization.left_square sq sq' a b c wf wg) :=
  HomotopyPullback.comparisonEquivOfSourceEquiv_toFun _ _ _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem rightEndHomotopyEquiv_toFun :
    (rightEndHomotopyEquiv sq sq' a b c wf wg EL hEL ER hER).toFun =
      HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
        (Subdivision.rightEnd (e := e')).hom c.hom (Subdivision.rightEnd (e := e)).hom
        (FiniteNormalization.right_square sq sq' a b c wf wg) :=
  HomotopyPullback.comparisonEquivOfSourceEquiv_toFun _ _ _ _ _ _ _ _ _ _ _ _ _

end Quillen.DoubleCylinder.Cartesian

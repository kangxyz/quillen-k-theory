import Quillen.CategoryTheory.TheoremB.DoubleCylinderFiberCoordinates

/-! # Exact collar restrictions of original double-cylinder fibers -/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.DoubleCylinder
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TheoremA.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') (cut : unitInterval)

def leftCollarFiberHomeomorph (y : LeftCollar f' g' sq' cut) :
    {x : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut x = y} ≃ₜ
      {x : D // map sq sq' a b c wf wg x = y.val} where
  toFun x := ⟨x.val.val,congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val,by
    change height f g sq x.val < cut
    rw [← height_map sq sq' a b c wf wg x.val,x.property]
    exact y.property⟩,Subtype.ext x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def rightCollarFiberHomeomorph (y : RightCollar f' g' sq' cut) :
    {x : RightCollar f g sq cut // rightCollarMap sq sq' a b c wf wg cut x = y} ≃ₜ
      {x : D // map sq sq' a b c wf wg x = y.val} where
  toFun x := ⟨x.val.val,congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val,by
    change cut < height f g sq x.val
    rw [← height_map sq sq' a b c wf wg x.val,x.property]
    exact y.property⟩,Subtype.ext x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def leftCollarEndFiberHomeomorph (hcut : 0 < cut) (y : B') :
    {x : B // b x = y} ≃ₜ
      {x : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut x =
        leftCollarInclusion f' g' sq' cut hcut y} :=
  (leftEndFiberHomeomorph sq sq' a b c wf wg y).trans
    (leftCollarFiberHomeomorph sq sq' a b c wf wg cut
      (leftCollarInclusion f' g' sq' cut hcut y)).symm

def rightCollarEndFiberHomeomorph (hcut : cut < 1) (y : C') :
    {x : C // c x = y} ≃ₜ
      {x : RightCollar f g sq cut // rightCollarMap sq sq' a b c wf wg cut x =
        rightCollarInclusion f' g' sq' cut hcut y} :=
  (rightEndFiberHomeomorph sq sq' a b c wf wg y).trans
    (rightCollarFiberHomeomorph sq sq' a b c wf wg cut
      (rightCollarInclusion f' g' sq' cut hcut y)).symm

def leftInteriorPoint (y : A') (t : OpenInterval) (ht : t.val < cut) : LeftCollar f' g' sq' cut :=
  ⟨l' (y,ULift.up t.val),by
    change height f' g' sq' (l' (y,ULift.up t.val)) < cut
    rw [height_cylinder]
    exact ht⟩
def rightInteriorPoint (y : A') (t : OpenInterval) (ht : cut < t.val) : RightCollar f' g' sq' cut :=
  ⟨l' (y,ULift.up t.val),by
    change cut < height f' g' sq' (l' (y,ULift.up t.val))
    rw [height_cylinder]
    exact ht⟩

def leftCollarInteriorFiberHomeomorph (y : A') (t : OpenInterval) (ht : t.val < cut) :
    {x : A // a x = y} ≃ₜ
      {x : LeftCollar f g sq cut // leftCollarMap sq sq' a b c wf wg cut x =
        leftInteriorPoint sq' cut y t ht} :=
  (interiorFiberHomeomorph sq sq' a b c wf wg y t).trans
    (leftCollarFiberHomeomorph sq sq' a b c wf wg cut (leftInteriorPoint sq' cut y t ht)).symm

def rightCollarInteriorFiberHomeomorph (y : A') (t : OpenInterval) (ht : cut < t.val) :
    {x : A // a x = y} ≃ₜ
      {x : RightCollar f g sq cut // rightCollarMap sq sq' a b c wf wg cut x =
        rightInteriorPoint sq' cut y t ht} :=
  (interiorFiberHomeomorph sq sq' a b c wf wg y t).trans
    (rightCollarFiberHomeomorph sq sq' a b c wf wg cut (rightInteriorPoint sq' cut y t ht)).symm

@[simp] theorem leftCollarEndFiberHomeomorph_val (hcut : 0 < cut) (y : B') (x : {x : B // b x = y}) :
    (leftCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y x).val =
      leftCollarInclusion f g sq cut hcut x.val := rfl
@[simp] theorem rightCollarEndFiberHomeomorph_val (hcut : cut < 1) (y : C') (x : {x : C // c x = y}) :
    (rightCollarEndFiberHomeomorph sq sq' a b c wf wg cut hcut y x).val =
      rightCollarInclusion f g sq cut hcut x.val := rfl
@[simp] theorem leftCollarInteriorFiberHomeomorph_val (y : A') (t : OpenInterval) (ht : t.val < cut)
    (x : {x : A // a x = y}) :
    (leftCollarInteriorFiberHomeomorph sq sq' a b c wf wg cut y t ht x).val.val =
      l (x.val,ULift.up t.val) := rfl
@[simp] theorem rightCollarInteriorFiberHomeomorph_val (y : A') (t : OpenInterval) (ht : cut < t.val)
    (x : {x : A // a x = y}) :
    (rightCollarInteriorFiberHomeomorph sq sq' a b c wf wg cut y t ht x).val.val =
      l (x.val,ULift.up t.val) := rfl

end Quillen.DoubleCylinder

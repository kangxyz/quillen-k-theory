/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitIdentityOperation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSplitMaps
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductSwapOuterUnit
public import Quillen.Waldhausen.SConstruction.Iterated.IdentityActionInterchangeSign

/-!
# Two original geometric unit operations and the actual independent-factor swap

Two independent scalar tracks anticommute on original nonnegative K-groups.
The original geometric projection-unit operations factor through those same
tracks and the unchanged base projection. Thus actual factor interchange
reverses the sign of their composite, including the original K-zero input.
No fixed action on a negative double cokernel is asserted here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes.ProductSwapUnit
open Quillen.PerfectComplexes.GlobalUnitIdentityOperation
universe u
namespace Quillen.PerfectComplexes.ProductUnitInterchange
attribute [local instance] Waldhausen.Additivity.KCommGroup

/-- The two genuine target scalar actions anticommute on every original nonnegative class. -/
theorem unitKOperation_interchange_sign (X : Scheme.{u}) (r s : (Γ(X, ⊤))ˣ)
    (n : ℕ) (a : BoundedFlatPerfectK X n) :
    unitKOperation X s (n + 1) (unitKOperation X r n a) =
      (unitKOperation X r (n + 1) (unitKOperation X s n a))⁻¹ :=
  originalKIdentityAction_interchange_sign (boundedFlatPerfectWaldhausen X)
    (smallUnit X r) (smallUnit X s) n a

variable {S T : Scheme.{u}} (p : S ⟶ integerBase) (q : T ⟶ integerBase)

/-- The actual factor unit pulled back to the original one-factor product. -/
def projectionUnit (X : Scheme.{u}) (r : (Γ(S, ⊤))ˣ) :
    (Γ((baseProductFunctor p).obj X, ⊤))ˣ :=
  Units.map (pullback.snd (toIntegerBase X) p).appTop.hom.toMonoidHom r

/-- The original raw projection-unit operation, with its complete chosen-zero normalization. -/
def projectionUnitOperation (X : Scheme.{u}) (r : (Γ(S, ⊤))ˣ) (n : ℕ) :
    BoundedFlatPerfectK X n →* BoundedFlatPerfectK ((baseProductFunctor p).obj X) (n + 1) :=
  originalKSelfTrackOperation (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectWaldhausen ((baseProductFunctor p).obj X))
    (boundedFlatPerfectUnitHomotopy ((baseProductProjection p).app X)
      (projectionUnit p X r)) n

/-- The two original projections and units, in their specified order. -/
def doubleProjectionUnitOperation (X : Scheme.{u}) (r : (Γ(S, ⊤))ˣ)
    (s : (Γ(T, ⊤))ˣ) (n : ℕ) :
    BoundedFlatPerfectK X n →*
      BoundedFlatPerfectK ((baseProductFunctor q).obj ((baseProductFunctor p).obj X)) (n + 2) :=
  (projectionUnitOperation q ((baseProductFunctor p).obj X) s (n + 1)).comp
    (projectionUnitOperation p X r n)

/-- Pullback along the second original projection is precisely the first-factor unit. -/
theorem projectionUnit_pullback (X : Scheme.{u}) (r : (Γ(S, ⊤))ˣ) :
    Units.map ((baseProductProjection q).app ((baseProductFunctor p).obj X)).appTop.hom.toMonoidHom
      (projectionUnit p X r) = innerUnit p q X r := by
  apply Units.ext
  change (((baseProductProjection q).app ((baseProductFunctor p).obj X)).appTop.hom
    ((pullback.snd (toIntegerBase X) p).appTop.hom (↑r))) =
      (innerProjection p q X).appTop.hom (↑r)
  rw [innerProjection, Scheme.Hom.comp_appTop]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Both raw operations retain the actual target identity actions and original base pullback. -/
theorem doubleProjectionUnitOperation_factor (X : Scheme.{u})
    (r : (Γ(S, ⊤))ˣ) (s : (Γ(T, ⊤))ˣ) (n : ℕ) (a : BoundedFlatPerfectK X n) :
    doubleProjectionUnitOperation p q X r s n a =
      unitKOperation _ (outerUnit q p X s) (n + 1)
        (unitKOperation _ (innerUnit p q X r) n
          (boundedFlatPerfectKPullback
            (((baseProductProjection q).app ((baseProductFunctor p).obj X)) ≫
              (baseProductProjection p).app X) n a)) := by
  simp only [doubleProjectionUnitOperation, projectionUnitOperation,
    originalUnit_operation, MonoidHom.comp_apply]
  have h := DFunLike.congr_fun
    (unitKOperation_pullback ((baseProductProjection q).app ((baseProductFunctor p).obj X))
      (projectionUnit p X r) n)
    (boundedFlatPerfectKPullback ((baseProductProjection p).app X) n a)
  change boundedFlatPerfectKPullback
      ((baseProductProjection q).app ((baseProductFunctor p).obj X)) (n + 1)
      (unitKOperation _ (projectionUnit p X r) n
        (boundedFlatPerfectKPullback ((baseProductProjection p).app X) n a)) =
    unitKOperation _
      (Units.map ((baseProductProjection q).app
        ((baseProductFunctor p).obj X)).appTop.hom.toMonoidHom (projectionUnit p X r)) n
      (boundedFlatPerfectKPullback ((baseProductProjection q).app
        ((baseProductFunctor p).obj X)) n
        (boundedFlatPerfectKPullback ((baseProductProjection p).app X) n a)) at h
  rw [projectionUnit_pullback] at h
  have hp := DFunLike.congr_fun
    (boundedFlatPerfectKPullback_comp
      ((baseProductProjection q).app ((baseProductFunctor p).obj X))
      ((baseProductProjection p).app X) n) a
  have hi := congrArg
    (unitKOperation ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))
      (innerUnit p q X r) n) hp.symm
  exact congrArg
    (unitKOperation ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))
      (outerUnit q p X s) (n + 1)) (h.trans hi)

/-- The actual geometric swap reverses the two original projection-unit operations. -/
theorem doubleProjectionUnitOperation_swap (X : Scheme.{u})
    (r : (Γ(S, ⊤))ˣ) (s : (Γ(T, ⊤))ˣ) (n : ℕ) (a : BoundedFlatPerfectK X n) :
    boundedFlatPerfectKPullback (baseProductSwapMap p q X) (n + 2)
      (doubleProjectionUnitOperation q p X s r n a) =
        (doubleProjectionUnitOperation p q X r s n a)⁻¹ := by
  rw [doubleProjectionUnitOperation_factor, doubleProjectionUnitOperation_factor]
  have h₁ := DFunLike.congr_fun
    (unitKOperation_pullback (baseProductSwapMap p q X) (outerUnit p q X r) (n + 1))
    (unitKOperation _ (innerUnit q p X s) n
      (boundedFlatPerfectKPullback
        (((baseProductProjection p).app ((baseProductFunctor q).obj X)) ≫
          (baseProductProjection q).app X) n a))
  simp only [MonoidHom.comp_apply, swap_unit] at h₁
  rw [h₁]
  have h₂ := DFunLike.congr_fun
    (unitKOperation_pullback (baseProductSwapMap p q X) (innerUnit q p X s) n)
    (boundedFlatPerfectKPullback
      (((baseProductProjection p).app ((baseProductFunctor q).obj X)) ≫
        (baseProductProjection q).app X) n a)
  simp only [MonoidHom.comp_apply, ProductSwapOuterUnit.swap_outer_unit] at h₂
  rw [h₂]
  have hb : baseProductSwapMap p q X ≫
      ((baseProductProjection p).app ((baseProductFunctor q).obj X)) ≫
        (baseProductProjection q).app X =
      ((baseProductProjection q).app ((baseProductFunctor p).obj X)) ≫
        (baseProductProjection p).app X := baseProductSwapMap_fst_fst p q X
  have hbK : boundedFlatPerfectKPullback (baseProductSwapMap p q X) n
      (boundedFlatPerfectKPullback
        (((baseProductProjection p).app ((baseProductFunctor q).obj X)) ≫
          (baseProductProjection q).app X) n a) =
      boundedFlatPerfectKPullback
        (((baseProductProjection q).app ((baseProductFunctor p).obj X)) ≫
          (baseProductProjection p).app X) n a := by
    rw [← MonoidHom.comp_apply, ← boundedFlatPerfectKPullback_comp, hb]
  rw [hbK]
  exact unitKOperation_interchange_sign _ (outerUnit q p X s) (innerUnit p q X r) n _

/-- The literal double Laurent projection operation has the required K-zero to K-two sign. -/
theorem doubleLaurentProjectionUnit_KZero_swap (X : Scheme.{u})
    (a : BoundedFlatPerfectK X 0) :
    boundedFlatPerfectKPullback
      (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) X) 2
      (doubleProjectionUnitOperation (laurentProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) X
        (laurentGlobalUnit (.of (ULift.{u} ℤ))) (laurentGlobalUnit (.of (ULift.{u} ℤ))) 0 a) =
    (doubleProjectionUnitOperation (laurentProjection (.of (ULift.{u} ℤ)))
      (laurentProjection (.of (ULift.{u} ℤ))) X
      (laurentGlobalUnit (.of (ULift.{u} ℤ))) (laurentGlobalUnit (.of (ULift.{u} ℤ))) 0 a)⁻¹ :=
  doubleProjectionUnitOperation_swap _ _ X _ _ 0 a

/-- The same original double projection operation as an additive-group arrow. -/
def doubleLaurentUnitMap (X : Scheme.{u}) :
    (boundedFlatPerfectKAddFunctor 0).obj (Opposite.op X) ⟶
      (boundedFlatPerfectKAddFunctor 2).obj
        (Opposite.op ((baseProductFunctor (laurentProjection (.of (ULift.{u} ℤ)))).obj
          ((baseProductFunctor (laurentProjection (.of (ULift.{u} ℤ)))).obj X))) :=
  AddCommGrpCat.ofHom (doubleProjectionUnitOperation
    (laurentProjection (.of (ULift.{u} ℤ))) (laurentProjection (.of (ULift.{u} ℤ))) X
    (laurentGlobalUnit (.of (ULift.{u} ℤ))) (laurentGlobalUnit (.of (ULift.{u} ℤ))) 0).toAdditive

/-- Actual geometric factor interchange is minus the unchanged original double unit arrow. -/
theorem doubleLaurentUnitMap_swap (X : Scheme.{u}) :
    doubleLaurentUnitMap X ≫ (boundedFlatPerfectKAddFunctor 2).map
      (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) X).op = -doubleLaurentUnitMap X := by
  apply AddCommGrpCat.hom_ext
  ext a
  exact congrArg Additive.ofMul
    (doubleLaurentProjectionUnit_KZero_swap X (Additive.toMul a))

end Quillen.PerfectComplexes.ProductUnitInterchange

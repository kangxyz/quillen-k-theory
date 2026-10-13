/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SmallModel.Fiber
public import Quillen.Waldhausen.SmallModel.Joint

/-! # Two-universe original-model regression consumers -/
@[expose] public section

noncomputable section
open CategoryTheory Limits Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Transport
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (W' : Structure D)

example : SmallCategory (Waldhausen.SmallModel C) := inferInstance
example : (sSet W.cof W.weq : SSet.{max u v}) ≅ sSet W.smallModel.cof W.smallModel.weq :=
  W.smallModelSSetIso
example : IsExact W.cof W.weq W.smallModel.cof W.smallModel.weq
    (AsSmall.up : C ⥤ Waldhausen.SmallModel C) := W.smallModel_up_exact
example : IsExact W.smallModel.cof W.smallModel.weq W.cof W.weq
    (AsSmall.down : Waldhausen.SmallModel C ⥤ C) := W.smallModel_down_exact
example : W.smallModelDeloopingHomeomorph W.kBasepoint = W.smallModel.kBasepoint :=
  W.smallModelDeloopingHomeomorph_basepoint
example (n : ℕ) : W.K n ≃* W.smallModel.K n := W.smallModelKEquiv n
example : Function.Bijective (W.smallModelKEquiv 0) := (W.smallModelKEquiv 0).bijective
example {F : C ⥤ D} (hF : IsExact W.cof W.weq W'.cof W'.weq F) (n : ℕ) :
    (W'.smallModelKEquiv n).toMonoidHom.comp (KMap hF n) =
      (KMap hF.smallModel n).comp (W.smallModelKEquiv n).toMonoidHom :=
  smallModelKEquiv_naturality hF n
example (he : ExtensionAxiom W) : ExtensionAxiom W.smallModel := W.smallModel_extensionAxiom he
example [W.weq.HasTwoOutOfThreeProperty] : W.smallModel.weq.HasTwoOutOfThreeProperty :=
  inferInstance

variable {W} (N : NestedWeakEquivalences W)
example : N.smallModel.coarse.cof = W.smallModel.cof := N.smallModel.cof_eq
example : N.smallModel.coarse.zero = W.smallModel.zero := N.smallModel.zero_eq
example : AcyclicCategory N ≌ AcyclicCategory N.smallModel := acyclicSmallEquivalence N
example : acyclicSmallDeloopingHomeomorph N (acyclicStructure N).kBasepoint =
    (acyclicStructure N.smallModel).kBasepoint := acyclicSmallDeloopingHomeomorph_basepoint N
example (t : unitInterval) (x : (acyclicStructure N).Delooping) :
    N.coarse.smallModelDeloopingHomeomorph (acyclicNullhomotopy N (t,x)) =
      acyclicNullhomotopy N.smallModel (t, acyclicSmallDeloopingHomeomorph N x) :=
  acyclicSmallNullhomotopy N t x
example (z : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :
    (smallModelChangeWeakFiberHomeomorph N z).val.1 = W.smallModelDeloopingHomeomorph z.val.1 := rfl
example (z : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) (t : unitInterval) :
    (smallModelChangeWeakFiberHomeomorph N z).val.2 t =
      N.coarse.smallModelDeloopingHomeomorph (z.val.2 t) := rfl
example : (smallModelChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun.comp (canonicalFiberMap N) =
    (canonicalFiberMap N.smallModel).comp (acyclicSmallDeloopingHomeomorph N).toHomotopyEquiv.toFun
      :=
  smallModel_canonicalFiberMap_square N
example (h : IsWeakHomotopyEquivalence (canonicalFiberMap N.smallModel)) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N) :=
  canonicalFiberMap_isWeakHomotopyEquivalence_of_smallModel N h
example (h : IsWeakHomotopyEquivalence (canonicalFiberMap N.smallModel)) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (canonicalFiberMap N)
      (canonicalFiberMap_basepoint N)) := by
  have transport (y : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint)
      (hy : canonicalFiberMap N (acyclicStructure N).kBasepoint = y) :
      Function.Bijective (homotopyGroupMap (N := Fin 0) (canonicalFiberMap N) hy) := by
    subst y
    exact (canonicalFiberMap_isWeakHomotopyEquivalence_of_smallModel N h).homotopy_bijective _ 0
  exact transport _ (canonicalFiberMap_basepoint N)

end Transport

open Quillen.Waldhausen.Fibration.RowFactorization

section

section
variable {C : Type u} [Category.{v} C] {W : Structure C}
  {N : NestedWeakEquivalences W} (D : JointData N)

example : JointData N.smallModel := D.smallModel

example (f : Arrow C) :
    (D.smallModel.inl.app ((AsSmall.up : C ⥤ SmallModel C).mapArrow.obj f)) =
      (AsSmall.up : C ⥤ SmallModel C).map (D.inl.app f) := rfl

example (f : Arrow C) :
    (D.smallModel.inr.app ((AsSmall.up : C ⥤ SmallModel C).mapArrow.obj f)) =
      (AsSmall.up : C ⥤ SmallModel C).map (D.inr.app f) := rfl

example (f : Arrow C) :
    (D.smallModel.projection.app ((AsSmall.up : C ⥤ SmallModel C).mapArrow.obj f)) =
      (AsSmall.up : C ⥤ SmallModel C).map (D.projection.app f) := rfl

example (hs : SecondEndpointSection N D) (f : Arrow (SmallModel C)) :
    D.smallModel.inr.app f ≫ (D.smallModel.joint.obj f).obj.hom ≫
      D.smallModel.projection.app f = 𝟙 f.right := hs.smallModel f

end

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckGroup.SmallModel
public import Quillen.Waldhausen.GrothendieckComparison.Equivalence

/-! # The original classical K₀ comparison in independent universes

The existing genuine common-universe model preserves the actual original
object loop under its original based realization homeomorphism. Composing
its checked K-equivalence with the original up/down algebraic presentation
maps gives the comparison on the unchanged original category and K₀.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The existing actual universe-lifting simplicial map preserves the original object simplex. -/
theorem smallModelSSetIso_objectSimplex (A : C) :
    W.smallModelSSetIso.hom.app (op ⦋1⦌) (W.kZeroObjectSimplex A) =
      W.smallModel.kZeroObjectSimplex (AsSmall.up.obj A) := by
  apply Subtype.ext
  change (intervalProjection ⦋1⦌ ⋙ QuotientRows.oneDiagram W A) ⋙ AsSmall.up =
    intervalProjection ⦋1⦌ ⋙ QuotientRows.oneDiagram W.smallModel (AsSmall.up.obj A)
  rw [Functor.assoc, QuotientRows.oneDiagram_postcompose W W.smallModel
    W.smallModel_up_exact rfl]

/-- The existing actual based homeomorphism maps the unchanged original object loop. -/
theorem smallModelDeloopingHomeomorph_objectLoop (A : C) :
    ((W.kZeroObjectLoop A).map W.smallModelDeloopingHomeomorph.continuous).cast
      W.smallModelDeloopingHomeomorph_basepoint.symm
      W.smallModelDeloopingHomeomorph_basepoint.symm =
        W.smallModel.kZeroObjectLoop (AsSmall.up.obj A) := by
  ext t
  change SSet.toTop.map W.smallModelSSetIso.hom
    (realizationEdgePath (W.kZeroObjectEdge A) t) = _
  exact (realizationEdgePath_naturality_apply W.smallModelSSetIso.hom
    (W.kZeroObjectEdge A) t).trans
      (congrArg (fun e : (sSet W.smallModel.cof W.smallModel.weq) _⦋1⦌ ↦
        SSet.toTop.map (SSet.yonedaEquiv.symm e) (realizationInterval t))
          (W.smallModelSSetIso_objectSimplex A))

/-- The original homotopical small-model equivalence retains the original object-loop class. -/
@[simp] theorem smallModelKEquiv_objectClass (A : C) :
    W.smallModelKEquiv 0 (W.kZeroObjectClass A) =
      W.smallModel.kZeroObjectClass (AsSmall.up.obj A) := by
  apply W.smallModel.kZeroFundamentalGroupEquiv.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (homotopyGroupMap W.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
      W.smallModelDeloopingHomeomorph_basepoint (W.kZeroObjectClass A)) = _
  rw [pi1MulEquivFundamentalGroup_naturality]
  change FundamentalGroup.mapOfEq _ _
    (W.kZeroFundamentalGroupEquiv (W.kZeroObjectClass A)) = _
  rw [W.kZeroFundamentalGroupEquiv_objectClass,
    W.smallModel.kZeroFundamentalGroupEquiv_objectClass, FundamentalGroup.mapOfEq_apply]
  exact congrArg Path.Homotopic.Quotient.mk (W.smallModelDeloopingHomeomorph_objectLoop A)

end Quillen.Waldhausen.Structure
namespace Quillen.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The genuine original classical-to-homotopical equivalence, allowing
independent original object and morphism universes. -/
def grothendieckKZeroEquivOfSmallModel : Multiplicative (Group W) ≃* W.K 0 :=
  (smallModelGrothendieckEquiv W).toMultiplicative.trans
    ((grothendieckKZeroEquiv W.smallModel).trans (W.smallModelKEquiv 0).symm)

/-- Universe transport keeps the original object class and original topological object loop. -/
@[simp] theorem grothendieckKZeroEquivOfSmallModel_objectClass (A : C) :
    grothendieckKZeroEquivOfSmallModel W (Multiplicative.ofAdd (objectClass W A)) =
      W.kZeroObjectClass A := by
  apply (W.smallModelKEquiv 0).injective
  change W.smallModelKEquiv 0
    ((W.smallModelKEquiv 0).symm
      (grothendieckKZeroEquiv W.smallModel
        (Multiplicative.ofAdd (smallModelGrothendieckEquiv W (objectClass W A))))) = _
  rw [MulEquiv.apply_symm_apply, smallModelGrothendieckEquiv_objectClass,
    grothendieckKZeroEquiv_objectClass, W.smallModelKEquiv_objectClass]

/-- The inverse universe-bridge comparison retains every original object generator. -/
@[simp] theorem grothendieckKZeroEquivOfSmallModel_symm_objectClass (A : C) :
    (grothendieckKZeroEquivOfSmallModel W).symm (W.kZeroObjectClass A) =
      Multiplicative.ofAdd (objectClass W A) := by
  rw [← grothendieckKZeroEquivOfSmallModel_objectClass W A, MulEquiv.symm_apply_apply]

/-- The general comparison retains the exact existing small-model comparison square. -/
theorem smallModelKEquiv_grothendieckKZeroEquivOfSmallModel
    (a : Multiplicative (Group W)) :
    W.smallModelKEquiv 0 (grothendieckKZeroEquivOfSmallModel W a) =
      grothendieckKZeroEquiv W.smallModel
        (Multiplicative.ofAdd (smallModelGrothendieckEquiv W a.toAdd)) :=
  (W.smallModelKEquiv 0).apply_symm_apply _

variable {D : Type u} [Category.{v} D] (V : Structure D) (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Every original exact functor commutes with the independent-universe comparison,
using precisely the existing canonical rebased KMap. -/
theorem grothendieckKZeroEquivOfSmallModel_natural
    (a : Multiplicative (Group W)) :
    KMap hF 0 (grothendieckKZeroEquivOfSmallModel W a) =
      grothendieckKZeroEquivOfSmallModel V ((map W F hF).toMultiplicative a) := by
  apply (V.smallModelKEquiv 0).injective
  have hk := DFunLike.congr_fun (smallModelKEquiv_naturality hF 0)
    (grothendieckKZeroEquivOfSmallModel W a)
  change V.smallModelKEquiv 0 (KMap hF 0 (grothendieckKZeroEquivOfSmallModel W a)) =
    KMap hF.smallModel 0 (W.smallModelKEquiv 0 (grothendieckKZeroEquivOfSmallModel W a)) at hk
  rw [hk, smallModelKEquiv_grothendieckKZeroEquivOfSmallModel,
    smallModelKEquiv_grothendieckKZeroEquivOfSmallModel]
  have hs := DFunLike.congr_fun
    (grothendieckKZeroEquiv_natural W.smallModel V.smallModel (smallModelFunctor F) hF.smallModel)
    (Multiplicative.ofAdd (smallModelGrothendieckEquiv W a.toAdd))
  change KMap hF.smallModel 0
    (grothendieckKZeroEquiv W.smallModel
      (Multiplicative.ofAdd (smallModelGrothendieckEquiv W a.toAdd))) =
    grothendieckKZeroEquiv V.smallModel
      (Multiplicative.ofAdd (map W.smallModel (smallModelFunctor F) hF.smallModel
        (smallModelGrothendieckEquiv W a.toAdd))) at hs
  rw [hs, ← smallModelGrothendieckEquiv_natural W V F hF]
  rfl

/-- The actual inverse comparison is natural on every original homotopical K₀ class. -/
theorem grothendieckKZeroEquivOfSmallModel_symm_natural (x : W.K 0) :
    (grothendieckKZeroEquivOfSmallModel V).symm (KMap hF 0 x) =
      (map W F hF).toMultiplicative ((grothendieckKZeroEquivOfSmallModel W).symm x) := by
  apply (grothendieckKZeroEquivOfSmallModel V).injective
  rw [MulEquiv.apply_symm_apply]
  have h := grothendieckKZeroEquivOfSmallModel_natural W V F hF
    ((grothendieckKZeroEquivOfSmallModel W).symm x)
  simpa only [MulEquiv.apply_symm_apply] using h

/-- On matching-universe small categories, the new universe bridge is precisely
the already-proved original canonical comparison, not a second identification. -/
theorem grothendieckKZeroEquivOfSmallModel_eq
    {C₀ : Type u} [SmallCategory C₀] (W₀ : Structure C₀) :
    grothendieckKZeroEquivOfSmallModel W₀ = grothendieckKZeroEquiv W₀ := by
  have h : (grothendieckKZeroEquivOfSmallModel W₀ : Multiplicative (Group W₀) →* W₀.K 0) =
      (grothendieckKZeroEquiv W₀ : Multiplicative (Group W₀) →* W₀.K 0) := by
    apply mulHom_ext W₀
    intro A
    exact (grothendieckKZeroEquivOfSmallModel_objectClass W₀ A).trans
      (grothendieckKZeroEquiv_objectClass W₀ A).symm
  apply MulEquiv.ext
  intro a
  exact congrArg (fun f : Multiplicative (Group W₀) →* W₀.K 0 ↦ f a) h

end Quillen.Waldhausen.AlgebraicGrothendieck

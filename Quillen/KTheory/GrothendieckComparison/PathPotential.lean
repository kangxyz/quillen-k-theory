/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.GrothendieckComparison.EdgeCocycle
public import Quillen.Topology.ClassifyingSpace.CompletionNaturality
public import Quillen.Topology.ClassifyingSpace.PathPotential

/-!
# Grothendieck potentials for actual paths projected to Q

A coboundary formula for the original Q-cocycle supplies a natural transformation
into the actual fundamental groupoid. Its naturality then applies to every
continuous path between original source vertices.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w z
open CategoryTheory CategoryTheory.Limits
open scoped Topology
namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The unchanged algebraic comparison followed by the original fundamental-group identification. -/
def grothendieckLoopClass : Multiplicative E.GrothendieckGroup →*
    End ((classifyingFundamentalGroupoidFunctor E.QCategory).obj E.qZero) :=
  E.kZeroFundamentalGroupEquiv.toMonoidHom.comp E.grothendieckToKZero

/-- The realized original closed edge has its original cocycle class. -/
theorem qEdgeClass_eq_grothendieckLoopClass {X Y : E.QCategory} (f : X ⟶ Y) :
    E.qEdgeClass (classifyingFundamentalGroupoidFunctor E.QCategory) f =
      E.grothendieckLoopClass (Multiplicative.ofAdd (E.qGrothendieckWeight f)) := by
  have h := congrArg E.kZeroFundamentalGroupEquiv (E.kZeroEdgeClass_eq_grothendieckToKZero f)
  dsimp only [grothendieckLoopClass, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  erw [MonoidHom.comp_apply, ← h]
  exact (E.kZeroFundamentalGroupEquiv.apply_symm_apply _).symm

variable {D : Type w} [Category.{z} D] (F : D ⥤ E.QCategory)
  (φ : D → E.GrothendieckGroup)
  (hφ : ∀ {a b : D} (f : a ⟶ b),
    E.qGrothendieckWeight (F.map f) = φ a - φ b)

/-- A cocycle potential gives a natural transformation in the actual fundamental groupoid. -/
def qCocyclePotential :
    F ⋙ classifyingFundamentalGroupoidFunctor E.QCategory ⟶
      (Functor.const D).obj
        ((classifyingFundamentalGroupoidFunctor E.QCategory).obj E.qZero) where
  app a := inv ((classifyingFundamentalGroupoidFunctor E.QCategory).map
    (E.fromZero (F.obj a))) ≫ E.grothendieckLoopClass (Multiplicative.ofAdd (φ a))
  naturality {a b} f := by
    dsimp only [Functor.comp_map]
    change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ 𝟙 _
    rw [Category.comp_id]
    apply (cancel_epi ((classifyingFundamentalGroupoidFunctor E.QCategory).map
      (E.fromZero (F.obj a)))).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    have he := E.qEdgeClass_eq_grothendieckLoopClass (F.map f)
    dsimp only [qEdgeClass] at he
    rw [← Category.assoc] at he
    rw [he]
    rw [hφ]
    change E.grothendieckLoopClass (Multiplicative.ofAdd (φ b)) *
      E.grothendieckLoopClass (Multiplicative.ofAdd (φ a - φ b)) = _
    rw [← map_mul]
    apply congrArg E.grothendieckLoopClass
    change Multiplicative.ofAdd (φ b + (φ a - φ b)) = Multiplicative.ofAdd (φ a)
    congr 1
    abel

/-- The same potential keeps the exact point-equality correction of the original realization map. -/
def realizedQCocyclePotential :
    classifyingFundamentalGroupoidFunctor D ⋙
      FundamentalGroupoid.map (classifyingSpaceMapUniversal F) ⟶
        (Functor.const D).obj ((classifyingFundamentalGroupoidFunctor E.QCategory).obj E.qZero) :=
  (classifyingFundamentalGroupoidUniversalNaturality F).hom ≫ E.qCocyclePotential F φ hφ

end Quillen.ExactStructure

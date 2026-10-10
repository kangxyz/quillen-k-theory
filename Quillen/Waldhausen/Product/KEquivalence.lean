/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Product.SSet
public import Quillen.Topology.Realization.ProductComparison

/-! # Actual product K-groups by the original projection maps

The strict S-product isomorphism and compact-source lifting of the canonical
realization-product comparison give the group equivalence. Its forward map
is definitionally the pair of the original canonical Waldhausen K-maps.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial Topology
universe u v

namespace Quillen.Waldhausen.Product
open ExtensionCategory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D)

/-- The original pair of actual projection realization maps. -/
def deloopingComparison : C((productStructure V W).Delooping, V.Delooping × W.Delooping) :=
  (deloopingMap (fst_exact V W)).hom.prodMk (deloopingMap (snd_exact V W)).hom

/-- The topological comparison factors through the strict S-product isomorphism. -/
theorem deloopingComparison_factor :
    deloopingComparison V W =
      (ProductRealization.comparison (sSet V.cof V.weq) (sSet W.cof W.weq)).comp
        (SSet.toTop.map (sSetIso V W).hom).hom := by
  apply ContinuousMap.ext
  intro p
  apply _root_.Prod.ext
  · exact (ConcreteCategory.congr_hom (show
      SSet.toTop.map (sSetIso V W).hom ≫
          CartesianMonoidalCategory.prodComparison SSet.toTop _ _ ≫
            CartesianMonoidalCategory.fst _ _ = deloopingMap (fst_exact V W) by
        simp [sSetIso, ← CategoryTheory.Functor.map_comp, deloopingMap]) p).symm
  · exact (ConcreteCategory.congr_hom (show
      SSet.toTop.map (sSetIso V W).hom ≫
          CartesianMonoidalCategory.prodComparison SSet.toTop _ _ ≫
            CartesianMonoidalCategory.snd _ _ = deloopingMap (snd_exact V W) by
        simp [sSetIso, ← CategoryTheory.Functor.map_comp, deloopingMap]) p).symm

/-- The actual product realization map is injective. -/
theorem deloopingComparison_injective : Function.Injective (deloopingComparison V W) := by
  rw [deloopingComparison_factor]
  exact (ProductRealization.comparison_injective _ _).comp
    (TopCat.homeoOfIso (SSet.toTop.mapIso (sSetIso V W))).injective

/-- Actual compact-source lifts transfer along the strict S-product homeomorphism. -/
theorem deloopingComparison_compact_lifts : HasCompactSourceLifts (deloopingComparison V W) := by
  intro T _ _ f
  obtain ⟨g, hg⟩ := ProductRealization.comparison_compact_lifts
    (sSet V.cof V.weq) (sSet W.cof W.weq) T f
  refine ⟨(SSet.toTop.map (sSetIso V W).inv).hom.comp g, ?_⟩
  rw [deloopingComparison_factor]
  apply ContinuousMap.ext
  intro t
  change ProductRealization.comparison _ _
    ((SSet.toTop.map (sSetIso V W).inv ≫ SSet.toTop.map (sSetIso V W).hom) (g t)) = f t
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  exact DFunLike.congr_fun hg t

/-- Chosen zero is retained literally by the two original projection functors. -/
theorem deloopingComparison_basepoint :
    deloopingComparison V W (productStructure V W).kBasepoint = (V.kBasepoint, W.kBasepoint) :=
  _root_.Prod.ext (deloopingMap_basepoint_of_zeroEq (fst_exact V W) rfl)
    (deloopingMap_basepoint_of_zeroEq (snd_exact V W) rfl)

/-- The canonical product homomorphism uses the original public K-maps. -/
def KMapPair (n : ℕ) : (productStructure V W).K n →* V.K n × W.K n :=
  (KMap (fst_exact V W) n).prod (KMap (snd_exact V W) n)

/-- Exact identification with the actual based product comparison. -/
theorem KMapPair_eq_piMap (n : ℕ) :
    KMapPair V W n = (piProdMap n V.kBasepoint W.kBasepoint).comp
      (piMap n (deloopingComparison V W) (deloopingComparison_basepoint V W)) := by
  unfold KMapPair
  rw [KMap_eq_piMap_of_zeroEq (fst_exact V W) rfl n,
    KMap_eq_piMap_of_zeroEq (snd_exact V W) rfl n]
  apply MonoidHom.ext
  intro a
  induction a using Quotient.inductionOn with | h p =>
    apply _root_.Prod.ext <;> rfl

/-- The pair of original canonical projection K-maps is bijective in every degree. -/
theorem KMapPair_bijective (n : ℕ) : Function.Bijective (KMapPair V W n) := by
  rw [KMapPair_eq_piMap]
  exact (piProdMap_bijective n V.kBasepoint W.kBasepoint).comp
    (piMap_bijective_of_compact_lifts (deloopingComparison V W)
      (deloopingComparison_injective V W) (deloopingComparison_compact_lifts V W)
      (deloopingComparison_basepoint V W) n)

/-- Actual product K-theory, including K₀, via the original canonical projections. -/
def KEquiv (n : ℕ) : (productStructure V W).K n ≃* V.K n × W.K n :=
  MulEquiv.ofBijective (KMapPair V W n) (KMapPair_bijective V W n)

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem KEquiv_coe (n : ℕ) :
    (↑(KEquiv V W n) : (productStructure V W).K n →* V.K n × W.K n) = (KMap (fst_exact V W)
        n).prod (KMap (snd_exact V W) n) := rfl


end Quillen.Waldhausen.Product

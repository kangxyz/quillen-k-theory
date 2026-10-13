/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.Functoriality
public import Quillen.Waldhausen.SConstruction.WeakNaturalTransformationNaturality
public import Quillen.Topology.Realization.HomotopySquare
public import Quillen.Topology.HomotopyFiber.BasedLESNaturality

/-!
# Entire original canonical-fiber naturality

For a strictly chosen-zero-preserving exact functor on a nested pair, the
actual cylinder, reversed nullhomotopy and canonical fiber map commute.
The whole path coordinate is proved; no comparison square is a premise.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D}
  (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W)
  {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)

lemma acyclicCylinder_natural (h0 : F.obj V.zero = W.zero) :
    weakNaturalTransformationCylinder (acyclicStructure N) N.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
      (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) ≫ sSetMap hFc =
    sSetMap (acyclicFunctor_exact N M hF hFc) ▷ Δ[1] ≫
      weakNaturalTransformationCylinder (acyclicStructure M) M.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact M)
        (zeroToAcyclicInclusion M) (zeroToAcyclicInclusion_weak M) := by
  ext n z : 4
  apply Subtype.ext
  change nerveCylinderDiagram (whiskerLeft z.1.val (zeroToAcyclicInclusion N)) z.2.down ⋙ F =
    nerveCylinderDiagram (whiskerLeft (z.1.val ⋙ acyclicFunctor N M hFc)
      (zeroToAcyclicInclusion M)) z.2.down
  rw [nerveCylinderDiagram_postcomp]
  apply nerveCylinderDiagram_congr_app _ _ _ rfl _
  · refine CategoryTheory.Functor.ext (fun _ => coarse_zero_eq N M h0) ?_
    intro i j f
    exact (hFc.zero N.coarse.isZero).eq_of_src _ _
  · intro p
    have he : F.map ((zeroToAcyclicInclusion N).app (z.1.val.obj p)) =
        eqToHom (coarse_zero_eq N M h0) ≫
          (zeroToAcyclicInclusion M).app ((acyclicFunctor N M hFc).obj (z.1.val.obj p)) :=
      (hFc.zero N.coarse.isZero).eq_of_src _ _
    exact (heq_of_eq he).trans (eqToHom_comp_heq _ (coarse_zero_eq N M h0))

lemma acyclicNullhomotopy_natural (h0 : F.obj V.zero = W.zero) (t : unitInterval)
    (x : (acyclicStructure N).Delooping) :
    deloopingMap hFc (acyclicNullhomotopy N (t, x)) =
      acyclicNullhomotopy M (t, deloopingMap (acyclicFunctor_exact N M hF hFc) x) := by
  exact realizationSimplicialHomotopy_square
    (weakNaturalTransformationHomotopy (acyclicStructure N) N.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
      (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N))
    (weakNaturalTransformationHomotopy (acyclicStructure M) M.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact M)
      (zeroToAcyclicInclusion M) (zeroToAcyclicInclusion_weak M))
    (sSetMap (acyclicFunctor_exact N M hF hFc)) (sSetMap hFc)
    (acyclicCylinder_natural N M hF hFc h0) (unitInterval.symm t) x


/-- The canonical homotopy-fiber map induced by the exact functor and its zero equality. -/
def fiberFunctorMap (h0 : F.obj V.zero = W.zero) : C(
    HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint,
    HomotopyFiber (changeWeakMap M) M.coarse.kBasepoint) :=
  HomotopyFiber.mapAt (deloopingMap hF).hom (deloopingMap hFc).hom
    (changeWeakMap_natural N M hF hFc) N.coarse.kBasepoint M.coarse.kBasepoint
    (deloopingMap_basepoint_of_zeroEq hFc (coarse_zero_eq N M h0))

lemma fiberFunctorMap_basepoint (h0 : F.obj V.zero = W.zero) :
    fiberFunctorMap N M hF hFc h0 (HomotopyFiber.basepoint (changeWeakMap N)
      N.coarse.kBasepoint V.kBasepoint (changeWeakMap_basepoint N)) =
    HomotopyFiber.basepoint (changeWeakMap M) M.coarse.kBasepoint W.kBasepoint
      (changeWeakMap_basepoint M) :=
  HomotopyFiber.mapAt_basepoint (deloopingMap hF).hom (deloopingMap hFc).hom
    (changeWeakMap_natural N M hF hFc) V.kBasepoint N.coarse.kBasepoint
    W.kBasepoint M.coarse.kBasepoint (changeWeakMap_basepoint N) (changeWeakMap_basepoint M)
    (deloopingMap_basepoint_of_zeroEq hF h0)
    (deloopingMap_basepoint_of_zeroEq hFc (coarse_zero_eq N M h0))

lemma canonicalFiberMap_natural (h0 : F.obj V.zero = W.zero) :
    (fiberFunctorMap N M hF hFc h0).comp (canonicalFiberMap N) =
    (canonicalFiberMap M).comp (deloopingMap (acyclicFunctor_exact N M hF hFc)).hom := by
  ext x : 1
  apply Subtype.ext
  apply Prod.ext
  · exact ContinuousMap.congr_fun (acyclicInclusionMap_natural N M hF hFc) x
  · exact ContinuousMap.ext (fun t => acyclicNullhomotopy_natural N M hF hFc h0 t x)

lemma canonicalFiberKMap_natural (h0 : F.obj V.zero = W.zero) (n : ℕ) :
    (piMap n (fiberFunctorMap N M hF hFc h0) (fiberFunctorMap_basepoint N M hF hFc h0)).comp
      (canonicalFiberKMap N n) =
    (canonicalFiberKMap M n).comp (KMap (acyclicFunctor_exact N M hF hFc) n) := by
  rw [KMap_eq_piMap_of_zeroEq (acyclicFunctor_exact N M hF hFc)
    (acyclicFunctor_zero N M hFc h0) n]
  unfold canonicalFiberKMap
  rw [← homotopyGroupMapHom_comp, ← homotopyGroupMapHom_comp]
  congr 1
  exact canonicalFiberMap_natural N M hF hFc h0

end Quillen.Waldhausen.Fibration

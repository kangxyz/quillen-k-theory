/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.PullbackNaturality
import Quillen.PerfectComplexes.GilletWaldhausen

/-!
# Contravariant strict-perfect K-theory on all schemes

The functor uses the actual geometric strict-perfect K-map. The original
vector-bundle comparison gives a natural isomorphism from `Scheme.KFunctor`,
with explicitly identified forward and inverse components. Pullback is not
defined by transporting the vector-bundle K-map along that equivalence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated CochainComplex
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- Strict-perfect K-theory, with maps induced by actual geometric pullback. -/
def StrictKFunctor (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (StrictK X.unop n)
  map f := GrpCat.ofHom (strictKPullback f.unop n)
  map_id X := by
    apply GrpCat.hom_ext
    exact strictKPullback_id X.unop n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact strictKPullback_comp g.unop f.unop n

@[simp] theorem StrictKFunctor_map {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) (n : ℕ) :
    ((StrictKFunctor n).map f).hom = strictKPullback f.unop n := rfl

/-- The existing vector-bundle/strict-perfect equivalence is natural for every
scheme morphism, without defining pullback by transport along that equivalence. -/
def vectorBundleToStrictNatIso (n : ℕ) :
    Quillen.Scheme.KFunctor.{u} n ≅ StrictKFunctor n :=
  NatIso.ofComponents
    (fun X ↦ (vectorBundleToStrictKEquiv X.unop n).toGrpIso)
    (fun f ↦ by
      apply GrpCat.hom_ext
      exact (vectorBundleToStrictKMap_pullback f.unop n).symm)

@[simp] theorem vectorBundleToStrictNatIso_hom_app (n : ℕ) (X : Scheme.{u}ᵒᵖ) :
    ((vectorBundleToStrictNatIso n).hom.app X).hom =
      vectorBundleToStrictKMap X.unop n := rfl

@[simp] theorem vectorBundleToStrictNatIso_inv_app (n : ℕ) (X : Scheme.{u}ᵒᵖ) :
    ((vectorBundleToStrictNatIso n).inv.app X).hom =
      (vectorBundleToStrictKEquiv X.unop n).symm.toMonoidHom := rfl

/-- The inverse of the original comparison also commutes with pullback. -/
theorem vectorBundleToStrictKEquiv_symm_pullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    (Quillen.Scheme.pullbackK f n).comp
        (vectorBundleToStrictKEquiv Y n).symm.toMonoidHom =
      (vectorBundleToStrictKEquiv X n).symm.toMonoidHom.comp (strictKPullback f n) := by
  exact (GrpCat.hom_ext_iff.mp ((vectorBundleToStrictNatIso n).inv.naturality f.op)).symm
end Quillen.PerfectComplexes

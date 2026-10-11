/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.KZeroFunctor
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback
public import Quillen.Waldhausen.SConstruction.Iterated.StableFunctoriality

/-!
# Original affine K-zero and bounded-flat stable groups

The original inclusion equivalence and original stable-group comparison identify the unchanged
perfect K-zero functor with degree zero of the raw bounded-flat prespectrum, retaining every
original coefficient pullback map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The original perfect K-zero group computes the raw bounded-flat degree-zero stable group. -/
def boundedFlatAffineStableKZeroIso (R : CommRingCat.{u}) :
    Quillen.Bass.affineKZeroFunctor.obj R ≅
      stableHomotopyGroup (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))) 0 :=
  ((boundedFlatPerfectKEquiv (Spec R) 0).symm.toAdditive.trans
    (originalKStableEquiv (boundedFlatPerfectWaldhausen (Spec R)) 0)).toAddCommGrpIso

/-- Original coefficient maps agree on every original perfect K-zero representative. -/
theorem boundedFlatAffineStableKZeroIso_naturality_apply {R S : CommRingCat.{u}}
    (f : R ⟶ S) (a : PerfectK (Spec R) 0) :
    (stableHomotopyFunctor 0).map (boundedFlatPerfectPrespectrumMap (Spec.map f))
      ((boundedFlatAffineStableKZeroIso R).hom (Additive.ofMul a)) =
    (boundedFlatAffineStableKZeroIso S).hom
      (Additive.ofMul (perfectKPullback (Spec.map f) 0 a)) := by
  change exactStableKMap (boundedFlatPerfectWaldhausen (Spec R))
      (boundedFlatPerfectWaldhausen (Spec S)) (boundedFlatPerfectPullback_exact (Spec.map f)) 0
      (originalKStableEquiv (boundedFlatPerfectWaldhausen (Spec R)) 0
        (Additive.ofMul ((boundedFlatPerfectKEquiv (Spec R) 0).symm a))) =
    originalKStableEquiv (boundedFlatPerfectWaldhausen (Spec S)) 0
      (Additive.ofMul ((boundedFlatPerfectKEquiv (Spec S) 0).symm
        (perfectKPullback (Spec.map f) 0 a)))
  have h := originalKStableEquiv_exact_naturality (boundedFlatPerfectWaldhausen (Spec R))
    (boundedFlatPerfectWaldhausen (Spec S)) (boundedFlatPerfectPullback_exact (Spec.map f)) 0
    ((boundedFlatPerfectKEquiv (Spec R) 0).symm a)
  refine h.symm.trans ?_
  congr 2
  simp only [perfectKPullback, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, boundedFlatPerfectKPullback]

/-- The comparison intertwines the unchanged original ring-map arrows. -/
@[reassoc]
theorem boundedFlatAffineStableKZeroIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffineStableKZeroIso R).hom ≫
      (stableHomotopyFunctor 0).map (boundedFlatPerfectPrespectrumMap (Spec.map f)) =
    Quillen.Bass.affineKZeroFunctor.map f ≫ (boundedFlatAffineStableKZeroIso S).hom := by
  ext a
  exact boundedFlatAffineStableKZeroIso_naturality_apply f a.toMul

end Quillen.PerfectComplexes

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PullbackHomotopy

/-! Both original geometric routes survive the normalized relative comparison for arbitrary maps. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.BoundedFlatTriplePullback

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

lemma original_left_route :
    (boundedFlatPerfectTriplePullbackHomotopy f g h).at 0 =
      (exactOriginalPrespectrumIsoHomotopy (boundedFlatPerfectWaldhausen T)
        (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectPullback_exact (f ≫ g ≫ h))
        ((boundedFlatPerfectPullback_exact (g ≫ h)).comp (boundedFlatPerfectPullback_exact f))
        (boundedFlatPerfectPullbackCompIso f (g ≫ h))).trans
      (exactOriginalPrespectrumIsoHomotopy (boundedFlatPerfectWaldhausen T)
        (boundedFlatPerfectWaldhausen X)
        ((boundedFlatPerfectPullback_exact (g ≫ h)).comp (boundedFlatPerfectPullback_exact f))
        ((boundedFlatPerfectPullback_exact h).comp
          ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f)))
        (Functor.isoWhiskerRight (boundedFlatPerfectPullbackCompIso g h)
          (boundedFlatPerfectPullback f) ≪≫
            Functor.associator (boundedFlatPerfectPullback h) (boundedFlatPerfectPullback g)
              (boundedFlatPerfectPullback f))) :=
  (boundedFlatPerfectTriplePullbackHomotopy f g h).at_zero

lemma original_right_route :
    (boundedFlatPerfectTriplePullbackHomotopy f g h).at 1 =
      (exactOriginalPrespectrumIsoHomotopy (boundedFlatPerfectWaldhausen T)
        (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectPullback_exact (f ≫ g ≫ h))
        ((boundedFlatPerfectPullback_exact h).comp (boundedFlatPerfectPullback_exact (f ≫ g)))
        (eqToIso (congrArg boundedFlatPerfectPullback (Category.assoc f g h).symm) ≪≫
          boundedFlatPerfectPullbackCompIso (f ≫ g) h)).trans
      (exactOriginalPrespectrumIsoHomotopy (boundedFlatPerfectWaldhausen T)
        (boundedFlatPerfectWaldhausen X)
        ((boundedFlatPerfectPullback_exact h).comp (boundedFlatPerfectPullback_exact (f ≫ g)))
        ((boundedFlatPerfectPullback_exact h).comp
          ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f)))
        (Functor.isoWhiskerLeft (boundedFlatPerfectPullback h)
          (boundedFlatPerfectPullbackCompIso f g))) :=
  (boundedFlatPerfectTriplePullbackHomotopy f g h).at_one

end Quillen.Tests.BoundedFlatTriplePullback

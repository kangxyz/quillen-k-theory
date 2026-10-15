/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassInclusionSourceLeg
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Compatibility of the original Bass Laurent nullhomotopies with inclusion

The proved positive-chart inclusion pasting and actual source-leg cone square compare the two
unchanged Laurent nullhomotopies. Every original cone and homotopy parameter is retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.BassInclusionNullTrack
variable (R : CommRingCat.{u})

/-- The original positive leg followed by Laurent inclusion and perfect cone inclusion. -/
def oldPositive :=
  ((boundedFlatLaurentPlusHomotopy R).postcomp (exactOriginalPrespectrumMap
    (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
    (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
    (boundedFlatPerfectInclusion_exact _))).postcomp (mappingConeInclusion (bassSquareComparison R))

/-- The original positive Laurent inclusion square, preceded by the bounded-flat projection. -/
def positiveMovement :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentPlus R))).postcomp
      (mappingConeInclusion (bassSquareComparison R))

/-- The original polynomial inclusion square followed by the perfect positive Laurent leg. -/
def polynomialMovement :=
  ((boundedFlatPerfectInclusionFlatPullbackHomotopy (polynomialProjection R)).postcomp
    (perfectFlatPrespectrumMap (laurentPlus R))).postcomp
      (mappingConeInclusion (bassSquareComparison R))

/-- The exact original Laurent projection inclusion track followed by perfect cone inclusion. -/
def laurentMovement :=
  (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentProjection R)).postcomp
    (mappingConeInclusion (bassSquareComparison R))

/-- The original perfect positive-leg track preceded by the original base inclusion. -/
def newPositive :=
  (Homotopy.precomp (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
    (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _))
    (laurentPlusHomotopy R)).postcomp (mappingConeInclusion (bassSquareComparison R))

/-- The proved original positive-chart inclusion pasting retains its entire perfect-cone image. -/
def positivePasting :
    ((positiveMovement R).trans (polynomialMovement R)).RelHomotopy
      ((oldPositive R).symm.trans ((laurentMovement R).trans (newPositive R))) := by
  simpa only [boundedFlatPerfectPlusInclusionLeftTrack,
    boundedFlatPerfectPlusInclusionRightTrack, Homotopy.postcomp_trans, Homotopy.postcomp_symm,
    positiveMovement, polynomialMovement, oldPositive, laurentMovement, newPositive] using
    (boundedFlatPerfectPlusInclusionPasting R).postcomp
      (mappingConeInclusion (bassSquareComparison R))

/-- Genuine inverse-track cancellation straightens the original three-track positive route. -/
def straightPositivePasting :
    (((oldPositive R).trans (positiveMovement R)).trans
      (polynomialMovement R)).RelHomotopy
        ((laurentMovement R).trans (newPositive R)) := by
  let A := oldPositive R
  let B := positiveMovement R
  let P := polynomialMovement R
  let T := (laurentMovement R).trans (newPositive R)
  exact (Homotopy.RelHomotopy.transAssoc A B P).trans
    (((Homotopy.RelHomotopy.refl A).hcomp (positivePasting R)).trans
      ((Homotopy.RelHomotopy.transAssoc A A.symm T).symm.trans
        (((Homotopy.RelHomotopy.reflTransSymm A).symm.hcomp
          (Homotopy.RelHomotopy.refl T)).trans (Homotopy.RelHomotopy.reflTrans T))))

/-- The image of the old source leg traverses the unchanged perfect cone cylinder. -/
def oldCone : Homotopy
    (((boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
      exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (Polynomial R)))) (boundedFlatPerfectInclusion_exact _)) ≫
      perfectFlatPrespectrumMap (laurentPlus R)) ≫ mappingConeInclusion (bassSquareComparison R))
    (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatBassSourceLeg R ≫ boundedFlatPerfectFlatPullbackPushoutMap
    (polynomialProjection R) (polynomialProjection R))
    (mappingConeHomotopy (bassSquareComparison R))).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) rfl

/-- The included base source leg traverses the same original perfect cone cylinder. -/
def newCone : Homotopy
    (((exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
      (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _) ≫
      perfectFlatPrespectrumMap (polynomialProjection R)) ≫
      perfectFlatPrespectrumMap (laurentPlus R)) ≫ mappingConeInclusion (bassSquareComparison R))
    (zeroHom _ _) :=
  (Homotopy.precomp (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
    (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _) ≫ bassSourceLeg R)
    (mappingConeHomotopy (bassSquareComparison R))).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) rfl

/-- The original source-leg cone square supplies its complete polynomial-movement pasting. -/
def conePasting :
    (oldCone R).RelHomotopy ((polynomialMovement R).trans (newCone R)) := by
  let Z := Quillen.LoopPrespectrum.Homotopy.refl (zeroHom
    (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R)))
    (mappingCone (bassSquareComparison R)))
  have J : (oldCone R).RelHomotopy
      (((polynomialMovement R).trans (newCone R)).trans Z) := by
    refine (boundedFlatPerfectBassSourceLegConeBoundary R).ofLevels _ _ ?_ ?_
    · intro n
      rfl
    · intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr
        · apply ContinuousMap.ext
          rintro ⟨s, x⟩
          rfl
        · rfl
      · rfl
  exact J.trans (Homotopy.RelHomotopy.transRefl _)

/-- The original positive geometry and actual cone square paste to the perfect null route. -/
def pastedNullComparison :
    ((oldPositive R).trans ((positiveMovement R).trans (oldCone R))).RelHomotopy
      ((laurentMovement R).trans ((newPositive R).trans (newCone R))) := by
  let A := oldPositive R
  let B := positiveMovement R
  let P := polynomialMovement R
  let E := oldCone R
  let G := newCone R
  let L := laurentMovement R
  let F := newPositive R
  exact (Homotopy.RelHomotopy.transAssoc A B E).symm.trans
    (((Homotopy.RelHomotopy.refl (A.trans B)).hcomp (conePasting R)).trans
      ((Homotopy.RelHomotopy.transAssoc (A.trans B) P G).symm.trans
        (((straightPositivePasting R).hcomp (Homotopy.RelHomotopy.refl G)).trans
          (Homotopy.RelHomotopy.transAssoc L F G))))

/-- The unchanged bounded-flat nullhomotopy followed by the actual proved geometric cone map. -/
def originalOldNull : Homotopy
    ((boundedFlatPerfectPrespectrumMap (laurentProjection R) ≫ exactOriginalPrespectrumMap
      (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (boundedFlatPerfectInclusion_exact _)) ≫ mappingConeInclusion (bassSquareComparison R))
    (zeroHom _ _) :=
  ((boundedFlatBassLaurentNullHomotopy R).postcomp
    (boundedFlatPerfectGeometricBassConeMap R)).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) (by
        apply Hom.ext
        funext n
        ext x
        exact (boundedFlatPerfectGeometricBassConeMap R).map_point n)

/-- The unchanged perfect nullhomotopy preceded by the original base inclusion. -/
def originalNewNull : Homotopy
    ((exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
      (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _) ≫
      perfectFlatPrespectrumMap (laurentProjection R)) ≫
      mappingConeInclusion (bassSquareComparison R))
    (zeroHom _ _) :=
  (Homotopy.precomp (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
    (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _))
    (bassLaurentNullHomotopy R)).cast (Category.assoc _ _ _).symm rfl

/-- The original perfect Laurent-null transport is exactly its literal endpoint cast. -/
theorem perfectLaurentNull_eq_cast :
    bassLaurentNullHomotopy R =
      ((laurentPlusHomotopy R).postcomp (mappingConeInclusion (bassSquareComparison R))).trans
        ((Homotopy.precomp (bassSourceLeg R)
          (mappingConeHomotopy (bassSquareComparison R))).cast
            (congrArg (fun k ↦ k ≫ mappingConeInclusion (bassSquareComparison R))
              (bassSourceLeg_comparison R)) rfl) := by
  unfold bassLaurentNullHomotopy
  congr 1

private theorem precomp_postcomp_level {D E F G : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (h : D ⟶ E) (H : Homotopy f g) (k : F ⟶ G) (n : ℕ) :
    (Homotopy.precomp h (H.postcomp k)).level n =
      ((Homotopy.precomp h H).postcomp k).level n := rfl

private theorem precomp_cast_level {D E F : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} (h : D ⟶ E) (H : Homotopy f g)
    (ef : f = f') (eg : g = g') (n : ℕ) :
    (Homotopy.precomp h (H.cast ef eg)).level n = (Homotopy.precomp h H).level n := rfl

private theorem precomp_precomp_level {D E F G : LoopPrespectrum.{u}}
    {f g : F ⟶ G} (h : D ⟶ E) (k : E ⟶ F) (H : Homotopy f g) (n : ℕ) :
    (Homotopy.precomp h (Homotopy.precomp k H)).level n =
      (Homotopy.precomp (h ≫ k) H).level n := rfl

/-- Every original perfect-null coordinate is the unchanged positive leg and cone cylinder. -/
theorem originalNewNull_level (n : ℕ) :
    (originalNewNull R).level n = ((newPositive R).trans (newCone R)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level, perfectLaurentNull_eq_cast, Homotopy.precomp_trans]
  apply Homotopy.trans_level_congr
  · exact precomp_postcomp_level _ _ _ n
  · rw [precomp_cast_level, precomp_precomp_level, newCone, Homotopy.cast_level]

/-- Mapped old-null coordinates retain the original positive leg and cone-square map. -/
theorem originalOldNull_level (n : ℕ) :
    (originalOldNull R).level n =
      ((oldPositive R).trans ((positiveMovement R).trans (oldCone R))).level n := by
  unfold originalOldNull
  rw [Homotopy.cast_level]
  change ((((boundedFlatLaurentPlusHomotopy R).postcomp
    (mappingConeInclusion (boundedFlatBassSquareComparison R))).trans
      (Homotopy.precomp (boundedFlatBassSourceLeg R)
        (mappingConeHomotopy (boundedFlatBassSquareComparison R)))).postcomp
          (boundedFlatPerfectGeometricBassConeMap R)).level n = _
  rw [Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    rfl
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    rfl

/-- The two unchanged Laurent nullhomotopies compare along the original Laurent inclusion track. -/
def originalNullComparison :
    (originalOldNull R).RelHomotopy ((laurentMovement R).trans (originalNewNull R)) := by
  refine (pastedNullComparison R).ofLevels _ _ (originalOldNull_level R) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level R n

end Quillen.PerfectComplexes.BassInclusionNullTrack

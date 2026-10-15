/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveStageComponents
public import Quillen.KTheory.Plus.ProjectiveTelescopeFactorization
public import Quillen.Topology.LocalCoefficients.HomotopyCorrection

/-! # The original two projective factorization tracks and finite abelian correction -/

@[expose] public section

open Quillen.LocalCoefficients

noncomputable section
open CategoryTheory MonoidalCategory
universe u
namespace Quillen.FiniteProjectiveModule
open LocalCoefficients
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (R : Type u) [Ring R]

/-- Common starting functor: right stabilization followed by the distinguished left addition. -/
def projectiveTrackSource (P : IsoCategory Rᵐᵒᵖ) (k : ℕ) :
    ProjectiveStage R ⥤ ProjectiveStage R :=
  AsSmall.down ⋙ EndofunctorTelescope.iterate (tensorRight (freeIso Rᵐᵒᵖ 1)) k ⋙
    tensorLeft P ⋙ AsSmall.up

/-- Common ending functor of the two actual factorization routes. -/
def projectiveTrackTarget (P Q : IsoCategory Rᵐᵒᵖ) :
    ProjectiveStage R ⥤ ProjectiveStage R :=
  projectiveStageRight R Q ⋙ projectiveStageLeft R P ⋙ projectiveStageLeft R P

/-- The upper route retains the specified finite complement factorization. -/
def projectiveUpperTrack (P Q : IsoCategory Rᵐᵒᵖ) (k : ℕ)
    (f : P ⊗ Q ≅ freeIso Rᵐᵒᵖ k) :
    projectiveTrackSource R P k ≅ projectiveTrackTarget R P Q :=
  Functor.isoWhiskerLeft AsSmall.down (Functor.isoWhiskerRight
    (TranslationTelescope.factorizationUpperTrack (freeIso Rᵐᵒᵖ 1) P Q k
      (rightIterationComplementIso R P Q k f)) AsSmall.up)

/-- The lower route retains the iterated commuting square and its associator correction. -/
def projectiveLowerTrack (P Q : IsoCategory Rᵐᵒᵖ) (k : ℕ)
    (f : P ⊗ Q ≅ freeIso Rᵐᵒᵖ k) :
    projectiveTrackSource R P k ≅ projectiveTrackTarget R P Q :=
  Functor.isoWhiskerLeft AsSmall.down (Functor.isoWhiskerRight
    (TranslationTelescope.factorizationLowerTrack (freeIso Rᵐᵒᵖ 1) P Q k
      (rightIterationComplementIso R P Q k f)) AsSmall.up)

/-- The common ending map reflects source components after the original stage inclusion. -/
theorem projectiveTrackTarget_infinite_joined_iff (P Q : IsoCategory Rᵐᵒᵖ) (n : ℕ)
    (x y : ClassifyingSpace (ProjectiveStage R)) :
    Joined (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)
        (classifyingSpaceMap (projectiveTrackTarget R P Q) x))
      (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)
        (classifyingSpaceMap (projectiveTrackTarget R P Q) y)) ↔
    Joined (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) x)
      (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) y) := by
  simp only [projectiveTrackTarget, classifyingSpaceMap_comp, TopCat.comp_app]
  rw [projectiveStageLeft_infinite_joined_iff, projectiveStageLeft_infinite_joined_iff,
    projectiveStageRight_infinite_joined_iff]

/-- The actual two finite-stage tracks admit abelian correction on every support
whose component relations are already detected by the original infinite inclusion. -/
theorem projectiveTracks_finite_correction (P Q : IsoCategory Rᵐᵒᵖ) (k n : ℕ)
    (f : P ⊗ Q ≅ freeIso Rᵐᵒᵖ k)
    {A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveStage R))}
    (hA : AbelianMonodromy A) (s : Finset (ClassifyingSpace (ProjectiveStage R)))
    (hs : ∀ x ∈ s, ∀ y ∈ s,
      Joined (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) x)
        (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) y) → Joined x y) :
    ∃ T : A ≅ A, ∀ x ∈ s,
      transport A ((classifyingSpaceNaturalTransformationHomotopy
          (projectiveUpperTrack R P Q k f).hom).evalAt x) ≫
        T.hom.app (FundamentalGroupoid.mk (classifyingSpaceMap (projectiveTrackTarget R P Q) x)) =
      transport A ((classifyingSpaceNaturalTransformationHomotopy
        (projectiveLowerTrack R P Q k f).hom).evalAt x) := by
  apply finite_homotopy_correction_exists _ _ hA s
  intro x hx y hy h
  apply hs x hx y hy
  exact (projectiveTrackTarget_infinite_joined_iff R P Q n x y).mp
    (h.map (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)).hom.continuous)

/-- On each genuine homology class the original two routes differ by one
coefficient automorphism, once its finite support has stabilized in components. -/
theorem projectiveTracks_homology_correction (P Q : IsoCategory Rᵐᵒᵖ) (k n : ℕ)
    (f : P ⊗ Q ≅ freeIso Rᵐᵒᵖ k)
    {A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveStage R))}
    (hA : AbelianMonodromy A) (d : ℕ)
    (x : homology (pullback (classifyingSpaceMap (projectiveTrackSource R P k)).hom A) d) :
    ∃ s : Finset (ClassifyingSpace (ProjectiveStage R)),
      (∀ a ∈ s, ∀ b ∈ s,
        Joined (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) a)
          (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) b) → Joined a b) →
      ∃ T : A ≅ A,
        coefficientHomologyMap
            (pullbackMap (classifyingSpaceMap (projectiveTrackTarget R P Q)).hom T.hom) d
          (coefficientHomologyMap (homotopyPullbackIso
            (classifyingSpaceNaturalTransformationHomotopy
              (projectiveUpperTrack R P Q k f).hom) A).hom d x) =
        coefficientHomologyMap (homotopyPullbackIso
          (classifyingSpaceNaturalTransformationHomotopy
            (projectiveLowerTrack R P Q k f).hom) A).hom d x := by
  obtain ⟨s, hs⟩ := homology_finite_homotopy_correction
    (classifyingSpaceNaturalTransformationHomotopy (projectiveUpperTrack R P Q k f).hom)
    (classifyingSpaceNaturalTransformationHomotopy (projectiveLowerTrack R P Q k f).hom)
    hA d x
  refine ⟨s, fun hc ↦ hs ?_⟩
  intro a ha b hb h
  apply hc a ha b hb
  exact (projectiveTrackTarget_infinite_joined_iff R P Q n a b).mp
    (h.map (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)).hom.continuous)

end Quillen.FiniteProjectiveModule

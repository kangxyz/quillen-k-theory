/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassTelescope

/-!
# Original native ambient Bass telescope under scheme restriction

Every scheme-over-base arrow preserves the actual forward Laurent unit, its
whole original scalar track, the entire Bass seed and the original finite
transitions. Their strict telescope map retains every cylinder height and stage
inclusion. Identity and composition hold for these actual maps. No compactness,
flatness, separation or open-immersion assumption is required.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass Quillen.PolynomialBaseChange
open Quillen.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q S : Over (Spec R)}

/-- The original joint Model restriction keeps the literal identity scheme map. -/
theorem boundedFlatCoefficientSectionModelRestriction_id (P : Over (Spec R)) :
    boundedFlatCoefficientSectionModelRestriction (𝟙 P) =
      𝟙 (boundedFlatCoefficientSectionModelRow P) := by
  apply NatTrans.ext
  funext a
  change (boundedFlatCoefficientSectionModelFunctor R).map (𝟙 (op P, a)) = 𝟙 _
  exact (boundedFlatCoefficientSectionModelFunctor R).map_id (op P, a)

/-- Original scheme composition is preserved by the same contravariant Model maps. -/
theorem boundedFlatCoefficientSectionModelRestriction_comp (f : P ⟶ Q) (g : Q ⟶ S) :
    boundedFlatCoefficientSectionModelRestriction (f ≫ g) =
      boundedFlatCoefficientSectionModelRestriction g ≫
        boundedFlatCoefficientSectionModelRestriction f := by
  have h : rowTransformation (f ≫ g) = rowTransformation g ≫ rowTransformation f := by
    apply NatTrans.ext
    funext a
    apply Prod.ext
    · rfl
    · exact (Category.comp_id (𝟙 a)).symm
  simpa only [boundedFlatCoefficientSectionModelRestriction, Functor.whiskerRight_comp]
    using congrArg (fun α ↦ Functor.whiskerRight α
      (boundedFlatCoefficientSectionModelFunctor R)) h

/-- The native ambient strict prespectrum restriction is the original Model realization. -/
def boundedFlatCoefficientAmbientPrespectrumSchemeRestriction (f : P ⟶ Q) :
    boundedFlatCoefficientAmbientPrespectrumFunctor Q ⟶
      boundedFlatCoefficientAmbientPrespectrumFunctor P :=
  Functor.whiskerRight (boundedFlatCoefficientSectionModelRestriction f) prespectrumFunctor

/-- The actual realized restriction preserves identities. -/
theorem boundedFlatCoefficientAmbientPrespectrumSchemeRestriction_id (P : Over (Spec R)) :
    boundedFlatCoefficientAmbientPrespectrumSchemeRestriction (𝟙 P) =
      𝟙 (boundedFlatCoefficientAmbientPrespectrumFunctor P) := by
  rw [boundedFlatCoefficientAmbientPrespectrumSchemeRestriction,
    boundedFlatCoefficientSectionModelRestriction_id]
  apply NatTrans.ext
  funext a
  change prespectrumFunctor.map (𝟙 _) = 𝟙 _
  exact prespectrumFunctor.map_id _

/-- The same realized restriction preserves original scheme composition. -/
theorem boundedFlatCoefficientAmbientPrespectrumSchemeRestriction_comp
    (f : P ⟶ Q) (g : Q ⟶ S) :
    boundedFlatCoefficientAmbientPrespectrumSchemeRestriction (f ≫ g) =
      boundedFlatCoefficientAmbientPrespectrumSchemeRestriction g ≫
        boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f := by
  rw [boundedFlatCoefficientAmbientPrespectrumSchemeRestriction,
    boundedFlatCoefficientSectionModelRestriction_comp, Functor.whiskerRight_comp]
  rfl

variable (f : P ⟶ Q)

/-- Every original scalar time of the forward Laurent action retains scheme restriction. -/
theorem boundedFlatCoefficientAmbientSchemeRestriction_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatCoefficientAmbientPrespectrumFunctor Q).obj a).space n) :
    ((boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f).app
      ((laurentUnderFunctor R).obj a)).map n
        (((boundedFlatCoefficientAmbientLaurentAction Q).track.homotopy a).level n (t, x)) =
    ((boundedFlatCoefficientAmbientLaurentAction P).track.homotopy a).level n
      (t, ((boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f).app a).map n x) :=
  LaurentSeed.ModelAction.track_square (boundedFlatCoefficientAmbientLaurentAction Q)
    (boundedFlatCoefficientAmbientLaurentAction P)
    (boundedFlatCoefficientSectionModelRestriction f)
    (fun a ↦ boundedFlatCoefficientSectionLaurentUnitIso_restriction f a) a n t x

/-- Original scheme restriction preserves the whole native ambient Bass seed. -/
theorem boundedFlatCoefficientAmbientBassSeed_schemeRestriction :
    boundedFlatCoefficientAmbientBassSeed Q ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f) =
    boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f ≫
      boundedFlatCoefficientAmbientBassSeed P :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientAmbientLaurentAction Q).track
    (boundedFlatCoefficientAmbientLaurentAction P).track
    (boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f)
    (boundedFlatCoefficientAmbientSchemeRestriction_laurent_apply f)

/-- The unchanged finite transformations preserve every actual iterated seed transition. -/
theorem boundedFlatCoefficientAmbientBassSchemeRestriction_transition (i : ℕ) :
    (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f) ≫
      boundedFlatCoefficientAmbientBassTransition P i =
    boundedFlatCoefficientAmbientBassTransition Q i ≫
      (strictDiagramIterate (laurentUnderSquareFunctor R) (i + 1)).map
        (boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientAmbientBassSeed Q) (boundedFlatCoefficientAmbientBassSeed P)
    (boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f)
    (boundedFlatCoefficientAmbientBassSeed_schemeRestriction f) i).symm

/-- The original quotient telescope map of those same strict native finite restrictions. -/
def boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction :
    boundedFlatCoefficientAmbientBassTelescopeFunctor Q ⟶
      boundedFlatCoefficientAmbientBassTelescopeFunctor P :=
  Telescope.diagramMap (boundedFlatCoefficientAmbientBassDiagram Q)
    (boundedFlatCoefficientAmbientBassDiagram P) (boundedFlatCoefficientAmbientBassTransition Q)
    (boundedFlatCoefficientAmbientBassTransition P)
    (fun i ↦ (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
      (boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f))
    (boundedFlatCoefficientAmbientBassSchemeRestriction_transition f)

/-- Every stage and cylinder height keeps its original finite strict scheme map. -/
theorem boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction_cylinder
    (a : Under R) (k i : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientAmbientBassDiagram Q i).obj a).space k) :
    ((boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction f).app a).map k
        (Telescope.cylinder (fun j ↦ (boundedFlatCoefficientAmbientBassDiagram Q j).obj a)
          (fun j ↦ (boundedFlatCoefficientAmbientBassTransition Q j).app a) k i (s, x)) =
    Telescope.cylinder (fun j ↦ (boundedFlatCoefficientAmbientBassDiagram P j).obj a)
      (fun j ↦ (boundedFlatCoefficientAmbientBassTransition P j).app a) k i
      (s, (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f)).app a).map k x) :=
  Telescope.diagramMap_cylinder _ _ _ _ _ _ a k i s x

/-- Every unchanged original finite-stage inclusion retains its full restriction face. -/
theorem boundedFlatCoefficientAmbientBassTelescopeInclusion_schemeRestriction (i : ℕ) :
    boundedFlatCoefficientAmbientBassTelescopeInclusion Q i ≫
      boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction f =
    (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (boundedFlatCoefficientAmbientPrespectrumSchemeRestriction f) ≫
      boundedFlatCoefficientAmbientBassTelescopeInclusion P i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The actual native ambient telescope restriction preserves the identity scheme arrow. -/
theorem boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction_id (P : Over (Spec R)) :
    boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction (𝟙 P) =
      𝟙 (boundedFlatCoefficientAmbientBassTelescopeFunctor P) := by
  apply NatTrans.ext
  funext a
  apply Telescope.hom_ext
  intro k i s x
  change ((boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction (𝟙 P)).app a).map k
      (Telescope.cylinder _ _ k i (s, x)) = Telescope.cylinder _ _ k i (s, x)
  rw [boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction_cylinder]
  dsimp only [boundedFlatCoefficientAmbientBassDiagram] at x ⊢
  rw [boundedFlatCoefficientAmbientPrespectrumSchemeRestriction_id,
    (strictDiagramIterate (laurentUnderSquareFunctor R) i).map_id]
  rfl

/-- Original scheme composition is preserved on every original telescope cylinder. -/
theorem boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction_comp
    {P Q S : Over (Spec R)} (f : P ⟶ Q) (g : Q ⟶ S) :
    boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction (f ≫ g) =
      boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction g ≫
        boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction f := by
  apply NatTrans.ext
  funext a
  apply Telescope.hom_ext
  intro k i s x
  change ((boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction (f ≫ g)).app a).map k
      (Telescope.cylinder _ _ k i (s, x)) =
    ((boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction f).app a).map k
      (((boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction g).app a).map k
        (Telescope.cylinder _ _ k i (s, x)))
  rw [boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction_cylinder,
    boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction_cylinder,
    boundedFlatCoefficientAmbientBassTelescopeSchemeRestriction_cylinder]
  dsimp only [boundedFlatCoefficientAmbientBassDiagram] at x ⊢
  rw [boundedFlatCoefficientAmbientPrespectrumSchemeRestriction_comp,
    (strictDiagramIterate (laurentUnderSquareFunctor R) i).map_comp]
  rfl

end Quillen.PerfectComplexes

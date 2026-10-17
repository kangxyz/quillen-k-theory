/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportedUnits


public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSectionUnits
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenGrading
public import Quillen.KTheory.Bass.StrictLaurentSeedContraction

/-!
# Original auxiliary-supported coefficient Laurent actions and Bass seeds

Forward native coefficient units lift through the actual supported section
inclusions. Their original coefficient and restriction equations prove the
supported C_Z/F_Z/G_Z action tracks and seeds with the same square, joint zero,
source-leg cylinder and scalar/null concatenation. Equal endpoint grades make
the actual graded zero endomorphism weak and construct the complete graded
seed contraction. Only the G_Z coefficient diagram requires compact P and Q.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.KTheory.Bass Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso boundedFlatCoefficientSectionLaurentUnitIso

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original ambient forward Laurent unit, with its proved coefficient naturality. -/
def boundedFlatCoefficientSupportedOpenLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientSupportedOpenModelFunctor f T) where
  unit a := boundedFlatCoefficientSupportedAmbientLaurentUnitIso Q T a
  naturality g := boundedFlatCoefficientSupportedAmbientLaurentUnitIso_coefficient Q T g

/-- The original restricted forward Laurent unit on the actual native fine open row. -/
def boundedFlatCoefficientSupportedFullOpenLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientSupportedFullOpenModelFunctor f T) where
  unit a := boundedFlatCoefficientSupportedFullOpenLaurentUnitIso f T a
  naturality g := boundedFlatCoefficientSupportedFullOpenLaurentUnitIso_coefficient f T g

/-- The entire original ambient Laurent action track on the unchanged coefficient Model map. -/
def boundedFlatCoefficientSupportedOpenLaurentHomotopy (a : Under R) :=
  (boundedFlatCoefficientSupportedOpenLaurentAction f T).track.homotopy a

/-- The entire original restricted Laurent action track on the actual fine open Model map. -/
def boundedFlatCoefficientSupportedFullOpenLaurentHomotopy (a : Under R) :=
  (boundedFlatCoefficientSupportedFullOpenLaurentAction f T).track.homotopy a

/-- All four original ambient native corners with their original positive and inverse charts. -/
def boundedFlatCoefficientSupportedOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T) a

/-- All four original fine open corners with the same coefficient charts. -/
def boundedFlatCoefficientSupportedFullOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) a

/-- The actual mapping cone of the original ambient square comparison. -/
def boundedFlatCoefficientSupportedOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T) a

/-- The actual mapping cone of the original fine open square comparison. -/
def boundedFlatCoefficientSupportedFullOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) a

/-- The original ambient source-leg cylinder; it is not a localization-null substitution. -/
def boundedFlatCoefficientSupportedOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T) a

/-- The original fine open source-leg cylinder on its unchanged native square. -/
def boundedFlatCoefficientSupportedFullOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) a

/-- The original ambient pointwise seed retains the prescribed scalar/null concatenation. -/
def boundedFlatCoefficientSupportedOpenBassSeedMap (a : Under R) :=
  (boundedFlatCoefficientSupportedOpenLaurentAction f T).track.seedMap a

/-- The original fine open pointwise seed retains that same prescribed concatenation. -/
def boundedFlatCoefficientSupportedFullOpenBassSeedMap (a : Under R) :=
  (boundedFlatCoefficientSupportedFullOpenLaurentAction f T).track.seedMap a

/-- The constructed coefficient-natural original ambient Bass seed. -/
def boundedFlatCoefficientSupportedOpenBassSeed :
    boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T) :=
  (boundedFlatCoefficientSupportedOpenLaurentAction f T).track.seed

/-- The constructed coefficient-natural original fine open Bass seed. -/
def boundedFlatCoefficientSupportedFullOpenBassSeed :
    boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T) :=
  (boundedFlatCoefficientSupportedFullOpenLaurentAction f T).track.seed

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The same actual open unit acts on the original graded Model; only weakness changes. -/
def boundedFlatCoefficientSupportedGradedOpenLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientSupportedGradedOpenModelFunctor f T) where
  unit a := boundedFlatCoefficientSupportedFullOpenLaurentUnitIso f T a
  naturality g := boundedFlatCoefficientSupportedFullOpenLaurentUnitIso_coefficient f T g

/-- The unchanged forward Laurent unit realized in the original graded coefficient diagram. -/
def boundedFlatCoefficientSupportedGradedOpenLaurentHomotopy (a : Under R) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).track.homotopy a

/-- The original graded native four-corner square. -/
def boundedFlatCoefficientSupportedGradedOpenBassSquare (a : Under R) :=
  LaurentSeed.square (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) a

/-- The actual mapping cone of the original graded comparison map. -/
def boundedFlatCoefficientSupportedGradedOpenBassCone (a : Under R) :=
  LaurentSeed.cone (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) a

/-- The original graded source-leg cylinder, with every time parameter unchanged. -/
def boundedFlatCoefficientSupportedGradedOpenBassNullHomotopy (a : Under R) :=
  LaurentSeed.sourceNull (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) a

/-- The graded pointwise seed uses that original source-leg null and forward scalar action. -/
def boundedFlatCoefficientSupportedGradedOpenBassSeedMap (a : Under R) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).track.seedMap a

/-- The constructed coefficient-natural original graded Bass seed. -/
def boundedFlatCoefficientSupportedGradedOpenBassSeed :
    boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).track.seed

/-- The actual chosen-zero endomorphism has equal original quotient grades. -/
theorem boundedFlatCoefficientSupportedGradedLaurentZero_weak (a : Under R)
    (S : (boundedFlatCoefficientSupportedGradedOpenModelFunctor f T).obj a) :
    ((boundedFlatCoefficientSupportedGradedOpenModelFunctor f T).obj
      ((laurentUnderFunctor R).obj a)).waldhausen.weq
      ((modelZeroEndotransformation ((boundedFlatCoefficientSupportedGradedOpenModelFunctor f T).map
        ((laurentUnderCoefficient R).app a))).app S) := rfl

/-- The whole original Laurent-action contraction has its same scalar and point endpoints. -/
def boundedFlatCoefficientSupportedGradedLaurentContraction (a : Under R) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).contraction
    (boundedFlatCoefficientSupportedGradedLaurentZero_weak f T) a

/-- The same chosen contraction preserves both independent times under every coefficient map. -/
theorem boundedFlatCoefficientSupportedGradedLaurentContraction_naturality
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (r t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).map
      ((laurentUnderFunctor R).map g)).map n
        ((boundedFlatCoefficientSupportedGradedLaurentContraction f T a).level n (r, (t, x))) =
      (boundedFlatCoefficientSupportedGradedLaurentContraction f T b).level n
        (r, (t, ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).map g).map n
          x)) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).contraction_naturality
    (boundedFlatCoefficientSupportedGradedLaurentZero_weak f T) g n r t x

/-- The original graded seed is null through its prescribed original source-leg conjugation. -/
def boundedFlatCoefficientSupportedGradedOpenBassSeedNull (a : Under R) :
    LoopPrespectrum.Homotopy (boundedFlatCoefficientSupportedGradedOpenBassSeedMap f T a)
      (zeroHom ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a)
        (parameterLooping (boundedFlatCoefficientSupportedGradedOpenBassCone f T a))) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).seedNullHomotopy
    (boundedFlatCoefficientSupportedGradedLaurentZero_weak f T) a

/-- The whole original graded seed null is coefficient-natural, with its actual Bass target. -/
def boundedFlatCoefficientSupportedGradedOpenBassSeedDiagramNull :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedGradedOpenBassSeed f T)
      (𝟙 ((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T))) :=
  (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).seedDiagramNull
    (boundedFlatCoefficientSupportedGradedLaurentZero_weak f T)

/-- The endpoint cast retains the same original graded seed-null time and loop value. -/
theorem boundedFlatCoefficientSupportedGradedOpenBassSeedDiagramNull_level (a : Under R)
    (n : ℕ) (r : unitInterval)
    (x : ((boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedFlatCoefficientSupportedGradedOpenBassSeedDiagramNull f T).homotopy a).level n (r, x) =
      (boundedFlatCoefficientSupportedGradedOpenBassSeedNull f T a).level n (r, x) := rfl

end Quillen.PerfectComplexes

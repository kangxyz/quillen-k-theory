/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.TensorByLine

/-!
# Exactness of the actual right line tensor

The original sheafified tensor symmetry transports finite limits, colimits and homology
preservation for a finite locally free coefficient.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
instance rightLineModule_preservesFiniteLimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteLimits (moduleTensorByLineRight L) :=
  preservesFiniteLimits_of_natIso (moduleTensorByLineSymmetry L)

instance rightLineModule_preservesFiniteColimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteColimits (moduleTensorByLineRight L) :=
  preservesFiniteColimits_of_natIso (moduleTensorByLineSymmetry L)

instance rightLineModule_preservesHomology {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : (moduleTensorByLineRight L).PreservesHomology :=
  ((CategoryTheory.Functor.exact_tfae (moduleTensorByLineRight L)).out 1 3).mp
    (fun (S : ShortComplex X.Modules) (hs : S.ShortExact) =>
      hs.map_of_exact (moduleTensorByLineRight L))


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
end
end

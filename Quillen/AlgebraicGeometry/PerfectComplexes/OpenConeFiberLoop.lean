/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.OpenCone


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenSupport
public import Quillen.Waldhausen.Fibration.CanonicalFiberObjectLoop
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# The actual supported cone in the original localization fiber

A perfect morphism which becomes a quasi-isomorphism on the original open has its literal
mapping cone in the original relative-acyclic category. Its canonical fiber loop keeps both the
fine object coordinate and the specified reversed zero-to-acyclic path coordinate. Comparison
with an original Laurent automorphism class remains a separate boundary calculation.
-/
@[expose] public section

open Quillen.Waldhausen


open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.Waldhausen.Fibration
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  {K L : Perfect X} (f : K ⟶ L) (hf : (perfectOpenWeakWaldhausen j).weq f)

/-- The actual original relative-acyclic object, with unchanged mapping-cone complex. -/
def perfectOpenMappingConeAcyclic : AcyclicCategory (perfectOpenNested j) :=
  (perfectSupportedToAcyclic j).obj
    ⟨CochainComplex.mappingCone f.hom, perfectOpenWeak_mappingCone_supported j f hf⟩

/-- The literal cone object enters the genuine canonical homotopy fiber through its object loop.
-/
def perfectOpenMappingConeFiberLoop :=
  canonicalFiberObjectLoop (perfectOpenNested j) (perfectOpenMappingConeAcyclic j f hf)

/-- Projection retains exactly the original fine mapping-cone object loop. -/
theorem perfectOpenMappingConeFiberLoop_projection (t : unitInterval) :
    (perfectOpenMappingConeFiberLoop j f hf t).val.1 =
      (perfectWaldhausen X).kZeroObjectLoop
        ⟨CochainComplex.mappingCone f.hom,
          locallyPerfect_mappingCone K.property L.property f.hom⟩ t :=
  canonicalFiberObjectLoop_projection _ _ t

/-- The independent fiber-path parameter retains the original reversed zero track. -/
theorem perfectOpenMappingConeFiberLoop_path (t s : unitInterval) :
    (perfectOpenMappingConeFiberLoop j f hf t).val.2 s =
      acyclicNullhomotopy (perfectOpenNested j)
        (s, (acyclicStructure (perfectOpenNested j)).kZeroObjectLoop
          (perfectOpenMappingConeAcyclic j f hf) t) := rfl

end Quillen.PerfectComplexes

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiber
public import Quillen.Waldhausen.Fibration.CanonicalFiberObjectTransport

/-!
# Original fiber-loop transport from the scalar cofiber to its supported cone

The specified cofiber-cone isomorphism, including its explicit cone sign, now transports the
actual canonical fiber loops. This is the full three-parameter transport needed in a boundary
calculation, before any identification with a Laurent-unit boundary.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.Fibration
open scoped Topology
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (K : Perfect X)

/-- The actual cofiber-cone isomorphism gives the specified original canonical fiber-loop track. -/
def perfectOpenScalarCofiberFiberTrack :
    (canonicalFiberObjectLoop (perfectOpenNested j)
      (perfectOpenScalarCofiberAcyclic j r q hq K)).Homotopy
        (canonicalFiberObjectLoop (perfectOpenNested j) (perfectOpenScalarCone j r q hq K)) :=
  canonicalFiberObjectWeakTrack (perfectOpenNested j)
    (perfectOpenScalarCofiberAcyclicIso j r q hq K).hom
    ((acyclicStructure (perfectOpenNested j)).weq_iso _ inferInstance)

/-- The whole original signed isomorphism cylinder remains visible before fiber projection. -/
theorem perfectOpenScalarCofiberFiberTrack_apply (a t : unitInterval) :
    perfectOpenScalarCofiberFiberTrack j r q hq K (a, t) =
      canonicalFiberMap (perfectOpenNested j)
        ((acyclicStructure (perfectOpenNested j)).weakObjectLoopTrack
          (perfectOpenScalarCofiberAcyclicIso j r q hq K).hom
          ((acyclicStructure (perfectOpenNested j)).weq_iso _ inferInstance) (a, t)) := rfl

/-- Comparison, object-loop and reversed fiber-path times are all retained independently. -/
theorem perfectOpenScalarCofiberFiberTrack_path (a t s : unitInterval) :
    (perfectOpenScalarCofiberFiberTrack j r q hq K (a, t)).val.2 s =
      acyclicNullhomotopy (perfectOpenNested j)
        (s, (acyclicStructure (perfectOpenNested j)).weakObjectLoopTrack
          (perfectOpenScalarCofiberAcyclicIso j r q hq K).hom
          ((acyclicStructure (perfectOpenNested j)).weq_iso _ inferInstance) (a, t)) := rfl

end Quillen.PerfectComplexes

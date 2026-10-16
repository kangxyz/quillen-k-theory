/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberPrism
public import Quillen.Waldhausen.Fibration.CofiberObjectChangeWeak

/-!
# The original fine scalar-cofiber triangle and its localization image

The actual fine quotient triangle gives a specified track from the source-plus-cofiber object
loop to the original middle object loop. Its image under the unchanged localization map is
exactly the cofiber-prism face already used in the boundary calculation, with both parameters
retained. No scalar invertibility on the original scheme is required.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen.Fibration
open scoped Topology
universe u
namespace Quillen.PerfectComplexes

/-- The original scalar factor has its genuine quotient square in the fine structure. -/
theorem perfectScalarCofiber_fine_isPushout (X : Scheme.{u}) (r : Γ(X, ⊤)) (K : Perfect X) :
    IsPushout (perfectScalarInclusion X r K) (0 : K ⟶ (perfectWaldhausen X).zero)
      ((ExtensionCategory.quotient (perfectWaldhausen X)).app (perfectScalarExtension X r K))
      (0 : (perfectWaldhausen X).zero ⟶
        (ExtensionCategory.cofiber (perfectWaldhausen X)).obj (perfectScalarExtension X r K)) := by
  have h := ExtensionCategory.cofiber_isPushout (perfectWaldhausen X)
    (perfectScalarExtension X r K)
  convert h using 1 <;> first
    | rfl
    | exact (perfectWaldhausen X).isZero.eq_of_tgt _ _
    | exact (perfectWaldhausen X).isZero.eq_of_src _ _

/-- The specified fine triangle track uses the original categorical cofiber and middle objects. -/
def perfectScalarCofiberObjectTrack (X : Scheme.{u}) (r : Γ(X, ⊤)) (K : Perfect X) :
    Path.Homotopy (((perfectWaldhausen X).kZeroObjectLoop K).trans
      ((perfectWaldhausen X).kZeroObjectLoop
        ((ExtensionCategory.cofiber (perfectWaldhausen X)).obj (perfectScalarExtension X r K))))
      ((perfectWaldhausen X).kZeroObjectLoop
        ((ExtensionCategory.middle (perfectWaldhausen X)).obj (perfectScalarExtension X r K))) :=
  (perfectWaldhausen X).cofiberObjectLoopTrack (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (perfectWaldhausen X)).app (perfectScalarExtension X r K))
    (ExtensionCategory.inclusion_cof (perfectWaldhausen X) (perfectScalarExtension X r K))
    (perfectScalarCofiber_fine_isPushout X r K)

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (K : Perfect X)

/-- The original localization map preserves the entire actual fine cofiber track. -/
theorem perfectScalarCofiberObjectTrack_changeWeak (a t : unitInterval) :
    changeWeakMap (perfectOpenNested j) (perfectScalarCofiberObjectTrack X r K (a, t)) =
      (perfectOpenNested j).coarse.cofiberObjectLoopTrack (perfectScalarInclusion X r K)
        ((ExtensionCategory.quotient (perfectWaldhausen X)).app (perfectScalarExtension X r K))
        (perfectScalarInclusion_openCof j r K) (perfectScalarCofiber_isPushout j r K) (a, t) :=
  cofiberObjectLoopTrack_changeWeak (perfectOpenNested j) (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (perfectWaldhausen X)).app (perfectScalarExtension X r K))
    (ExtensionCategory.inclusion_cof (perfectWaldhausen X) (perfectScalarExtension X r K))
    (perfectScalarInclusion_openCof j r K) (perfectScalarCofiber_fine_isPushout X r K)
    (perfectScalarCofiber_isPushout j r K) a t

/-- The exact nerve-one face of the original scalar prism is this same fine-track image. -/
theorem perfectScalarCofiberObjectTrack_prism_face (a t : unitInterval) :
    changeWeakMap (perfectOpenNested j) (perfectScalarCofiberObjectTrack X r K (a, t)) =
      perfectOpenScalarCofiberCompositionCube j r q hq K (a, 1, t) := by
  rw [perfectScalarCofiberObjectTrack_changeWeak]
  unfold perfectOpenScalarCofiberCompositionCube
  rw [Structure.cofiberPrismCompositionCube_nerve_one]

end Quillen.PerfectComplexes

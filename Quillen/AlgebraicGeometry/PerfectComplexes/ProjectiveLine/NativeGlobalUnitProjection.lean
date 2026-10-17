/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeGlobalBoundaryCoordinates
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitFlatComposition
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitInclusionOperation

/-!
# Original unit-boundary coordinates on the literal native Laurent projection

The actual negative-chart projection equation identifies the composed unit operation with
the literal Laurent projection operation. The actual bounded-flat inclusion then transports
these original global all-degree coordinates, without changing either unit or connecting map.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Waldhausen.Additivity.KCommGroup
private theorem unitOperation_map_eq {U Y : Scheme.{u}} (f g : U ⟶ Y)
    [Flat f] [Flat g] (hfg : f = g) (q : (Γ(U, ⊤))ˣ) (n : ℕ) :
    originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy f q) n =
      originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy g q) n := by
  subst g
  rfl

variable (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj] (n : ℕ)

/-- The original forward operation on the actual Laurent projection has the same Phi pair. -/
theorem projectiveConnecting_comp_forwardProjection_allDegrees :
    (projectiveConnecting X n).comp
      (originalKSelfTrackOperation (perfectWaldhausen X.obj)
        (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
        (perfectFlatUnitHomotopy (Relative.laurentProjection.app X).hom (laurentGlobalUnit X)) n) =
      (nativeTwoSummandKMap X n).comp
        (invMonoidHom.prod (MonoidHom.id (PerfectK X.obj n))) := by
  have hp := perfectFlatUnitHomotopy_originalKOperation_precomp
    (Relative.minus.app X).hom (Relative.polynomialProjection.app X).hom (laurentGlobalUnit X) n
  have hm := congrArg (fun f => f.hom) (Relative.minus_projection X)
  change (Relative.minus.app X).hom ≫ (Relative.polynomialProjection.app X).hom =
    (Relative.laurentProjection.app X).hom at hm
  have hp' := hp.trans (unitOperation_map_eq _ _ hm (laurentGlobalUnit X) n)
  exact (congrArg (fun f : PerfectK X.obj n →*
      PerfectK (Relative.laurentFunctor.obj X).obj (n + 1) =>
        (projectiveConnecting X n).comp f) hp'.symm).trans
    (projectiveConnecting_comp_selfTrack_polynomial_allDegrees X n)

/-- The original inverse operation on the actual Laurent projection has the inverse Phi pair. -/
theorem projectiveConnecting_comp_inverseProjection_allDegrees :
    (projectiveConnecting X n).comp
      (originalKSelfTrackOperation (perfectWaldhausen X.obj)
        (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
        (perfectFlatUnitHomotopy (Relative.laurentProjection.app X).hom (laurentGlobalUnit X)⁻¹) n)
          =
      (nativeTwoSummandKMap X n).comp
        ((MonoidHom.id (PerfectK X.obj n)).prod invMonoidHom) := by
  have hp := perfectFlatUnitHomotopy_originalKOperation_precomp
    (Relative.minus.app X).hom (Relative.polynomialProjection.app X).hom (laurentGlobalUnit X)⁻¹ n
  have hm := congrArg (fun f => f.hom) (Relative.minus_projection X)
  change (Relative.minus.app X).hom ≫ (Relative.polynomialProjection.app X).hom =
    (Relative.laurentProjection.app X).hom at hm
  have hp' := hp.trans (unitOperation_map_eq _ _ hm (laurentGlobalUnit X)⁻¹ n)
  exact (congrArg (fun f : PerfectK X.obj n →*
      PerfectK (Relative.laurentFunctor.obj X).obj (n + 1) =>
        (projectiveConnecting X n).comp f) hp'.symm).trans
    (projectiveConnecting_comp_inverseSelfTrack_polynomial_allDegrees X n)

/-- Actual model inclusion transports the literal forward projection and the unchanged boundary.
-/
theorem projectiveConnecting_comp_boundedFlatForwardProjection_allDegrees :
    (projectiveConnecting X n).comp
      ((boundedFlatPerfectToPerfectKMap (Relative.laurentFunctor.obj X).obj (n + 1)).comp
        (originalKSelfTrackOperation (boundedFlatPerfectWaldhausen X.obj)
          (boundedFlatPerfectWaldhausen (Relative.laurentFunctor.obj X).obj)
          (boundedFlatPerfectUnitHomotopy (Relative.laurentProjection.app X).hom
            (laurentGlobalUnit X)) n)) =
      ((nativeTwoSummandKMap X n).comp
        (invMonoidHom.prod (MonoidHom.id (PerfectK X.obj n)))).comp
          (boundedFlatPerfectToPerfectKMap X.obj n) := by
  rw [boundedFlatPerfectToPerfectKMap_comp_unitOperation, ← MonoidHom.comp_assoc,
    projectiveConnecting_comp_forwardProjection_allDegrees]

/-- Actual model inclusion also retains the literal inverse-unit operation and boundary. -/
theorem projectiveConnecting_comp_boundedFlatInverseProjection_allDegrees :
    (projectiveConnecting X n).comp
      ((boundedFlatPerfectToPerfectKMap (Relative.laurentFunctor.obj X).obj (n + 1)).comp
        (originalKSelfTrackOperation (boundedFlatPerfectWaldhausen X.obj)
          (boundedFlatPerfectWaldhausen (Relative.laurentFunctor.obj X).obj)
          (boundedFlatPerfectUnitHomotopy (Relative.laurentProjection.app X).hom
            (laurentGlobalUnit X)⁻¹) n)) =
      ((nativeTwoSummandKMap X n).comp
        ((MonoidHom.id (PerfectK X.obj n)).prod invMonoidHom)).comp
          (boundedFlatPerfectToPerfectKMap X.obj n) := by
  rw [boundedFlatPerfectToPerfectKMap_comp_unitOperation, ← MonoidHom.comp_assoc,
    projectiveConnecting_comp_inverseProjection_allDegrees]

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass

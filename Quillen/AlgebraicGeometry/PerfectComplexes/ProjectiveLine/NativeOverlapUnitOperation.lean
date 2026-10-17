/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitOpenComposition
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitKOperation
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeOverlapUnitBoundary

/-!
# Original Laurent overlap transport of unit operations in all connective degrees

The whole open/flat composition comparison transports the actual negative Laurent pullback
unit operation through the original inverse overlap equivalence. The inverse-unit consequence
retains the same geometric map and all original input classes, including degree zero.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass

/-- Equality induction transports only the original flat map, with its unit fixed. -/
private theorem unitSelfTrack_map_eq {X Y : Scheme.{u}} (f g : X ⟶ Y)
    [Flat f] [Flat g] (hfg : f = g) (q : (Γ(X, ⊤))ˣ) (n : ℕ) :
    originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q) n =
      originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy g q) n := by
  subst g
  rfl

/-- The whole original overlap comparison preserves the actual forward unit operation. -/
theorem laurentOverlap_comp_unitSelfTrack (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}) (n
  : ℕ) :
    (laurentOverlapEquiv X (n + 1)).symm.toMonoidHom.comp
        (originalKSelfTrackOperation (perfectWaldhausen
          (Relative.polynomialFunctor.obj X).obj)
          (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
          (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit X)) n) =
      originalKSelfTrackOperation (perfectWaldhausen
        (Relative.polynomialFunctor.obj X).obj)
        (perfectWaldhausen (overlapOpen X).toScheme)
        (perfectFlatUnitHomotopy (overlapOpen X).ι (overlapLaurentUnit X)) n := by
  change (perfectKRestrict (overlapOpenIso X).inv (n + 1)).comp _ = _
  have h := perfectFlatUnitHomotopy_originalKOperation_restrict_comp
    (Relative.minus.app X).hom (overlapOpenIso X).inv (laurentGlobalUnit X) n
  have he := unitSelfTrack_map_eq
    ((overlapOpenIso X).inv ≫ (Relative.minus.app X).hom) (overlapOpen X).ι
    (overlapOpenIso_inv_minus X) (overlapLaurentUnit X) n
  exact h.trans he

/-- Every original polynomial-chart class retains the literal forward Laurent unit. -/
theorem laurentOverlap_unitSelfTrack (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}) (n : ℕ)
    (a : PerfectK (Relative.polynomialFunctor.obj X).obj n) :
    (laurentOverlapEquiv X (n + 1)).symm
        (originalKSelfTrackOperation (perfectWaldhausen
          (Relative.polynomialFunctor.obj X).obj)
          (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
          (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit
            X)) n a) =
      originalKSelfTrackOperation (perfectWaldhausen
        (Relative.polynomialFunctor.obj X).obj)
        (perfectWaldhausen (overlapOpen X).toScheme)
        (perfectFlatUnitHomotopy (overlapOpen X).ι (overlapLaurentUnit X)) n a :=
  DFunLike.congr_fun (laurentOverlap_comp_unitSelfTrack X n) a

/-- Only inversion of the original unit reverses the output; overlap transport is forward. -/
theorem laurentOverlap_unitSelfTrack_inverse (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u})
  (n : ℕ)
    (a : PerfectK (Relative.polynomialFunctor.obj X).obj n) :
    (laurentOverlapEquiv X (n + 1)).symm
        (originalKSelfTrackOperation (perfectWaldhausen
          (Relative.polynomialFunctor.obj X).obj)
          (perfectWaldhausen (Relative.laurentFunctor.obj X).obj)
          (perfectFlatUnitHomotopy (Relative.minus.app X).hom (laurentGlobalUnit
            X)) n a) =
      (originalKSelfTrackOperation (perfectWaldhausen
        (Relative.polynomialFunctor.obj X).obj)
        (perfectWaldhausen (overlapOpen X).toScheme)
        (perfectFlatUnitHomotopy (overlapOpen X).ι (overlapLaurentUnit X)⁻¹) n a)⁻¹ := by
  rw [laurentOverlap_unitSelfTrack,
    perfectFlatUnitHomotopy_originalKOperation_inv, inv_inv]

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenPseudofunctor
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenScalarUnit

/-!
# The original full-open restriction components and coefficient squares

Each component is actual bounded-flat pullback along the specified open inclusion. The
coefficient comparison is the preexisting open-pair pullback isomorphism, including its actual
scheme-square equality. Original restriction of the scalar is identified with the same target
unit, and original bounded-flat pullback retains that unit as well. These formulas do not
assert a full-open cofinality equivalence or identify independently chosen zeros.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The source pullback pseudofunctor uses the same original affine coefficient diagram. -/
def boundedFlatAffineFixedBasePseudofunctor : Pseudofunctor (LocallyDiscrete (Under R)) Cat :=
  (ambientFunctor R).toPseudofunctor.comp boundedFlatPerfectPseudofunctor

/-- The actual coefficient square in the original open-pair category. -/
def boundedFlatAffineFullOpenPairSquare {a b : Under R} (f : a ⟶ b) :
    (⟨Arrow.mk (inclusion j b), (show IsOpenImmersion (inclusion j b) from inferInstance)⟩ :
      Quillen.Scheme.OpenPairs) ⟶
      ⟨Arrow.mk (inclusion j a), (show IsOpenImmersion (inclusion j a) from inferInstance)⟩ :=
  ObjectProperty.homMk (Arrow.homMk (openMap j f) (Spec.map f.right)
    (openMap_inclusion j f))

/-- Every comparison component is the original pullback to the actual full open. -/
def boundedFlatAffineFullOpenRestriction (a : Under R) :
    BoundedFlatPerfect (Spec a.right) ⥤ BoundedFlatPerfect (openSpace j a) :=
  boundedFlatPerfectPullback (inclusion j a)

/-- The original relative-open weak class makes precisely this component Waldhausen-exact. -/
theorem boundedFlatAffineFullOpenRestriction_exact (a : Under R) :
    Waldhausen.IsExact (boundedFlatPerfectOpenWaldhausen (inclusion j a)).cof
      (boundedFlatPerfectOpenWaldhausen (inclusion j a)).weq
      (boundedFlatPerfectWaldhausen (openSpace j a)).cof
      (boundedFlatPerfectWaldhausen (openSpace j a)).weq
      (boundedFlatAffineFullOpenRestriction j a) :=
  boundedFlatPerfectOpenRestriction_exact (inclusion j a)

/-- The specified original open-pair isomorphism supplies the coefficient square. -/
def boundedFlatAffineFullOpenRestrictionIso {a b : Under R} (f : a ⟶ b) :
    boundedFlatPerfectPullback (Spec.map f.right) ⋙
        boundedFlatAffineFullOpenRestriction j b ≅
      boundedFlatAffineFullOpenRestriction j a ⋙
        boundedFlatPerfectPullback (openMap j f) :=
  boundedFlatPerfectOpenPairIso (boundedFlatAffineFullOpenPairSquare j f)

/-- The square retains both original composition comparisons and the original lift equation. -/
theorem boundedFlatAffineFullOpenRestrictionIso_original {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenRestrictionIso j f =
      (boundedFlatPerfectPullbackCompIso (inclusion j b) (Spec.map f.right)).symm ≪≫
        eqToIso (congrArg boundedFlatPerfectPullback (openMap_inclusion j f).symm) ≪≫
          boundedFlatPerfectPullbackCompIso (openMap j f) (inclusion j a) := rfl

/-- This original component agrees with ordinary perfect restriction via the existing iso. -/
def boundedFlatAffineFullOpenOriginalRestrictionIso (a : Under R) :
    boundedFlatPerfectInclusion (Spec a.right) ⋙ perfectRestrict (inclusion j a) ≅
      boundedFlatAffineFullOpenRestriction j a ⋙
        boundedFlatPerfectInclusion (openSpace j a) :=
  boundedFlatPerfectOriginalRestrictionIso (inclusion j a)

/-- The target unit is the image under the specified original inclusion, with no replacement. -/
def boundedFlatAffineFullOpenUnit (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    (Γ(openSpace j a, ⊤))ˣ :=
  Units.map (inclusion j a).appTop.hom.toMonoidHom r

/-- Actual complex restriction sends the original scalar to that exact target unit. -/
theorem boundedFlatAffineFullOpenRestriction_scalar (a : Under R)
    (r : (Γ(Spec a.right, ⊤))ˣ) (K : Complex (Spec a.right)) :
    (restrict (inclusion j a)).map ((complexGlobalScalar (Spec a.right) (↑r)).app K) =
      (complexGlobalUnitIso (openSpace j a) (boundedFlatAffineFullOpenUnit j a r)).hom.app
        ((restrict (inclusion j a)).obj K) :=
  restrict_map_complexGlobalScalar_unit (inclusion j a) (↑r)
    (boundedFlatAffineFullOpenUnit j a r) rfl K

omit [IsOpenImmersion j] in
/-- Original bounded-flat pullback acts by the identical target unit on each original object. -/
theorem boundedFlatAffineFullOpenRestriction_unit (a : Under R)
    (r : (Γ(Spec a.right, ⊤))ˣ) (K : BoundedFlatPerfect (Spec a.right)) :
    (boundedFlatAffineFullOpenRestriction j a).map
        ((boundedFlatPerfectGlobalUnitIso (Spec a.right) r).hom.app K) =
      (boundedFlatPerfectGlobalUnitIso (openSpace j a)
        (boundedFlatAffineFullOpenUnit j a r)).hom.app
          ((boundedFlatAffineFullOpenRestriction j a).obj K) :=
  boundedFlatPerfectPullback_map_globalUnit (inclusion j a) r K

end Quillen.PerfectComplexes

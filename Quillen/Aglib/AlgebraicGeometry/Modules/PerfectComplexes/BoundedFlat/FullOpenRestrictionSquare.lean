/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.FullOpenPseudofunctor
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Restriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.GlobalUnitPullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.ScalarRestriction

/-!
# Original full-open coefficient restriction squares

Actual bounded-flat pullback along each specified open inclusion retains its existing pair
comparison, scalar restriction and pulled-back unit.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The source pullback pseudofunctor uses the same original affine coefficient diagram. -/
def boundedFlatAffineFixedBasePseudofunctor : Pseudofunctor (LocallyDiscrete (Under R)) Cat :=
  (ambientFunctor R).toPseudofunctor.comp boundedFlatPerfectPseudofunctor

/-- The actual coefficient square in the original open-pair category. -/
def boundedFlatAffineFullOpenPairSquare {a b : Under R} (f : a ⟶ b) :
    (⟨Arrow.mk (inclusion j b), (show IsOpenImmersion (inclusion j b) from inferInstance)⟩ :
      AlgebraicGeometry.Scheme.OpenPairs) ⟶
      ⟨Arrow.mk (inclusion j a), (show IsOpenImmersion (inclusion j a) from inferInstance)⟩ :=
  ObjectProperty.homMk (Arrow.homMk (openMap j f) (Spec.map f.right)
    (openMap_inclusion j f))

/-- Every comparison component is the original pullback to the actual full open. -/
def boundedFlatAffineFullOpenRestriction (a : Under R) :
    BoundedFlatPerfect (Spec a.right) ⥤ BoundedFlatPerfect (openSpace j a) :=
  boundedFlatPerfectPullback (inclusion j a)

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
    (r : (Γ(Spec a.right, ⊤))ˣ) (K : CochainComplex (Spec a.right).Modules ℤ) :
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

end

end

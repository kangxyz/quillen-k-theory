/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionFullOpenCoefficient
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionFullOpenUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionFullOpenZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionSpectrumNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentUnit

/-! Original open-pair, coefficient, zero and Laurent consumers for the full-open comparison. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.Tests.FullOpenCoefficient
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- At the identity algebra the actual projection, rather than object equality, recovers j. -/
theorem identityOpenProjection :
    (identityProjectionIso j).hom ≫ j = inclusion j (Under.mk (𝟙 R)) :=
  openFunctor_identityProjection j

/-- A composite original coefficient arrow retains all three original pseudo constraints. -/
theorem originalOpenPairComposite {a b c : Under R} (f : a ⟶ b) (g : b ⟶ c) :
    Cat.Hom.toNatIso
        ((boundedFlatAffineFullOpenRestrictionStrongTrans j).naturality (f ≫ g).toLoc) =
      (boundedFlatPerfectPullbackCompIso (inclusion j c) (Spec.map (f ≫ g).right)).symm ≪≫
        eqToIso (congrArg boundedFlatPerfectPullback (openMap_inclusion j (f ≫ g)).symm) ≪≫
          boundedFlatPerfectPullbackCompIso (openMap j (f ≫ g)) (inclusion j a) :=
  (boundedFlatAffineFullOpenRestrictionStrongTrans_naturality j (f ≫ g)).trans
    (boundedFlatAffineFullOpenRestrictionIso_original j (f ≫ g))

/-- The actual open-pair forward component cancels its original inverse on every complex. -/
theorem originalOpenPairInverse {a b : Under R} (f : a ⟶ b)
    (K : BoundedFlatPerfect (Spec a.right)) :
    (boundedFlatAffineFullOpenRestrictionIso j f).hom.app K ≫
        (boundedFlatAffineFullOpenRestrictionIso j f).inv.app K = 𝟙 _ :=
  Iso.hom_inv_id_app (boundedFlatAffineFullOpenRestrictionIso j f) K

/-- The coefficient comparison uses the accepted original section-evaluation transition iso. -/
theorem originalSectionCoefficientIso {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineSectionFullOpenCoefficientIso j f =
      (Functor.associator (boundedFlatAffineSectionsMap f.right)
        (boundedFlatAffineOriginalEvaluation b.right)
        (boundedFlatAffineFullOpenRestriction j b)).symm ≪≫
      Functor.isoWhiskerRight (boundedFlatAffineSectionCoefficientIso f.right)
        (boundedFlatAffineFullOpenRestriction j b) ≪≫
      Functor.associator (boundedFlatAffineOriginalEvaluation a.right)
        (boundedFlatPerfectPullback (Spec.map f.right))
        (boundedFlatAffineFullOpenRestriction j b) ≪≫
      Functor.isoWhiskerLeft (boundedFlatAffineOriginalEvaluation a.right)
        (boundedFlatAffineFullOpenRestrictionIso j f) ≪≫
      (Functor.associator (boundedFlatAffineOriginalEvaluation a.right)
        (boundedFlatAffineFullOpenRestriction j a)
        (boundedFlatPerfectPullback (openMap j f))).symm := rfl

/-- The actual image of the original section zero, at any coefficient, is a genuine zero. -/
theorem originalSectionImageZero (a : Under R) :
    IsZero ((boundedFlatAffineSectionFullOpenRestriction j a).obj
      (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).zero) :=
  isZero_boundedFlatAffineSectionFullOpenImageZero j a

/-- The source-zero map is retained under the original restriction functor. -/
theorem originalSectionZeroArrow (a : Under R) (s : BoundedFlatAffineSections a.right) :
    (boundedFlatAffineSectionFullOpenRestriction j a).map
      ((boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).isZero.to_ s) =
      (isZero_boundedFlatAffineSectionFullOpenImageZero j a).to_
        ((boundedFlatAffineSectionFullOpenRestriction j a).obj s) :=
  (isZero_boundedFlatAffineSectionFullOpenImageZero j a).eq_of_src _ _

omit [IsOpenImmersion j] in
/-- The original Laurent coordinate acts by its exact inclusion-restricted global unit. -/
theorem originalLaurentRestriction (a : Under R)
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ a.right)
    (s : BoundedFlatAffineSections a.right) :
    (boundedFlatAffineSectionFullOpenRestriction j a).map
      ((boundedFlatAffineSectionUnitIso a.right
        (Units.map (Spec.map h).appTop.hom.toMonoidHom
          (Quillen.Scheme.PolynomialLaurent.laurentGlobalUnit R))).hom.app s) =
      (boundedFlatPerfectGlobalUnitIso (openSpace j a)
        (Units.map (inclusion j a).appTop.hom.toMonoidHom
          (Units.map (Spec.map h).appTop.hom.toMonoidHom
            (Quillen.Scheme.PolynomialLaurent.laurentGlobalUnit R)))).hom.app
        ((boundedFlatAffineSectionFullOpenRestriction j a).obj s) :=
  boundedFlatAffineSectionFullOpenRestriction_unit j a _ s

end Quillen.Tests.FullOpenCoefficient

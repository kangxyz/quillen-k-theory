/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientConeFunctor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeCoefficientObjectBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarConeFunctor

/-!
# Natural negative restriction of the native coefficient cone

The existing global signed-cone comparison is natural in the unchanged perfect coefficient.
It identifies the actual supported restriction K-map with the polynomial scalar cone K-map
in every connective degree.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex Quillen.Waldhausen
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass

private theorem restrict_cone_map_naturality {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {K₁ L₁ K₂ L₂ : CochainComplex X.Modules ℤ}
    (p : K₁ ⟶ L₁) (q : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : p ≫ b = a ≫ q) :
    (Modules.Complex.restrict j).map (CochainComplex.mappingCone.map p q a b h) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso q
          (Scheme.Modules.restrictFunctor j)).hom =
      (CochainComplex.mappingCone.mapHomologicalComplexIso p
        (Scheme.Modules.restrictFunctor j)).hom ≫
          CochainComplex.mappingCone.map ((Modules.Complex.restrict j).map p)
            ((Modules.Complex.restrict j).map q)
            ((Modules.Complex.restrict j).map a) ((Modules.Complex.restrict j).map b)
            (by simpa only [Functor.map_comp] using
              congrArg ((Modules.Complex.restrict j).map) h) := by
  ext n : 1
  have hf : (CochainComplex.mappingCone.map p q a b h).f n ≫
      (CochainComplex.mappingCone.fst q).1.v n (n + 1) rfl =
    (CochainComplex.mappingCone.fst p).1.v n (n + 1) rfl ≫ a.f (n + 1) := by
    simp [CochainComplex.mappingCone.ext_from_iff _ (n + 1) n rfl,
      CochainComplex.mappingCone.map, Category.assoc]
  have hs : (CochainComplex.mappingCone.map p q a b h).f n ≫
      (CochainComplex.mappingCone.snd q).v n n (add_zero n) =
    (CochainComplex.mappingCone.snd p).v n n (add_zero n) ≫ b.f n := by
    simp [CochainComplex.mappingCone.ext_from_iff _ (n + 1) n rfl,
      CochainComplex.mappingCone.map, Category.assoc]
  simp only [CochainComplex.mappingCone.map] at hf hs
  simp [Modules.Complex.restrict, CochainComplex.mappingCone.mapHomologicalComplexIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso',
    CochainComplex.mappingCone.map, Category.assoc, -Functor.map_comp,
    ← Functor.map_comp_assoc, hf, hs]

private theorem coefficient_cone_minus_naturality (X :
  AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u})
    {K L : Perfect (nativeLineFunctor.obj X).obj} (g : K ⟶ L) :
    (Modules.Complex.restrict (nativeMinus.app X).hom).map ((coefficientConeFunctor X).map g).hom ≫
        (coefficientConeMinusIso X L).hom =
      (coefficientConeMinusIso X K).hom ≫
        ((perfectSupportedScalarConeFunctor (overlapOpen X).ι
          (nativePolynomialCoordinate X) (overlapLaurentUnit X)⁻¹
          (polynomialCoordinate_overlap X)).map
            ((perfectRestrict (nativeMinus.app X).hom).map g)).hom := by
  rw [coefficientConeFunctor_map_hom]
  dsimp only [coefficientConeMinusIso, Iso.trans_hom]
  rw [← Category.assoc, restrict_cone_map_naturality]
  simp only [Category.assoc]
  apply (cancel_epi (CochainComplex.mappingCone.mapHomologicalComplexIso
    (coefficientPerfectCoordinate X K).hom
    (Scheme.Modules.restrictFunctor (nativeMinus.app X).hom)).hom).mpr
  have hscalar :
      ((perfectSupportedScalarConeFunctor (overlapOpen X).ι
        (nativePolynomialCoordinate X) (overlapLaurentUnit X)⁻¹
        (polynomialCoordinate_overlap X)).map
          ((perfectRestrict (nativeMinus.app X).hom).map g)).hom =
      CochainComplex.mappingCone.map
        ((complexGlobalScalar _ (nativePolynomialCoordinate X)).app
          ((Modules.Complex.restrict (nativeMinus.app X).hom).obj K.obj))
        ((complexGlobalScalar _ (nativePolynomialCoordinate X)).app
          ((Modules.Complex.restrict (nativeMinus.app X).hom).obj L.obj))
        ((Modules.Complex.restrict (nativeMinus.app X).hom).map g.hom)
        ((Modules.Complex.restrict (nativeMinus.app X).hom).map g.hom)
        ((complexGlobalScalar _ (nativePolynomialCoordinate X)).naturality
          ((Modules.Complex.restrict (nativeMinus.app X).hom).map g.hom)).symm := rfl
  rw [hscalar]
  dsimp only [CochainComplex.mappingCone.isoOfIso, Modules.Complex.restrict,
    nativeNegativeTwist, perfectTensorByLine, ObjectProperty.lift, ObjectProperty.ι_obj]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 1
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj,
    perfectTensorByLine, ObjectProperty.lift, ObjectProperty.ι_obj, Modules.Complex.restrict,
    Iso.app_hom] using
    (tensorByLineComplexChartIso (nativeMinus.app X).hom (nativeTautologicalLine X)
      (nativeTautologicalMinusIso X)).hom.naturality g.hom

/-- The already-fixed supported cone component is natural on every perfect coefficient map. -/
theorem coefficientSupportedConeMinusIso_naturality (X : QuasiCompactSchemes.{u})
    {K L : Perfect (nativeLineFunctor.obj X).obj} (g : K ⟶ L) :
    (perfectSupportedRestrict (nativeMinus.app X).hom (positiveOpen X)).map
        ((coefficientConeFunctor X).map g) ≫
          (coefficientSupportedConeMinusIso X L).hom =
      (coefficientSupportedConeMinusIso X K).hom ≫
        (perfectSupportedScalarConeFunctor (overlapOpen X).ι
          (nativePolynomialCoordinate X) (overlapLaurentUnit X)⁻¹
          (polynomialCoordinate_overlap X)).map
            ((perfectRestrict (nativeMinus.app X).hom).map g) := by
  apply ObjectProperty.hom_ext
  exact coefficient_cone_minus_naturality X g

/-- The original objectwise cone comparison forms the actual negative-chart natural isomorphism. -/
def coefficientConeMinusNatIso (X : QuasiCompactSchemes.{u}) :
    coefficientConeFunctor X ⋙
        perfectSupportedRestrict (nativeMinus.app X).hom (positiveOpen X) ≅
      perfectRestrict (nativeMinus.app X).hom ⋙
        perfectSupportedScalarConeFunctor (overlapOpen X).ι
          (nativePolynomialCoordinate X) (overlapLaurentUnit X)⁻¹
          (polynomialCoordinate_overlap X) :=
  NatIso.ofComponents (coefficientSupportedConeMinusIso X)
    (fun g => coefficientSupportedConeMinusIso_naturality X g)

/-- Actual supported negative restriction is the scalar cone in every connective K-degree. -/
theorem coefficientConeKMap_restrict (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (perfectSupportedKRestrict (nativeMinus.app X).hom (positiveOpen X) n).comp
        (coefficientConeKMap X n) =
      (perfectSupportedScalarConeKMap (overlapOpen X).ι
        (nativePolynomialCoordinate X) (overlapLaurentUnit X)⁻¹
        (polynomialCoordinate_overlap X) n).comp
          (perfectKRestrict (nativeMinus.app X).hom n) := by
  unfold perfectSupportedKRestrict coefficientConeKMap
    perfectSupportedScalarConeKMap perfectKRestrict
  rw [KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (coefficientConeMinusNatIso X) n

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass

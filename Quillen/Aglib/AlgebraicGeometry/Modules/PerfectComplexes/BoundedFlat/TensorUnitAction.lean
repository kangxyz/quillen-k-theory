/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.TensorToUnit
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.GlobalUnit

/-!
# Actual tensor-unit automorphisms on bounded-flat perfect complexes

The first tensor factor is the original structure module, placed in degree zero by degreewise
left tensor. Its original global-unit automorphism acts through the coefficient tensor functor.
The genuine left unitor intertwines this action with the existing forward scalar automorphism
on every complex and on the original bounded-flat full subcategory. This is a categorical
comparison of actual tensor maps, not an identification of a K-theory cup product.

Intended upstream owner:
`Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitAction`.
The hypotheses are an arbitrary scheme and a global unit. The current consumer is the original
restricted tensor-unit iterated-S comparison in Quillen.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry SheafOfModulesOfCommRing
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Complex
universe u
namespace Quillen.PerfectComplexes

/-- The original sheaf tensor left unitor, applied in every complex degree. -/
def complexTensorUnitIso (X : Scheme.{u}) :
    tensorLeft (SheafOfModules.unit X.ringCatSheaf) ≅
      𝟭 (CochainComplex X.Modules ℤ) :=
  NatIso.mapHomologicalComplex (tensorLeftUnitIso X.sheaf) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso X.Modules (.up ℤ)

/-- The actual coefficient tensor of the original structure-module automorphism. -/
def complexTensorUnitAutomorphism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorLeft (SheafOfModules.unit X.ringCatSheaf) ≅
      tensorLeft (SheafOfModules.unit X.ringCatSheaf) :=
  let e : moduleTensorLeftFunctor X (SheafOfModules.unit X.ringCatSheaf) ≅
      moduleTensorLeftFunctor X (SheafOfModules.unit X.ringCatSheaf) :=
    (tensorFunctor X.sheaf).mapIso (unitMulIso X r)
  NatIso.mapHomologicalComplex e (.up ℤ)

/-- The complex unitor retains the genuine sheaf unitor in each degree. -/
theorem complexTensorUnitIso_hom_f (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((complexTensorUnitIso X).hom.app K).f n =
      (tensorLeftUnitIso X.sheaf).hom.app (K.X n) := by
  change (tensorLeftUnitIso X.sheaf).hom.app (K.X n) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The automorphism retains the original coefficient tensor map in each degree. -/
theorem complexTensorUnitAutomorphism_hom_f (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((complexTensorUnitAutomorphism X r).hom.app K).f n =
      (moduleTensorCoefficientMap X (unitMul X r)).app (K.X n) := rfl

/-- The original tensor-unit automorphism is the forward scalar under the actual unitor. -/
theorem complexTensorUnitAutomorphism_unitor (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (complexTensorUnitAutomorphism X r).hom ≫ (complexTensorUnitIso X).hom =
      (complexTensorUnitIso X).hom ≫ (complexGlobalUnitIso X r).hom := by
  apply NatTrans.ext
  funext K
  ext n : 1
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    complexTensorUnitAutomorphism_hom_f, complexTensorUnitIso_hom_f,
    complexGlobalUnitIso_original_terms]
  exact NatTrans.congr_app (moduleLineCoordinate_unitMul X (r : Γ(X, ⊤))) (K.X n)

/-- Genuine degreewise tensor by the structure module on the bounded-flat perfect subcategory. -/
def boundedFlatPerfectTensorUnit (X : Scheme.{u}) :
    BoundedFlatPerfect X ⥤ BoundedFlatPerfect X :=
  (boundedFlatPerfect X).lift
    ((boundedFlatPerfect X).ι ⋙ tensorLeft (SheafOfModules.unit X.ringCatSheaf))
    (fun K => boundedFlatPerfect_of_iso ((complexTensorUnitIso X).app K.obj).symm K.property)

/-- The same left unitor in the original bounded-flat full subcategory. -/
def boundedFlatPerfectTensorUnitIso (X : Scheme.{u}) :
    boundedFlatPerfectTensorUnit X ≅ 𝟭 (BoundedFlatPerfect X) :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfect X).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfect X).ι (complexTensorUnitIso X))

/-- Tensor the original structure-module unit automorphism on every bounded-flat input. -/
def boundedFlatPerfectTensorUnitAutomorphism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    boundedFlatPerfectTensorUnit X ≅ boundedFlatPerfectTensorUnit X :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfect X).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfect X).ι (complexTensorUnitAutomorphism X r))

/-- Inclusion retains the original complex tensor map, without a replacement identity functor. -/
theorem boundedFlatPerfectTensorUnitAutomorphism_hom_original
    (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) (K : BoundedFlatPerfect X) :
    (boundedFlatPerfect X).ι.map
        ((boundedFlatPerfectTensorUnitAutomorphism X r).hom.app K) =
      (complexTensorUnitAutomorphism X r).hom.app K.obj := by
  simp only [boundedFlatPerfectTensorUnitAutomorphism,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.ι_obj]

/-- The actual full-subcategory unitor keeps its original ambient component. -/
theorem boundedFlatPerfectTensorUnitIso_hom_original (X : Scheme.{u})
    (K : BoundedFlatPerfect X) :
    (boundedFlatPerfect X).ι.map ((boundedFlatPerfectTensorUnitIso X).hom.app K) =
      (complexTensorUnitIso X).hom.app K.obj := by
  simp only [boundedFlatPerfectTensorUnitIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    ObjectProperty.ι_obj]

/-- The entire natural transformation, hence every morphism, keeps the original forward scalar. -/
theorem boundedFlatPerfectTensorUnitAutomorphism_unitor
    (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectTensorUnitAutomorphism X r).hom ≫
        (boundedFlatPerfectTensorUnitIso X).hom =
      (boundedFlatPerfectTensorUnitIso X).hom ≫ (boundedFlatPerfectGlobalUnitIso X r).hom := by
  apply NatTrans.ext
  funext K
  apply (boundedFlatPerfect X).ι.map_injective
  simp only [NatTrans.comp_app, Functor.map_comp,
    boundedFlatPerfectTensorUnitAutomorphism_hom_original,
    boundedFlatPerfectTensorUnitIso_hom_original, boundedFlatPerfectGlobalUnitIso_hom_original]
  exact NatTrans.congr_app (complexTensorUnitAutomorphism_unitor X r) K.obj

end Quillen.PerfectComplexes

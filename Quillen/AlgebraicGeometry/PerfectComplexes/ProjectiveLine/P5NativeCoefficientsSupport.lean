/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.AcyclicSupport
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeCoefficientsOne
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Closure
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian.OpenImmersion

/-! # Actual inverse-image open support for the native coefficients

The open is literally the inverse image under the native projection. Ordinary
open base change is the original cartesian mate; the restricted bounded-below
flasque model computes its derived direct image through the installed unit.
Acyclicity follows from the existing flasque-kernel pushforward theorem. The
right tensor and original total augmentation preserve acyclicity on that same
open before the signed shift.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients


open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen





noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeCoefficients
open FlasqueCoefficients

/-- The standard derived-category instance for sheaves of modules on `Y`. -/
local instance nativeSupportStandardDerived (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _

/-- Open restriction preserves the full original flasque-perfect object predicate. -/
lemma restrict_objects {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (K : FlasqueBoundedBelow.Obj P) :
    FlasqueBoundedBelow.objects U ((restrict j).obj K.obj) := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  refine ⟨⟨locallyPerfect_restrict j K.property.1.1, a,
    restrict_isStrictlyGE j K.obj a⟩, fun n => ?_⟩
  let : TopCat.Presheaf.IsFlasque (K.obj.X n).presheaf := K.property.2 n
  exact restrictModule_isFlasque j (K.obj.X n)

/-- The actual original restriction, lifted only by the proved object predicate. -/
def restrictedModel {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (K : FlasqueBoundedBelow.Obj P) : FlasqueBoundedBelow.Obj U :=
  ⟨(restrict j).obj K.obj, restrict_objects j K⟩

/-- The actual restricted flasque complex computes direct image via the installed unit. -/
def restrictedPushforwardDerivedIso {U P V : Scheme.{u}} (j : U ⟶ P)
    [IsOpenImmersion j] (f : U ⟶ V) (K : FlasqueBoundedBelow.Obj P) :
    DerivedCategory.Plus.Q.obj
      ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj
        ((toPlus U).obj (restrictedModel j K))) ≅
      (derivedPushforwardPlus f).obj
        (DerivedCategory.Plus.Q.obj ((toPlus U).obj (restrictedModel j K))) :=
  (derivedPushforwardIso f).app (restrictedModel j K)

/-- The preceding comparison is the installed unit on the literal restricted model. -/
lemma restrictedPushforwardDerivedIso_hom_unit {U P V : Scheme.{u}} (j : U ⟶ P)
    [IsOpenImmersion j] (f : U ⟶ V) (K : FlasqueBoundedBelow.Obj P) :
    (restrictedPushforwardDerivedIso j f K).hom =
      (derivedPushforwardPlusUnit f).app ((toPlus U).obj (restrictedModel j K)) := rfl

/-- Ordinary pushforward of an actual bounded-below acyclic flasque model is acyclic. -/
lemma ordinaryPushforward_acyclic_of_flasque {U V : Scheme.{u}} (f : U ⟶ V)
    (K : FlasqueBoundedBelow.Obj U) (hK : K.obj.Acyclic) :
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic := by
  obtain ⟨a, ha⟩ := K.property.1.2
  let := ha
  intro n
  have h := pushforward_exactAt_succ_of_acyclic_flasque f K.obj a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE K.obj a i hi)
    hK K.property.2 (n - 1)
  simpa only [sub_add_cancel] using h

/-- The actual original total augmentation preserves acyclicity on that same open. -/
lemma rightTensorTotal_restrictAcyclic (X : QuasiCompactSchemes.{u})
    {U : Scheme.{u}} (j : U ⟶ (nativeLineFunctor.obj X).obj) [IsOpenImmersion j]
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj)
    (hK : ((restrict j).obj K.obj).Acyclic) :
    ((restrict j).obj ((rightTensorTotal X).obj K).obj).Acyclic := by
  have ht := AlgebraicGeometry.Scheme.Modules.Complex.tensorRight_restrict_acyclic j
    (nativeTautologicalLine X) K.obj hK
  exact (restrictAcyclic_iff_of_quasiIso j ((tensorTotalUnit X).app K).hom).mp ht

/-- G0 carries actual inverse-image support to support away from the original base open. -/
lemma G0_preservesSupport (X : QuasiCompactSchemes.{u}) (Z : X.obj.Opens)
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj)
    (hK : ((restrict ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).obj K.obj).Acyclic) :
    ((restrict Z.ι).obj ((G0 X).obj K).obj).Acyclic := by
  let p := (nativeProjection.app X).hom
  have hp := ordinaryPushforward_acyclic_of_flasque (p ∣_ Z)
    (restrictedModel (p ⁻¹ᵁ Z).ι K) hK
  intro n
  exact (hp n).of_iso ((ordinaryOpenRestrictionIso p Z).app K.obj).symm

/-- G1 uses right tensor, the original total augmentation and the signed shift on support. -/
lemma G1_preservesSupport (X : QuasiCompactSchemes.{u}) (Z : X.obj.Opens)
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj)
    (hK : ((restrict ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).obj K.obj).Acyclic) :
    ((restrict Z.ι).obj ((G1 X).obj K).obj).Acyclic := by
  have hT := rightTensorTotal_restrictAcyclic X
    ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι K hK
  exact restrictAcyclic_shift Z.ι
    (G0_preservesSupport X Z ((rightTensorTotal X).obj K) hT) 1

/-- The actual coefficient pair preserves support on the literal inverse-image open. -/
lemma G_preservesSupport (X : QuasiCompactSchemes.{u}) (Z : X.obj.Opens)
    (K : FlasqueBoundedBelow.Obj (nativeLineFunctor.obj X).obj)
    (hK : ((restrict ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι).obj K.obj).Acyclic) :
    ((restrict Z.ι).obj ((G X).obj K).1.obj).Acyclic ∧
      ((restrict Z.ι).obj ((G X).obj K).2.obj).Acyclic :=
  ⟨G0_preservesSupport X Z K hK, G1_preservesSupport X Z K hK⟩

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeCoefficients

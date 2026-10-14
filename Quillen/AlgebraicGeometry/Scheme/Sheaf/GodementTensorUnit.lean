/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GodementTotalQuasiIso
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.TensorDerivedPushforward

/-! # Original Godement augmentation inside an exact tensor

The maps below tensor the original augmentation and then apply the original total.
Their source and target are the actual lower-bounded complexes.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.SchemeSheaf

/-- A typed postcomposition of an actual unit, before any total is specialized. -/
def originalUnitPostcompose {A : Type*} [Category A] (G F : A ⥤ A)
    (η : 𝟭 A ⟶ G) : F ⟶ G ⋙ F where
  app K := F.map (η.app K)
  naturality {K C} f := by
    change F.map f ≫ F.map (η.app C) = F.map (η.app K) ≫ F.map (G.map f)
    simp only [← Functor.map_comp]
    exact congrArg F.map (η.naturality f)

/-- The original exact termwise functor preserves the actual quasi-isomorphisms. -/
lemma exactPlus_map_quasiIso {X : Scheme.{u}} (F : X.Modules ⥤ X.Modules)
    [F.Additive] [F.PreservesHomology] {K C : CochainComplex.Plus X.Modules}
    (f : K ⟶ C) [QuasiIso f.hom] :
    QuasiIso (F.mapCochainComplexPlus.map f).hom :=
  inferInstanceAs (QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom))

/-- Tensor the original total augmentation in the varying complex. -/
def godementTensorUnit (X : Scheme.{u}) (E : X.Modules) :
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus ⟶
      godementTotalPlus X ⋙ (moduleTensorLeftFunctor X E).mapCochainComplexPlus :=
  originalUnitPostcompose (godementTotalPlus X)
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus (godementTotalPlusUnit X)

/-- Its component is the original left tensor of the original augmentation. -/
lemma godementTensorUnit_app (X : Scheme.{u}) (E : X.Modules)
    (C : CochainComplex.Plus X.Modules) :
    (godementTensorUnit X E).app C =
      (moduleTensorLeftFunctor X E).mapCochainComplexPlus.map
          ((godementTotalPlusUnit X).app C) := rfl

/-- Finite local freeness gives the weak arrow through the proved exact tensor. -/
theorem godementTensorUnit_quasiIso {X : Scheme.{u}} (E : X.Modules)
    [IsFiniteLocallyFree X E] (C : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementTensorUnit X E).app C).hom := by
  rw [godementTensorUnit_app]
  exact exactPlus_map_quasiIso _ ((godementTotalPlusUnit X).app C)

/-- Apply the original outer total to the original tensor of the augmentation. -/
def godementTensorTotalUnit (X : Scheme.{u}) (E : X.Modules) :
    (moduleTensorLeftFunctor X E).mapCochainComplexPlus ⋙ godementTotalPlus X ⟶
      (godementTotalPlus X ⋙ (moduleTensorLeftFunctor X E).mapCochainComplexPlus) ⋙
        godementTotalPlus X :=
  Functor.whiskerRight (godementTensorUnit X E) (godementTotalPlus X)

/-- The component retains the original augmentation before the outer total. -/
lemma godementTensorTotalUnit_app (X : Scheme.{u}) (E : X.Modules)
    (C : CochainComplex.Plus X.Modules) :
    (godementTensorTotalUnit X E).app C =
      (godementTotalPlus X).map
        ((moduleTensorLeftFunctor X E).mapCochainComplexPlus.map
          ((godementTotalPlusUnit X).app C)) := rfl

/-- Both actual totals are connected by a natural quasi-isomorphism. -/
theorem godementTensorTotalUnit_quasiIso {X : Scheme.{u}} (E : X.Modules)
    [IsFiniteLocallyFree X E] (C : CochainComplex.Plus X.Modules) :
    QuasiIso ((godementTensorTotalUnit X E).app C).hom := by
  let := godementTensorUnit_quasiIso E C
  exact godementTotalPlus_map_quasiIso ((godementTensorUnit X E).app C)

/-- The actual total retains each specified lower bound. -/
theorem godementTotalPlus_sameLowerBound {X : Scheme.{u}}
    (C : CochainComplex.Plus X.Modules) (a : ℤ) [C.obj.IsStrictlyGE a] :
    ((godementTotalPlus X).obj C).obj.IsStrictlyGE a :=
  godementTotal_isStrictlyGE C.obj a
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE C.obj a n hn)

/-- Every degree of the actual total is flasque for every original Plus input. -/
theorem godementTotalPlus_termwiseFlasque {X : Scheme.{u}}
    (C : CochainComplex.Plus X.Modules) (n : ℤ) :
    TopCat.Presheaf.IsFlasque (((godementTotalPlus X).obj C).obj.X n).presheaf := by
  obtain ⟨a, ha⟩ := C.property
  let := ha
  exact godementTotal_isFlasque C.obj a
    (fun i hi => CochainComplex.isZero_of_isStrictlyGE C.obj a i hi) n

end Quillen.SchemeSheaf

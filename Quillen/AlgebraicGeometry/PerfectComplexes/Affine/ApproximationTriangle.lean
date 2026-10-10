/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedComparison

/-!
# Original-target triangles for module approximations on an affine open

An actual module chain map gives a distinguished triangle after associated
sheaves and restriction. An actual derived isomorphism transports only its
middle vertex to the original all-sheaf target. The cone comparison commutes
with the literal cone inclusion. A second explicit transport identifies the
residual vertex with the single on its own homology whenever such an isomorphism
is given. Neither vanishing of the residual arrow nor splitting is assumed.
No compactness or perfection hypothesis is needed for these triangle adapters.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated
universe u
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

variable (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
  {P K : ModuleComplex R} (f : P ⟶ K)

/-- The actual additive cone comparison for associated sheaves followed by open restriction. -/
def openAssociatedConeIso :
    (restrict j).obj ((associatedComplex R).obj (CochainComplex.mappingCone f)) ≅
      CochainComplex.mappingCone ((restrict j).map ((associatedComplex R).map f)) :=
  (restrict j).mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso f (tilde.functor R)) ≪≫
    CochainComplex.mappingCone.mapHomologicalComplexIso ((associatedComplex R).map f)
      (Scheme.Modules.restrictFunctor j)

@[reassoc]
lemma openAssociatedConeIso_inr :
    (restrict j).map ((associatedComplex R).map (CochainComplex.mappingCone.inr f)) ≫
      (openAssociatedConeIso R j f).hom =
        CochainComplex.mappingCone.inr ((restrict j).map ((associatedComplex R).map f)) := by
  dsimp [openAssociatedConeIso]
  rw [← Category.assoc, ← (restrict j).map_comp,
    CochainComplex.mappingCone.map_inr]
  exact CochainComplex.mappingCone.map_inr _ _

@[reassoc]
lemma openAssociatedConeIso_inr_inv :
    CochainComplex.mappingCone.inr ((restrict j).map ((associatedComplex R).map f)) ≫
      (openAssociatedConeIso R j f).inv =
        (restrict j).map ((associatedComplex R).map (CochainComplex.mappingCone.inr f)) := by
  rw [← openAssociatedConeIso_inr R j f, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {E : Complex U}
  (eK : (toDerived U).obj ((restrict j).obj ((associatedComplex R).obj K)) ≅ (toDerived U).obj E)

/-- The actual approximation arrow with its target transported to the original all-sheaf complex. -/
def originalApproximationHom :
    (toDerived U).obj ((restrict j).obj ((associatedComplex R).obj P)) ⟶ (toDerived U).obj E :=
  (toDerived U).map ((restrict j).map ((associatedComplex R).map f)) ≫ eK.hom

/-- The residual arrow retains the original chain cone inclusion and both comparison isomorphisms.
-/
def originalApproximationBoundary :
    (toDerived U).obj E ⟶
      (toDerived U).obj ((restrict j).obj ((associatedComplex R).obj (CochainComplex.mappingCone
        f))) :=
  eK.inv ≫
    (toDerived U).map (CochainComplex.mappingCone.inr ((restrict j).map ((associatedComplex R).map
      f))) ≫
      ((toDerived U).mapIso (openAssociatedConeIso R j f)).inv

@[reassoc]
lemma originalApproximationBoundary_eq :
    originalApproximationBoundary R j f eK =
      eK.inv ≫ (toDerived U).map
        ((restrict j).map ((associatedComplex R).map (CochainComplex.mappingCone.inr f))) := by
  dsimp [originalApproximationBoundary]
  rw [← (toDerived U).map_comp, openAssociatedConeIso_inr_inv]

/-- The original-E approximation triangle, with the literal restricted module cone as third vertex.
-/
def originalApproximationTriangle : Triangle (Derived U) :=
  Triangle.mk (originalApproximationHom R j f eK)
    (originalApproximationBoundary R j f eK)
    (((toDerived U).mapIso (openAssociatedConeIso R j f)).hom ≫
      ((toDerived U).mapTriangle.obj
        (CochainComplex.mappingCone.triangle ((restrict j).map ((associatedComplex R).map
          f)))).mor₃)

/-- No cone or target is replaced abstractly: this isomorphism displays all three comparison maps.
-/
def originalApproximationTriangleIso :
    originalApproximationTriangle R j f eK ≅
      (toDerived U).mapTriangle.obj
        (CochainComplex.mappingCone.triangle ((restrict j).map ((associatedComplex R).map f))) := by
  refine Triangle.isoMk _ _ (Iso.refl _) eK.symm
    ((toDerived U).mapIso (openAssociatedConeIso R j f)) ?_ ?_ ?_
  · dsimp [originalApproximationTriangle, originalApproximationHom]
    simp
  · dsimp [originalApproximationTriangle, originalApproximationBoundary]
    simp
  · dsimp [originalApproximationTriangle]
    simp

lemma originalApproximationTriangle_distinguished :
    originalApproximationTriangle R j f eK ∈ distTriang (Derived U) :=
  isomorphic_distinguished _
    (mappingConeTriangle_distinguished ((restrict j).map ((associatedComplex R).map f))) _
    (originalApproximationTriangleIso R j f eK)

@[simp]
lemma originalApproximationTriangle_mor₁ :
    (originalApproximationTriangle R j f eK).mor₁ = originalApproximationHom R j f eK := rfl

@[simp]
lemma originalApproximationTriangle_mor₂ :
    (originalApproximationTriangle R j f eK).mor₂ = originalApproximationBoundary R j f eK := rfl

variable (n : ℤ)
  (eD : (toDerived U).obj
      ((restrict j).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))) ≅
    (toDerived U).obj ((CochainComplex.singleFunctor U.Modules n).obj
      (((restrict j).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))).homology n)))

/-- Transport the actual residual vertex to the single on its own homology sheaf. -/
def originalApproximationSingleTriangle : Triangle (Derived U) :=
  Triangle.mk (originalApproximationHom R j f eK)
    (originalApproximationBoundary R j f eK ≫ eD.hom)
    (eD.inv ≫ (originalApproximationTriangle R j f eK).mor₃)

/-- The single-homology triangle is explicitly isomorphic to the original cone triangle. -/
def originalApproximationSingleTriangleIso :
    originalApproximationSingleTriangle R j f eK n eD ≅
      originalApproximationTriangle R j f eK := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) eD.symm ?_ ?_ ?_
  · dsimp [originalApproximationSingleTriangle, originalApproximationTriangle]
    simp
  · dsimp [originalApproximationSingleTriangle, originalApproximationTriangle]
    simp
  · dsimp [originalApproximationSingleTriangle]
    simp

lemma originalApproximationSingleTriangle_distinguished :
    originalApproximationSingleTriangle R j f eK n eD ∈ distTriang (Derived U) :=
  isomorphic_distinguished _ (originalApproximationTriangle_distinguished R j f eK) _
    (originalApproximationSingleTriangleIso R j f eK n eD)

@[simp]
lemma originalApproximationSingleTriangle_mor₁ :
    (originalApproximationSingleTriangle R j f eK n eD).mor₁ =
      originalApproximationHom R j f eK := rfl

@[simp]
lemma originalApproximationSingleTriangle_mor₂ :
    (originalApproximationSingleTriangle R j f eK n eD).mor₂ =
      originalApproximationBoundary R j f eK ≫ eD.hom := rfl

lemma originalApproximationSingleTriangle_mor₂_eq_zero_iff :
    (originalApproximationSingleTriangle R j f eK n eD).mor₂ = 0 ↔
      originalApproximationBoundary R j f eK = 0 := by
  rw [originalApproximationSingleTriangle_mor₂, ← cancel_mono eD.hom, zero_comp]

end Quillen.PerfectComplexes.Affine

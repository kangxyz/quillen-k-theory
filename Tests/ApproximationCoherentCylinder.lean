/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.WeakCommaCylinder

/-! # Semantic consumers of the genuine approximation cylinder filling

These use independent source and target universes, retain the original weak
functor, exercise both strict filling faces, and check the actual based
nullhomotopy at the original App2 point coming from the specified source zero.
The final consumer instantiates the cylinder from actual cone-closed complexes.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen
open Quillen.Waldhausen.HasApproximationProperty
universe v u v' u' w z
namespace Quillen.Tests.ApproximationCoherentCylinder

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty] (T : FunctorialFactorization W)
  (Y : WideSubcategory V.weq)

/-- An actual cofibrant successor receives the two strict cylinder triangles. -/
theorem coherent_parallel_filling [HasBinaryCoproducts C]
    {A B : WeakComma hF Y} (f g : A ⟶ B) :
    ∃ (Z : WeakComma hF Y) (b : B ⟶ Z)
      (c : weakCommaCylinder hF T Y A ⟶ Z),
      W.cof b.left.hom ∧
      weakCommaEndpointZero h hF T Y A ≫ c = f ≫ b ∧
      weakCommaEndpointOne h hF T Y A ≫ c = g ≫ b := by
  let s := parallelFilling h hF T Y f g
  exact ⟨s.target, s.fromTarget, s.fromCylinder, s.fromTarget_cof, s.first, s.second⟩

/-- The constructed cylinder is a genuine source cylinder, including both
actual weak endpoint maps and their unchanged strict projection. -/
theorem cylinder_endpoints_weak_cof [HasBinaryCoproducts C] (A : WeakComma hF Y) :
    W.cof (weakCommaEndpointZero h hF T Y A).left.hom ∧
    W.weq (weakCommaEndpointZero h hF T Y A).left.hom ∧
    W.cof (weakCommaEndpointOne h hF T Y A).left.hom ∧
    W.weq (weakCommaEndpointOne h hF T Y A).left.hom ∧
    weakCommaEndpointZero h hF T Y A ≫ weakCommaCylinderProjection hF T Y A = 𝟙 A ∧
    weakCommaEndpointOne h hF T Y A ≫ weakCommaCylinderProjection hF T Y A = 𝟙 A :=
  ⟨T.foldEndpointZero_cof _, (weakCommaEndpointZero h hF T Y A).left.property,
    T.foldEndpointOne_cof _, (weakCommaEndpointOne h hF T Y A).left.property,
    weakCommaEndpointZero_projection h hF T Y A,
    weakCommaEndpointOne_projection h hF T Y A⟩

omit [V.weq.HasTwoOutOfThreeProperty] in
/-- No change of the original functor or its underlying arrow is involved. -/
theorem original_functor_map {A B : WideSubcategory W.weq} (f : A ⟶ B) :
    (hF.weakFunctor.map f).hom = F.map f.hom := rfl

/-- The source-zero App2 vertex stays fixed for the whole genuine nullhomotopy. -/
theorem zero_origin_loop_based {B : WeakComma hF Y}
    (f g : weakCommaPoint h hF Y ⟶ B) (t : unitInterval) :
    parallelLoopNullhomotopy h hF T Y f g (t, 0) =
      classifyingSpacePoint (weakCommaPoint h hF Y) ∧
    parallelLoopNullhomotopy h hF T Y f g (t, 1) =
      classifyingSpacePoint (weakCommaPoint h hF Y) :=
  ⟨parallelLoopNullhomotopy_source h hF T Y f g t,
    parallelLoopNullhomotopy_target h hF T Y f g t⟩

include T in
/-- Strict full/essentially-surjective input supplies App2, not an assumed
contractibility or path-homotopy endpoint. -/
theorem full_essSurj_parallel_paths [F.Full] [F.EssSurj]
    (hreflect : ∀ {X Y : C} (f : X ⟶ Y), V.weq (F.map f) → W.weq f)
    {A B : WeakComma hF Y} (f g : A ⟶ B) :
    (classifyingSpacePath f).Homotopic (classifyingSpacePath g) :=
  parallel_paths_homotopic_of_factorization
    (of_full_essSurj T hF.weak hreflect) hF T Y f g

/-- The natural isomorphism retains the original common-successor formula. -/
theorem groupoid_constant_component [HasBinaryCoproducts C]
    {G : Type z} [Groupoid.{w} G] (H : WeakComma hF Y ⥤ G) (P A : WeakComma hF Y) :
    (groupoidConstantIso h hF T Y H P).hom.app A =
      H.map (weakCommaPairLeft h hF Y A P) ≫
        inv (H.map (weakCommaPairRight h hF Y A P)) := rfl

section Complexes
open CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

include hcone in
/-- The actual cone construction supplies the required source factorization.
No independent joint-cylinder or higher-filling hypothesis is introduced. -/
theorem split_complex_parallel_paths
    (Y : WideSubcategory (complexSubcategory P).weq)
    {X Z : WeakComma (splitComplexSubcategory_to_complexSubcategory_exact P) Y}
    (f g : X ⟶ Z) : (classifyingSpacePath f).Homotopic (classifyingSpacePath g) := by
  let := complexSubcategory_saturated P
  exact parallel_paths_homotopic_of_factorization (splitComparison_approximation P hcone)
    (splitComplexSubcategory_to_complexSubcategory_exact P)
    (splitSubcategoryFunctorialFactorization P hcone) Y f g
end Complexes
end Quillen.Tests.ApproximationCoherentCylinder

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Approximation.ReedyCubes

/-! # Semantic consumers of actual finite Reedy replacement

These test the joint latching cofibration, strict original square factorization,
coherence under maps of arbitrary original squares, all actual vertices in every
finite dimension, original map equality, and retained chosen-zero vertices.
-/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen
open Quillen.Waldhausen.FunctorialFactorization
universe v u u'

namespace QuillenTest.ApproximationReedyReplacement

open Quillen

variable {C : Type u} [Category.{v} C] {W : Structure C}
  (T : FunctorialFactorization W)

/-- The actual original square is factored through a joint-cofibration square,
with both original weak projection components and exact factorization. -/
theorem actual_reedy_factorization (f : Arrow (ExtensionCategory.Obj W)) :
    W.cof (T.reedyInclusion.app f).hom.left ∧
    W.cof (ExtensionCategory.relativeMap W (T.reedyInclusion.app f)) ∧
    W.weq (T.reedyProjection.app f).hom.left ∧
    W.weq (T.reedyProjection.app f).hom.right ∧
    T.reedyInclusion.app f ≫ T.reedyProjection.app f = f.hom :=
  ⟨(T.reedyInclusion_cof f).1, (T.reedyInclusion_cof f).2,
    (T.reedyProjection_weak f).1, (T.reedyProjection_weak f).2,
    T.reedyInclusion_projection f⟩

/-- Arbitrary original squares become genuine Reedy squares without changing
the minimal vertex, and all four comparisons are actual weak equivalences. -/
theorem arbitrary_square_replacement (f : Arrow (Arrow C)) :
    W.cof (T.reedySquareReplacement.obj f).obj.hom.hom.left ∧
    W.cof (ExtensionCategory.relativeMap W (T.reedySquareReplacement.obj f).obj.hom) ∧
    (T.reedySquareReplacement.obj f).obj.left.obj.left = f.left.left ∧
    W.weq (T.reedySquareProjection.app f).left.left ∧
    W.weq (T.reedySquareProjection.app f).left.right ∧
    W.weq (T.reedySquareProjection.app f).right.left ∧
    W.weq (T.reedySquareProjection.app f).right.right :=
  ⟨(T.reedySquareReplacement.obj f).property.1,
    (T.reedySquareReplacement.obj f).property.2,
    T.reedySquareReplacement_initial f,
    T.reedySquareProjection_weak f⟩

/-- The replacement comparison commutes strictly with every original cube
map, not merely with the individual square's internal arrows. -/
theorem arbitrary_square_comparison_natural {f g : Arrow (Arrow C)} (a : f ⟶ g) :
    (reedySquareForget (W := W)).map (T.reedySquareReplacement.map a) ≫
      T.reedySquareProjection.app g = T.reedySquareProjection.app f ≫ a :=
  T.reedySquareProjection.naturality a

section Small
variable {C₀ : Type u} [SmallCategory C₀] {D : Type u'} [SmallCategory D]
  {W₀ : Structure C₀} {V : Structure D} {F : C₀ ⥤ D}
  (T₀ : FunctorialFactorization W₀)
  (h : HasApproximationProperty W₀ V F)
  (hF : IsExact W₀.cof W₀.weq V.cof V.weq F)

/-- All vertices of every finite original cube have actual weak comparisons. -/
theorem finite_cube_all_vertices (n : ℕ) (X : originalCube (C := C₀) n)
    (v : CubeVertex n) :
    W₀.weq ((originalCubeVertex n v).map (T₀.cubeProjection n |>.app X)) :=
  T₀.cubeProjection_vertex_weak n X v

/-- Pointwise weak original cubes remain weak after genuine Reedy replacement. -/
theorem finite_cube_weak_maps [W₀.weq.HasTwoOutOfThreeProperty]
    (n : ℕ) {X Y : originalCube (C := C₀) n} (a : X ⟶ Y)
    (ha : originalCubeWeq W₀ n a) :
    (reedyCube W₀ n).waldhausen.weq ((T₀.cubeReplacement n).map a) :=
  T₀.cubeReplacement_weak n a ha

include h in
/-- Every finite genuine Reedy cube admits relative App2 through the original
iterated F, and that F agrees strictly with original diagram postcomposition. -/
theorem finite_cube_relative_App2 (n : ℕ)
    {X : (reedyCube W₀ n).carrier} {Y : (reedyCube V n).carrier}
    (f : (reedyCubeMap W₀ hF n).functor.obj X ⟶ Y) :
    (∃ (Z : (reedyCube W₀ n).carrier) (i : X ⟶ Z)
      (p : (reedyCubeMap W₀ hF n).functor.obj Z ⟶ Y),
      (reedyCube W₀ n).waldhausen.cof i ∧
      (reedyCube V n).waldhausen.weq p ∧
      (reedyCubeMap W₀ hF n).functor.map i ≫ p = f) ∧
    (reedyCubeMap W₀ hF n).functor ⋙ reedyCubeForget V n =
      reedyCubeForget W₀ n ⋙ originalCubeMap (F := F) n :=
  ⟨(h.reedyCube_approximation hF n).lift f, reedyCubeMap_forget W₀ hF n⟩

/-- Recursion has not replaced the specified source zero with isomorphic choices. -/
theorem finite_cube_original_zero (n : ℕ) (v : CubeVertex n) :
    (originalCubeVertex n v).obj
      ((reedyCubeForget W₀ n).obj (reedyCube W₀ n).waldhausen.zero) = W₀.zero :=
  reedyCube_zero_vertex W₀ n v
end Small

end QuillenTest.ApproximationReedyReplacement

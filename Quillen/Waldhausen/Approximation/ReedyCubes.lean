/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Approximation.ReedyReplacement
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Finite iteration of genuine Reedy-arrow constructions

An n-cube is the literal n-fold arrow category. The Reedy model iterates the
existing cofibration-arrow Waldhausen structure. The given functorial source
factorization, exact original functors, and their App1/App2 properties transfer
by finite recursion, without any new diagram-filling or functorial-App2 premise.
The model is bundled only to express dependent finite iteration in Lean.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u u'

namespace Quillen.Waldhausen

/-- A bundled small Waldhausen category, used for finite dependent recursion. -/
structure ReedyCubeModel where
  /-- The type of objects of the small category on which the Reedy construction is iterated. -/
  carrier : Type u
  [category : SmallCategory carrier]
  /-- The Waldhausen structure on the bundled small category. -/
  waldhausen : Structure carrier

attribute [instance] ReedyCubeModel.category

namespace ReedyCubeModel

/-- One genuine Reedy-arrow step uses the original existing owner. -/
def next (M : ReedyCubeModel.{u}) : ReedyCubeModel.{u} where
  carrier := ExtensionCategory.Obj M.waldhausen
  waldhausen := ExtensionCategory.waldhausenStructure M.waldhausen

/-- Exact comparison data retain the original functor and both structures. -/
structure ExactMap (M : ReedyCubeModel.{u}) (N : ReedyCubeModel.{u'}) where
  /-- The functor between the two bundled categories, with preservation of the displayed
  cofibration and weak-equivalence classes recorded by `exact`. -/
  functor : M.carrier ⥤ N.carrier
  exact : IsExact M.waldhausen.cof M.waldhausen.weq N.waldhausen.cof N.waldhausen.weq functor

/-- Iteration uses precisely original postcomposition on actual Reedy arrows. -/
def ExactMap.next {M : ReedyCubeModel.{u}} {N : ReedyCubeModel.{u'}}
    (F : ExactMap M N) : ExactMap M.next N.next where
  functor := ExtensionCategory.postcompose M.waldhausen N.waldhausen F.exact
  exact := ExtensionCategory.postcompose_exact M.waldhausen N.waldhausen F.exact

end ReedyCubeModel

variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- The original n-fold arrow category, with no cofibration restrictions. -/
def originalCube : ℕ → Cat.{u, u}
  | 0 => Cat.of C
  | n + 1 => Cat.of (Arrow (originalCube n))

/-- The genuine n-fold Reedy cofibration-arrow Waldhausen model. -/
def reedyCube : ℕ → ReedyCubeModel.{u}
  | 0 => ⟨C, W⟩
  | n + 1 => (reedyCube n).next

/-- The canonical forgetful map retains the original n-fold arrow diagram. -/
def reedyCubeForget : (n : ℕ) → (reedyCube W n).carrier ⥤ originalCube (C := C) n
  | 0 => 𝟭 C
  | n + 1 => ExtensionCategory.forget (reedyCube W n).waldhausen ⋙
      (reedyCubeForget n).mapArrow

/-- Pointwise weak equivalences in the literal original n-fold arrow category. -/
def originalCubeWeq : (n : ℕ) → MorphismProperty (originalCube (C := C) n)
  | 0 => W.weq
  | n + 1 => (originalCubeWeq n).inverseImage Arrow.leftFunc ⊓
      (originalCubeWeq n).inverseImage Arrow.rightFunc

/-- Pointwise weakness of an original finite cube contains identities. -/
theorem originalCubeWeq_id : (n : ℕ) → ∀ X, originalCubeWeq W n (𝟙 X)
  | 0, X => W.weq.id_mem X
  | n + 1, X => ⟨originalCubeWeq_id n X.left, originalCubeWeq_id n X.right⟩

/-- Composition is tested at the actual vertices at every finite stage. -/
theorem originalCubeWeq_comp : (n : ℕ) → ∀ {X Y Z : originalCube (C := C) n}
    (f : X ⟶ Y) (g : Y ⟶ Z), originalCubeWeq W n f → originalCubeWeq W n g →
      originalCubeWeq W n (f ≫ g)
  | 0, _, _, _, f, g, hf, hg => W.weq.comp_mem f g hf hg
  | n + 1, _, _, _, f, g, hf, hg =>
      ⟨originalCubeWeq_comp n f.left g.left hf.1 hg.1,
        originalCubeWeq_comp n f.right g.right hf.2 hg.2⟩

/-- Forgetting the genuine Reedy structure preserves and reflects exactly the
original pointwise weak equivalences. -/
theorem reedyCubeForget_weak_iff : (n : ℕ) →
    ∀ {X Y : (reedyCube W n).carrier} (f : X ⟶ Y),
      originalCubeWeq W n ((reedyCubeForget W n).map f) ↔ (reedyCube W n).waldhausen.weq f
  | 0, _, _, _ => Iff.rfl
  | n + 1, _, _, f => and_congr (reedyCubeForget_weak_iff n f.hom.left)
      (reedyCubeForget_weak_iff n f.hom.right)

/-- Saturation of the original class transfers to every finite pointwise
cube class. -/
theorem originalCubeWeq_saturated [W.weq.HasTwoOutOfThreeProperty] : (n : ℕ) →
    (originalCubeWeq W n).HasTwoOutOfThreeProperty
  | 0 => inferInstanceAs (W.weq.HasTwoOutOfThreeProperty)
  | n + 1 => by
      let := originalCubeWeq_saturated n
      change ((originalCubeWeq W n).inverseImage Arrow.leftFunc ⊓
        (originalCubeWeq W n).inverseImage Arrow.rightFunc).HasTwoOutOfThreeProperty
      infer_instance

/-- The actual vertices of an n-fold arrow diagram, as finite Boolean words. -/
def CubeVertex : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × CubeVertex n

/-- Evaluate a literal n-fold arrow diagram at a specified actual vertex. -/
def originalCubeVertex : (n : ℕ) → CubeVertex n → originalCube (C := C) n ⥤ C
  | 0, _ => 𝟭 C
  | n + 1, (false, v) => Arrow.leftFunc ⋙ originalCubeVertex n v
  | n + 1, (true, v) => Arrow.rightFunc ⋙ originalCubeVertex n v

/-- The recursive weak class is exactly weakness at every original vertex. -/
theorem originalCubeWeq_iff_vertices : (n : ℕ) →
    ∀ {X Y : originalCube (C := C) n} (f : X ⟶ Y),
      originalCubeWeq W n f ↔ ∀ v : CubeVertex n,
        W.weq ((originalCubeVertex n v).map f)
  | 0, _, _, f => by
      change W.weq f ↔ ∀ _ : Unit, W.weq f
      simp
  | n + 1, _, _, f => by
      change (originalCubeWeq W n f.left ∧ originalCubeWeq W n f.right) ↔ _
      rw [originalCubeWeq_iff_vertices n f.left, originalCubeWeq_iff_vertices n f.right]
      constructor
      · rintro ⟨hl, hr⟩ ⟨(_ | _), v⟩
        · exact hl v
        · exact hr v
      · intro h
        exact ⟨fun v ↦ h (false, v), fun v ↦ h (true, v)⟩

namespace FunctorialFactorization
variable {W} (T : FunctorialFactorization W)

/-- Finite iteration of the constructed genuine Reedy factorization. -/
def cubeFactorization : (n : ℕ) → FunctorialFactorization (reedyCube W n).waldhausen
  | 0 => T
  | n + 1 => (cubeFactorization n).reedyFactorization

/-- Every arbitrary original finite cube is coherently replaced by a genuine
Reedy cube. No input arrow is assumed to be a cofibration. -/
def cubeReplacement : (n : ℕ) → originalCube (C := C) n ⥤ (reedyCube W n).carrier
  | 0 => 𝟭 C
  | n + 1 => (cubeReplacement n).mapArrow ⋙
      (T.cubeFactorization n).cofibrationArrowReplacement

/-- The actual comparison to each original finite cube, natural in all cubes. -/
def cubeProjection : (n : ℕ) →
    T.cubeReplacement n ⋙ reedyCubeForget W n ⟶ 𝟭 (originalCube (C := C) n)
  | 0 => 𝟙 (𝟭 C)
  | n + 1 => Functor.whiskerRight
      (Functor.whiskerLeft (T.cubeReplacement n).mapArrow
        (T.cubeFactorization n).cofibrationArrowProjection)
      (reedyCubeForget W n).mapArrow ≫
        (Functor.mapArrowFunctor _ _).map (cubeProjection n)

/-- The comparison to every original finite cube is weak at all vertices,
proved by finite induction from the actual factorization projections. -/
theorem cubeProjection_weak : (n : ℕ) → ∀ X : originalCube (C := C) n,
    originalCubeWeq W n (T.cubeProjection n |>.app X)
  | 0, X => W.weq.id_mem X
  | n + 1, X => by
      have hq := (T.cubeFactorization n).cofibrationArrowProjection_weak
        ((T.cubeReplacement n).mapArrow.obj X)
      exact ⟨originalCubeWeq_comp W n _ _
          ((reedyCubeForget_weak_iff W n _).2 hq.1) (cubeProjection_weak n X.left),
        originalCubeWeq_comp W n _ _
          ((reedyCubeForget_weak_iff W n _).2 hq.2) (cubeProjection_weak n X.right)⟩

/-- Coherent replacement preserves pointwise weak maps of original finite
cubes, by the actual natural comparison and original saturation. -/
theorem cubeReplacement_weak [W.weq.HasTwoOutOfThreeProperty]
    (n : ℕ) {X Y : originalCube (C := C) n} (f : X ⟶ Y)
    (hf : originalCubeWeq W n f) :
    (reedyCube W n).waldhausen.weq ((T.cubeReplacement n).map f) := by
  let := originalCubeWeq_saturated W n
  apply (reedyCubeForget_weak_iff W n _).1
  apply (originalCubeWeq W n).of_postcomp _ (T.cubeProjection n |>.app Y)
    (T.cubeProjection_weak n Y)
  change originalCubeWeq W n
    ((T.cubeReplacement n ⋙ reedyCubeForget W n).map f ≫ (T.cubeProjection n).app Y)
  rw [(T.cubeProjection n).naturality]
  exact originalCubeWeq_comp W n _ _ (T.cubeProjection_weak n X) hf

/-- The weak comparison theorem expressed at every actual original vertex. -/
theorem cubeProjection_vertex_weak (n : ℕ) (X : originalCube (C := C) n)
    (v : CubeVertex n) :
    W.weq ((originalCubeVertex n v).map (T.cubeProjection n |>.app X)) :=
  (originalCubeWeq_iff_vertices W n _).1 (T.cubeProjection_weak n X) v

end FunctorialFactorization

/-- Every vertex of the recursively chosen source zero is the original zero. -/
theorem reedyCube_zero_vertex : (n : ℕ) → ∀ v : CubeVertex n,
    (originalCubeVertex n v).obj
      ((reedyCubeForget W n).obj (reedyCube W n).waldhausen.zero) = W.zero
  | 0, _ => rfl
  | n + 1, (false, v) => reedyCube_zero_vertex n v
  | n + 1, (true, v) => reedyCube_zero_vertex n v

variable {D : Type u'} [SmallCategory D] {V : Structure D} {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The exact original comparison iterated on actual finite Reedy cubes. -/
def reedyCubeMap : (n : ℕ) → ReedyCubeModel.ExactMap (reedyCube W n) (reedyCube V n)
  | 0 => ⟨F, hF⟩
  | n + 1 => (reedyCubeMap n).next

/-- The literal original functor iterated on arbitrary n-fold arrow diagrams. -/
def originalCubeMap : (n : ℕ) → originalCube (C := C) n ⥤ originalCube (C := D) n
  | 0 => F
  | n + 1 => (originalCubeMap n).mapArrow

/-- The finite Reedy comparison retains the actual original functor on all
underlying finite cubes, as strict equality of functors. -/
theorem reedyCubeMap_forget : (n : ℕ) →
    (reedyCubeMap W hF n).functor ⋙ reedyCubeForget V n =
      reedyCubeForget W n ⋙ originalCubeMap (F := F) n
  | 0 => rfl
  | n + 1 => by
      change ExtensionCategory.forget (reedyCube W n).waldhausen ⋙
        ((reedyCubeMap W hF n).functor ⋙ reedyCubeForget V n).mapArrow =
        ExtensionCategory.forget (reedyCube W n).waldhausen ⋙
          (reedyCubeForget W n ⋙ originalCubeMap (F := F) n).mapArrow
      rw [reedyCubeMap_forget n]

namespace HasApproximationProperty
variable {W} (h : HasApproximationProperty W V F)

include h in
/-- App1/App2 hold for all finite genuine Reedy cubes, by actual finite
induction from the original approximation property. -/
theorem reedyCube_approximation : (n : ℕ) →
    HasApproximationProperty (reedyCube W n).waldhausen (reedyCube V n).waldhausen
      (reedyCubeMap W hF n).functor
  | 0 => h
  | n + 1 => (reedyCube_approximation n).reedyArrow_approximation
      (reedyCubeMap W hF n).exact

end HasApproximationProperty
end Quillen.Waldhausen

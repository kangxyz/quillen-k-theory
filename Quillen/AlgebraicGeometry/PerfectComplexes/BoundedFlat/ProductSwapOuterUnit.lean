/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductSwapUnit

/-!
# The original outer unit under the forward product swap

The original map σ(P,L) pulls the inner Laurent unit back to the outer Laurent
unit. This is the inverse geometric direction to the earlier σ(L,P) equation.
The whole original Model unit track is retained at every time, using the same
normalized exact pullback and its literal prespectrum map. No compactness or
flatness hypothesis is introduced.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.FunctorIdentityAutomorphism Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.ProductSwapUnit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace Quillen.PerfectComplexes.ProductSwapOuterUnit

variable {S T : Scheme.{u}} (p : S ⟶ integerBase) (q : T ⟶ integerBase)
  (X : Scheme.{u})

/-- The new direction uses the literal inverse of the previously checked swap. -/
theorem swap_is_original_inverse :
    baseProductSwapMap p q X = (baseProductSwapIso q p).inv.app X := rfl

/-- Pullback along σ(S,T) sends the inner T-unit to the original outer T-unit. -/
theorem swap_outer_unit (r : Γ(T, ⊤)ˣ) :
    Units.map (baseProductSwapMap p q X).appTop.hom.toMonoidHom
      (innerUnit q p X r) = outerUnit q p X r := by
  apply Units.ext
  have h := congrArg (fun f => f.appTop) (baseProductSwapMap_fst_snd p q X)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑r)

/-- The actual normalized pullback preserves this correctly directed original unit. -/
theorem normalizedSwap_preserves (r : Γ(T, ⊤)ˣ) :
    Preserves (boundedFlatNormalizedPullback (baseProductSwapMap p q X))
      (boundedFlatPerfectGlobalUnitIso _ (innerUnit q p X r))
      (boundedFlatPerfectGlobalUnitIso _ (outerUnit q p X r)) := by
  have h := GlobalUnitReferenceNaturality.normalizedPullback_preserves
    (baseProductSwapMap p q X) (innerUnit q p X r)
  rw [swap_outer_unit] at h
  exact h

private instance smallDown_isEquivalence {Y : Scheme.{u}} :
    (AsSmall.down : SmallModel (BoundedFlatPerfect Y) ⥤ BoundedFlatPerfect Y).IsEquivalence :=
  (AsSmall.equiv : BoundedFlatPerfect Y ≌
    SmallModel (BoundedFlatPerfect Y)).isEquivalence_inverse

/-- Faithful lowering preserves the same actual unit in the original small Model. -/
theorem swapModelMap_preserves (r : Γ(T, ⊤)ˣ) :
    Preserves (swapModelMap p q X).functor
      (smallUnit _ (innerUnit q p X r)) (smallUnit _ (outerUnit q p X r)) := by
  intro K
  apply (AsSmall.down : SmallModel (BoundedFlatPerfect
    ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))) ⥤ _).map_injective
  change (boundedFlatNormalizedPullback (baseProductSwapMap p q X)).map
      (AsSmall.down.map ((smallUnit _ (innerUnit q p X r)).hom.app K)) =
    AsSmall.down.map ((smallUnit _ (outerUnit q p X r)).hom.app
      (AsSmall.up.obj ((boundedFlatNormalizedPullback (baseProductSwapMap p q X)).obj
        (AsSmall.down.obj K))))
  rw [smallUnit, map_lift_hom, smallUnit, map_lift_hom]
  exact normalizedSwap_preserves p q X r (AsSmall.down.obj K)

/-- The complete original unit track commutes at every time with σ(S,T) pullback. -/
theorem unitTrack_square {V : Model.{u + 1}}
    (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      ((baseProductFunctor p).obj ((baseProductFunctor q).obj X))))
    (r : Γ(T, ⊤)ˣ) (t : unitInterval) :
    (prespectrumIsoHomotopy G (onFunctor G.functor
      (smallUnit _ (innerUnit q p X r)))).at t ≫ prespectrumMap (swapModelMap p q X) =
    (prespectrumIsoHomotopy (G ≫ swapModelMap p q X)
      (onFunctor (G ≫ swapModelMap p q X).functor
        (smallUnit _ (outerUnit q p X r)))).at t := by
  have h : G ≫ swapModelMap p q X = 𝟙 V ≫ (G ≫ swapModelMap p q X) := by simp
  have e := prespectrumIsoHomotopy_square_at G (G ≫ swapModelMap p q X)
    (𝟙 V) (swapModelMap p q X)
    (onFunctor G.functor (smallUnit _ (innerUnit q p X r)))
    (onFunctor (G ≫ swapModelMap p q X).functor (smallUnit _ (outerUnit q p X r))) h
    (onFunctor_whisker_square G.functor (G ≫ swapModelMap p q X).functor
      (𝟙 V : V ⟶ V).functor (swapModelMap p q X).functor
      (eqToHom (congrArg Model.Hom.functor h))
      (smallUnit _ (innerUnit q p X r)) (smallUnit _ (outerUnit q p X r))
      (swapModelMap_preserves p q X r).whisker) t
  have hi : prespectrumMap (𝟙 V) = (𝟙 (prespectrum V) : prespectrum V ⟶ prespectrum V) :=
    prespectrumFunctor.map_id V
  simpa only [hi, Category.id_comp] using e

/-- The actual polynomial/Laurent interchange keeps the original Laurent generator. -/
theorem polynomial_laurent_swap_unit :
    Units.map (baseProductSwapMap (polynomialProjection (.of (ULift.{u} ℤ)))
      (laurentProjection (.of (ULift.{u} ℤ))) X).appTop.hom.toMonoidHom
      (innerUnit (laurentProjection (.of (ULift.{u} ℤ)))
        (polynomialProjection (.of (ULift.{u} ℤ))) X
        (laurentGlobalUnit (.of (ULift.{u} ℤ)))) =
    outerUnit (laurentProjection (.of (ULift.{u} ℤ)))
      (polynomialProjection (.of (ULift.{u} ℤ))) X
      (laurentGlobalUnit (.of (ULift.{u} ℤ))) := swap_outer_unit _ _ X _

end Quillen.PerfectComplexes.ProductSwapOuterUnit

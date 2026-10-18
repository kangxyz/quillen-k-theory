/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Aglib.AlgebraicGeometry.Products.IntegerBaseInterchange
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Units
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitReferenceNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIsoNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback

/-!
# Actual independent-variable swap preserves the first-factor unit

The original first factor becomes the outer factor after swapping. The map is
contravariant on global sections and on normalized bounded-flat pullback.
There are no quasi-compactness or flatness assumptions. This independent
reconstruction is adopted here; it does not construct a mixed-axis
global coefficient-index transformation or an all-stage seed comparison.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open Quillen.FunctorIdentityAutomorphism
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace Quillen.PerfectComplexes.ProductSwapUnit

variable {S T : Scheme.{u}} (p : S ⟶ integerBase) (q : T ⟶ integerBase)
  (X : Scheme.{u})

/-- Projection to S in the unswapped product (X × S) × T. -/
def innerProjection : (baseProductFunctor q).obj ((baseProductFunctor p).obj X) ⟶ S :=
  pullback.fst (toIntegerBase ((baseProductFunctor p).obj X)) q ≫
    pullback.snd (toIntegerBase X) p

/-- Projection to S in the swapped product (X × T) × S. -/
def outerProjection : (baseProductFunctor p).obj ((baseProductFunctor q).obj X) ⟶ S :=
  pullback.snd (toIntegerBase ((baseProductFunctor q).obj X)) p

/-- The original first-factor unit on the unswapped product. -/
def innerUnit (r : Γ(S, ⊤)ˣ) :
    Γ((baseProductFunctor q).obj ((baseProductFunctor p).obj X), ⊤)ˣ :=
  Units.map (innerProjection p q X).appTop.hom.toMonoidHom r

/-- The same factor's unit on the swapped product. -/
def outerUnit (r : Γ(S, ⊤)ˣ) :
    Γ((baseProductFunctor p).obj ((baseProductFunctor q).obj X), ⊤)ˣ :=
  Units.map (outerProjection p q X).appTop.hom.toMonoidHom r

/-- Pulling back the outer S-unit along the actual swap recovers the inner S-unit. -/
theorem swap_unit (r : Γ(S, ⊤)ˣ) :
    Units.map (baseProductSwapMap p q X).appTop.hom.toMonoidHom
      (outerUnit p q X r) = innerUnit p q X r := by
  apply Units.ext
  have h := congrArg (fun f => f.appTop) (baseProductSwapMap_snd p q X)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑r)

/-- The original normalized bounded-flat pullback preserves the actual swapped unit. -/
theorem normalizedSwap_preserves (r : Γ(S, ⊤)ˣ) :
    Preserves (boundedFlatNormalizedPullback (baseProductSwapMap p q X))
      (boundedFlatPerfectGlobalUnitIso
        ((baseProductFunctor p).obj ((baseProductFunctor q).obj X))
        (outerUnit p q X r))
      (boundedFlatPerfectGlobalUnitIso
        ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))
        (innerUnit p q X r)) := by
  have h := GlobalUnitReferenceNaturality.normalizedPullback_preserves
    (baseProductSwapMap p q X) (outerUnit p q X r)
  rw [swap_unit] at h
  exact h


local instance {Y : Scheme.{u}} :
    (AsSmall.down : SmallModel (BoundedFlatPerfect Y) ⥤ BoundedFlatPerfect Y).IsEquivalence :=
  (AsSmall.equiv : BoundedFlatPerfect Y ≌
    SmallModel (BoundedFlatPerfect Y)).isEquivalence_inverse

/-- The genuine global scalar lifted through the original faithful small-model equivalence. -/
def smallUnit (Y : Scheme.{u}) (r : (Γ(Y, ⊤))ˣ) :
    𝟭 (SmallModel (BoundedFlatPerfect Y)) ≅ 𝟭 (SmallModel (BoundedFlatPerfect Y)) :=
  lift (AsSmall.down : SmallModel (BoundedFlatPerfect Y) ⥤ BoundedFlatPerfect Y)
    (boundedFlatPerfectGlobalUnitIso Y r)

/-- The actual normalized geometric swap as an original zero-preserving exact Model map. -/
def swapModelMap :
    modelOf (boundedFlatPerfectWaldhausen
      ((baseProductFunctor p).obj ((baseProductFunctor q).obj X))) ⟶
    modelOf (boundedFlatPerfectWaldhausen
      ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact (baseProductSwapMap p q X))
    (boundedFlatNormalizedPullback_obj_zero _)

/-- The Model map is precisely the original geometric prespectrum pullback. -/
theorem swapModelMap_prespectrum :
    prespectrumMap (swapModelMap p q X) =
      boundedFlatPerfectPrespectrumMap (baseProductSwapMap p q X) := rfl

/-- Faithful lowering lifts the actual scalar equation to the original small Model. -/
theorem swapModelMap_preserves (r : (Γ(S, ⊤))ˣ) :
    Preserves (swapModelMap p q X).functor
      (smallUnit ((baseProductFunctor p).obj ((baseProductFunctor q).obj X))
        (outerUnit p q X r))
      (smallUnit ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))
        (innerUnit p q X r)) := by
  intro K
  apply (AsSmall.down : SmallModel (BoundedFlatPerfect
    ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))) ⥤ _).map_injective
  change (boundedFlatNormalizedPullback (baseProductSwapMap p q X)).map
      (AsSmall.down.map ((smallUnit _ (outerUnit p q X r)).hom.app K)) =
    AsSmall.down.map ((smallUnit _ (innerUnit p q X r)).hom.app
      (AsSmall.up.obj ((boundedFlatNormalizedPullback (baseProductSwapMap p q X)).obj
        (AsSmall.down.obj K))))
  rw [smallUnit, map_lift_hom, smallUnit, map_lift_hom]
  exact normalizedSwap_preserves p q X r (AsSmall.down.obj K)

/-- Every time slice of the original geometric unit track commutes with the actual swap. -/
theorem unitTrack_square {V : Model.{u + 1}}
    (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      ((baseProductFunctor p).obj ((baseProductFunctor q).obj X))))
    (r : (Γ(S, ⊤))ˣ) (t : unitInterval) :
    (prespectrumIsoHomotopy G (onFunctor G.functor
      (smallUnit _ (outerUnit p q X r)))).at t ≫ prespectrumMap (swapModelMap p q X) =
    (prespectrumIsoHomotopy (G ≫ swapModelMap p q X)
      (onFunctor (G ≫ swapModelMap p q X).functor
        (smallUnit _ (innerUnit p q X r)))).at t := by
  have h : G ≫ swapModelMap p q X = 𝟙 V ≫ (G ≫ swapModelMap p q X) := by simp
  have e := prespectrumIsoHomotopy_square_at G (G ≫ swapModelMap p q X)
    (𝟙 V) (swapModelMap p q X)
    (onFunctor G.functor (smallUnit _ (outerUnit p q X r)))
    (onFunctor (G ≫ swapModelMap p q X).functor (smallUnit _ (innerUnit p q X r))) h
    (onFunctor_whisker_square G.functor (G ≫ swapModelMap p q X).functor
      (𝟙 V : V ⟶ V).functor (swapModelMap p q X).functor
      (eqToHom (congrArg Model.Hom.functor h))
      (smallUnit _ (outerUnit p q X r)) (smallUnit _ (innerUnit p q X r))
      (swapModelMap_preserves p q X r).whisker) t
  have hi : prespectrumMap (𝟙 V) = (𝟙 (prespectrum V) : prespectrum V ⟶ prespectrum V) :=
    prespectrumFunctor.map_id V
  simpa only [hi, Category.id_comp] using e

/-- The swap preserves the original Laurent generator in the specified first factor. -/
theorem laurent_swap_unit :
    Units.map (baseProductSwapMap
        (laurentProjection (.of (ULift.{u} ℤ))) q X).appTop.hom.toMonoidHom
      (outerUnit (laurentProjection (.of (ULift.{u} ℤ))) q X
        (laurentGlobalUnit (.of (ULift.{u} ℤ)))) =
    innerUnit (laurentProjection (.of (ULift.{u} ℤ))) q X
      (laurentGlobalUnit (.of (ULift.{u} ℤ))) :=
  swap_unit (laurentProjection (.of (ULift.{u} ℤ))) q X
    (laurentGlobalUnit (.of (ULift.{u} ℤ)))

/-- The whole original Laurent-unit track retains the actual swap square. -/
theorem laurent_unitTrack_square {V : Model.{u + 1}}
    (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      ((baseProductFunctor (laurentProjection (.of (ULift.{u} ℤ)))).obj
        ((baseProductFunctor q).obj X)))) (t : unitInterval) :
    (prespectrumIsoHomotopy G (onFunctor G.functor
      (smallUnit _ (outerUnit (laurentProjection (.of (ULift.{u} ℤ))) q X
        (laurentGlobalUnit (.of (ULift.{u} ℤ))))))).at t ≫
      prespectrumMap (swapModelMap (laurentProjection (.of (ULift.{u} ℤ))) q X) =
    (prespectrumIsoHomotopy
      (G ≫ swapModelMap (laurentProjection (.of (ULift.{u} ℤ))) q X)
      (onFunctor (G ≫ swapModelMap (laurentProjection (.of (ULift.{u} ℤ))) q X).functor
        (smallUnit _ (innerUnit (laurentProjection (.of (ULift.{u} ℤ))) q X
          (laurentGlobalUnit (.of (ULift.{u} ℤ))))))).at t :=
  unitTrack_square (laurentProjection (.of (ULift.{u} ℤ))) q X G
    (laurentGlobalUnit (.of (ULift.{u} ℤ))) t

end Quillen.PerfectComplexes.ProductSwapUnit

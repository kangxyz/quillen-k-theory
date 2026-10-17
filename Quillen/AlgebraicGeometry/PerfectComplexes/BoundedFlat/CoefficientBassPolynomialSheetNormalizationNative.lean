/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPolynomialSheetNormalization
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation

/-! Native invariance of the actual complete-reference polynomial sheet normalization. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPolynomialSheetNormalization
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {V W T : Model.{u}} (F F' : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (ε : G.functor ≅ (F ≫ J).functor) (δ : F'.functor ≅ F.functor)

/-- The continuous full-reference reanchoring of the polynomial sheet along the supplied `δ`. -/
abbrev polynomialMap := TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor δ))
/-- The corresponding continuous Laurent-reference reanchoring through the induced anchor
isomorphism. -/
abbrev laurentMap := TopCat.ofHom (mapParameter
  (CommonReferenceProduct.reanchor (laurentIso F F' J G ε δ)))

/-- The existing two-sheet map is used only to prove the included first-sheet evaluation law. -/
def fullMap := CommonReferenceNerve.CutOpenMap.map F J G F' J (F' ≫ J)
  ε ε (Iso.refl _) (Iso.refl _) (polynomialMap F F' δ) (laurentMap F F' J G ε δ)
  (attachment_square F F' J G ε δ) (attachment_square F F' J G ε δ)

/-- Complete-reference reanchoring preserves every native value on the original cells. -/
theorem fullMap_native (n : ℕ) (z : space F J G ε ε)
    (x : (prespectrum V).space n) :
    nativeEval F' J (F' ≫ J) (Iso.refl _) (Iso.refl _) n
      (fullMap F F' J G ε δ z) x = nativeEval F J G ε ε n z x := by
  rcases exists_native_cell F J G ε ε z with
    ⟨y, rfl⟩ | ⟨y, t, rfl⟩ | ⟨y, t, rfl⟩ | rfl | rfl
  · rw [fullMap, CommonReferenceNerve.CutOpenMap.map_laurent,
      nativeEval_laurentInclusion, nativeEval_laurentInclusion]
    exact congrArg ((Quillen.LoopPrespectrum.mappingConeInclusion (prespectrumMap J)).map n)
      (pointwise_reanchor (laurentIso F F' J G ε δ) n y x)
  · rw [fullMap, CommonReferenceNerve.CutOpenMap.map_cylinderMinus,
      nativeEval_cylinderMinus, nativeEval_cylinderMinus]
    exact congrArg (fun z ↦ Quillen.ReducedMappingCone.cylinder _ _ _ (t, z))
      (pointwise_reanchor δ n y x)
  · rw [fullMap, CommonReferenceNerve.CutOpenMap.map_cylinderPlus,
      nativeEval_cylinderPlus, nativeEval_cylinderPlus]
    exact congrArg (fun z ↦ Quillen.ReducedMappingCone.cylinder _ _ _ (t, z))
      (pointwise_reanchor δ n y x)
  · rw [fullMap, CommonReferenceNerve.CutOpenMap.map_tipMinus,
      nativeEval_tipMinus, nativeEval_tipMinus]
  · rw [fullMap, CommonReferenceNerve.CutOpenMap.map_tipPlus,
      nativeEval_tipPlus, nativeEval_tipPlus]

/-- The actual single-sheet normalization preserves all degrees and arbitrary native inputs. -/
theorem map_native (n : ℕ) (z : |firstSimplicial F J G ε|)
    (x : (prespectrum V).space n) :
    nativeEval F' J (F' ≫ J) (Iso.refl _) (Iso.refl _) n
      (SSet.toTop.map (left₁ F' J (F' ≫ J) (Iso.refl _) (Iso.refl _))
        (map F F' J G ε δ z)) x =
    nativeEval F J G ε ε n (SSet.toTop.map (left₁ F J G ε ε) z) x := by
  have h := ConcreteCategory.congr_hom
    (CommonReferenceNerve.CutOpenMap.map_first F J G F' J (F' ≫ J)
      ε ε (Iso.refl _) (Iso.refl _) (polynomialMap F F' δ) (laurentMap F F' J G ε δ)
      (attachment_square F F' J G ε δ) (attachment_square F F' J G ε δ)) z
  exact (congrArg (fun y ↦ nativeEval F' J (F' ≫ J) (Iso.refl _) (Iso.refl _) n y x)
    h.symm).trans (fullMap_native F F' J G ε δ n _ x)

end Quillen.PerfectComplexes.CoefficientBassPolynomialSheetNormalization

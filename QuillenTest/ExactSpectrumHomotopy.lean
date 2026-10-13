/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ExactCoherence

/-! Consumers of the actual spectrum maps, whole based homotopies and original K-map. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u v
namespace QuillenTest.ExactSpectrumHomotopy

open Quillen
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (W : Structure C) (V : Structure D) (U : Structure E)
  {F G : C ⥤ D} (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)

/-- No strict chosen-zero condition enters the original K-map comparison. -/
theorem original_K_map (n : ℕ) (a : W.K n) :
    originalZeroSpaceEquiv V n (KMap hF n a) =
      homotopyGroupMap ((exactOriginalPrespectrumMap W V hF).map 0)
        ((exactOriginalPrespectrumMap W V hF).map_point 0) (originalZeroSpaceEquiv W n a) :=
  exactOriginalZeroSpaceEquiv_naturality W V hF n a

/-- Every time slice of the weak-transformation track is an original prespectrum map. -/
theorem whole_structure_square (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A))
    (n : ℕ) (s t : unitInterval) (x : (originalPrespectrum W).space n) :
    (exactOriginalPrespectrumHomotopy W V hF hG η hη).level (n+1)
      (s,(originalPrespectrum W).structureMap n x t) =
      (originalPrespectrum V).structureMap n
        ((exactOriginalPrespectrumHomotopy W V hF hG η hη).level n (s,x)) t :=
  (exactOriginalPrespectrumHomotopy W V hF hG η hη).comm n s x t

/-- The entire track preserves the original basepoint, not merely its endpoints. -/
theorem whole_basepoint_track (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A))
    (n : ℕ) (s : unitInterval) :
    (exactOriginalPrespectrumHomotopy W V hF hG η hη).level n
      (s,(originalPrespectrum W).point n) = (originalPrespectrum V).point n :=
  (exactOriginalPrespectrumHomotopy W V hF hG η hη).at_point n s

/-- Both actual endpoint maps are retained. -/
theorem actual_endpoints (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) :
    (exactOriginalPrespectrumHomotopy W V hF hG η hη).at 0 = exactOriginalPrespectrumMap W V hF ∧
    (exactOriginalPrespectrumHomotopy W V hF hG η hη).at 1 = exactOriginalPrespectrumMap W V hG :=
  ⟨LoopPrespectrum.Homotopy.at_zero_eq _, LoopPrespectrum.Homotopy.at_one_eq _⟩

/-- The original level homotopy maps agree, including level and degree zero. -/
theorem original_level_maps (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) (n k : ℕ) :
    homotopyGroupMap (N := Fin k) ((exactOriginalPrespectrumMap W V hF).map n)
      ((exactOriginalPrespectrumMap W V hF).map_point n) =
    homotopyGroupMap ((exactOriginalPrespectrumMap W V hG).map n)
      ((exactOriginalPrespectrumMap W V hG).map_point n) :=
  (exactOriginalPrespectrumHomotopy W V hF hG η hη).homotopyGroupMap_eq n k

/-- The natural-isomorphism specialization uses a full structure-compatible homotopy. -/
theorem original_iso_endpoint (e : F ≅ G) :
    (exactOriginalPrespectrumIsoHomotopy W V hF hG e).at 1 = exactOriginalPrespectrumMap W V hG :=
  LoopPrespectrum.Homotopy.at_one_eq _

/-- Identity reaches the literal identity spectrum map. -/
theorem identity_endpoint :
    (exactOriginalPrespectrumMapIdHomotopy W).at 1 = 𝟙 (originalPrespectrum W) :=
  LoopPrespectrum.Homotopy.at_one_eq _

/-- Binary composition reaches the actual composite, without a zero-image hypothesis. -/
theorem composition_endpoint {J : D ⥤ E} (hJ : IsExact V.cof V.weq U.cof U.weq J) :
    (exactOriginalPrespectrumMapCompHomotopy W V U hF hJ).at 1 =
      exactOriginalPrespectrumMap W V hF ≫ exactOriginalPrespectrumMap V U hJ :=
  LoopPrespectrum.Homotopy.at_one_eq _

/-- In the zero-preserving subcase composition is the genuine original strict composite. -/
theorem original_strict_composition {J : D ⥤ E} (hJ : IsExact V.cof V.weq U.cof U.weq J)
    (h0F : F.obj W.zero = V.zero) (h0J : J.obj V.zero = U.zero) :
    originalPrespectrumMap W U (hF.comp hJ) ((congrArg J.obj h0F).trans h0J) =
      originalPrespectrumMap W V hF h0F ≫ originalPrespectrumMap V U hJ h0J :=
  originalPrespectrumMap_comp W V U hF hJ h0F h0J

end QuillenTest.ExactSpectrumHomotopy

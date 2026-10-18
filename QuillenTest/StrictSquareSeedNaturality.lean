/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.StrictSquareSeedNaturality

/-!
# Composition regression for the original strict-square seed

Two actual square maps with whole same-time scalar compatibility preserve the original
null/unit/null loop after composition. The original source and target nullhomotopies
remain the specified ones, without any new chosen null track.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.LoopPrespectrum.StrictSquare
universe u

example {S T R : Arrow (Arrow Quillen.LoopPrespectrum.{u})} (e : S ⟶ T) (f : T ⟶ R)
    (U : Homotopy (S.left.hom ≫ S.hom.right) (S.left.hom ≫ S.hom.right))
    (V : Homotopy (T.left.hom ≫ T.hom.right) (T.left.hom ≫ T.hom.right))
    (W : Homotopy (R.left.hom ≫ R.hom.right) (R.left.hom ≫ R.hom.right))
    (he : ∀ n r x, e.right.right.map n (U.level n (r, x)) =
      V.level n (r, e.left.left.map n x))
    (hf : ∀ n r x, f.right.right.map n (V.level n (r, x)) =
      W.level n (r, f.left.left.map n x)) :
    (U.postcomp (mappingConeInclusion (comparison S))).nullLoopMap
        (sourceNullHomotopy S) ≫ strictSquareLoopedConeFunctor.map (e ≫ f) =
      (e.left.left ≫ f.left.left) ≫
        (W.postcomp (mappingConeInclusion (comparison R))).nullLoopMap
          (sourceNullHomotopy R) := by
  apply sourceSeed_naturality (e ≫ f) U W
  intro n r x
  change f.right.right.map n (e.right.right.map n (U.level n (r, x))) =
    W.level n (r, f.left.left.map n (e.left.left.map n x))
  rw [he, hf]

#print axioms Quillen.LoopPrespectrum.StrictSquare.sourceSeed_naturality
#print axioms Quillen.LoopPrespectrum.StrictSquare.sourceSeed_naturality_apply

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopyNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumTransformationTransport

/-!
# Whole original zero-source transformation tracks under strict Model squares

A strict square of actual chosen-zero-preserving Model maps automatically identifies the whole
realized tracks of transformations from their original zero functors. Pointwise uniqueness from
the actual zero objects proves the categorical transformation square, including the source-zero
transport. The original homotopy time and the degree-zero loop coordinate are unchanged.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor Quillen.LoopPrespectrum
universe u
namespace Quillen.Waldhausen.IteratedS

/-- Actual zero Model maps commute with the original chosen-zero-preserving square sides. -/
theorem zeroHom_square {V W T U : Model.{u}} (a : V ⟶ T) (b : W ⟶ U) :
    zeroHom V W ≫ b = a ≫ zeroHom T U := by
  apply Model.Hom.ext
  refine CategoryTheory.Functor.ext (fun _ => b.zero) ?_
  intro X Y f
  exact (b.exact.zero W.waldhausen.isZero).eq_of_src _ _

/-- The whole original zero-source tracks commute with every strict original Model square. -/
theorem prespectrumZeroTransformationHomotopy_naturality
    {V W T U : Model.{u}} (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (h : F ≫ b = a ≫ G)
    (η : (zeroHom V W).functor ⟶ F.functor)
    (θ : (zeroHom T U).functor ⟶ G.functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (hθ : ∀ X, U.waldhausen.weq (θ.app X)) (n : ℕ) :
    ((prespectrumTransformationHomotopy η hη).postcomp (prespectrumMap b)).level n =
      (Homotopy.precomp (prespectrumMap a) (prespectrumTransformationHomotopy θ hθ)).level n := by
  let α : (zeroHom V W ≫ b).functor ⟶ (F ≫ b).functor := whiskerRight η b.functor
  let β : (a ≫ zeroHom T U).functor ⟶ (a ≫ G).functor := whiskerLeft a.functor θ
  have hzero := zeroHom_square a b
  have he : α = eqToHom (congrArg Model.Hom.functor hzero) ≫ β ≫
      eqToHom (congrArg Model.Hom.functor h.symm) := by
    ext X
    exact (b.exact.zero W.waldhausen.isZero).eq_of_src _ _
  have ht : ∀ X, U.waldhausen.weq
      ((eqToHom (congrArg Model.Hom.functor hzero) ≫ β ≫
        eqToHom (congrArg Model.Hom.functor h.symm)).app X) := by
    intro X
    have hx := congrArg (fun σ => σ.app X) he
    rw [← hx]
    exact b.exact.weak _ (hη X)
  have hc := prespectrumTransformationHomotopy_transport_level hzero h.symm β
    (fun X => hθ (a.functor.obj X)) ht n
  have heLevel : (prespectrumTransformationHomotopy α
      (fun X => b.exact.weak _ (hη X))).level n =
        (prespectrumTransformationHomotopy
          (eqToHom (congrArg Model.Hom.functor hzero) ≫ β ≫
            eqToHom (congrArg Model.Hom.functor h.symm)) ht).level n := by
    exact prespectrumTransformationHomotopy_level_eq_of_heq rfl rfl _ _ _ _ (heq_of_eq he) n
  exact (prespectrumTransformationHomotopy_postcomp_level η hη b n).symm.trans
    (heLevel.trans (hc.trans (prespectrumTransformationHomotopy_precomp_level θ hθ a n)))

end Quillen.Waldhausen.IteratedS

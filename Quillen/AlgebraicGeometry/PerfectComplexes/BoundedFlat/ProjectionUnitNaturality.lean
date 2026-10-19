/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductUnitInterchangeSign

/-!
# Naturality of the actual geometric projection-unit operation

Arbitrary scheme pullback preserves the original independent-factor unit and
its original projection. The resulting square is an equality of the actual
nonnegative K-operations, including degree zero and chosen-zero normalization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.ProductUnitInterchange
variable {S : Scheme.{u}} (p : S ⟶ integerBase)

/-- Every base map preserves the same independent-factor unit on its product. -/
theorem projectionUnit_map {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(S, ⊤))ˣ) :
    Units.map ((baseProductFunctor p).map f).appTop.hom.toMonoidHom
      (projectionUnit p Y r) = projectionUnit p X r := by
  apply Units.ext
  have h : (baseProductFunctor p).map f ≫ pullback.snd (toIntegerBase Y) p =
      pullback.snd (toIntegerBase X) p := by
    simp [baseProductFunctor]
  have hs := congrArg (fun g ↦ g.appTop) h
  rw [Scheme.Hom.comp_appTop] at hs
  exact ConcreteCategory.congr_hom hs (↑r)

/-- The original projection-unit operation is natural under every actual scheme morphism. -/
theorem projectionUnitOperation_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(S, ⊤))ˣ) (n : ℕ) :
    (boundedFlatPerfectKPullback ((baseProductFunctor p).map f) (n + 1)).comp
        (projectionUnitOperation p Y r n) =
      (projectionUnitOperation p X r n).comp (boundedFlatPerfectKPullback f n) := by
  unfold projectionUnitOperation
  rw [boundedFlatPerfectUnitHomotopy_originalKOperation_postcomp,
    boundedFlatPerfectUnitHomotopy_originalKOperation_precomp, projectionUnit_map]
  exact congrArg (fun g ↦ originalKSelfTrackOperation
    (boundedFlatPerfectWaldhausen Y)
    (boundedFlatPerfectWaldhausen ((baseProductFunctor p).obj X))
    (boundedFlatPerfectUnitHomotopy g (projectionUnit p X r)) n)
    ((baseProductProjection p).naturality f)

end Quillen.PerfectComplexes.ProductUnitInterchange

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.TheoremA.AttachmentHomology

/-! Strict consumers of the original replacement-skeleton relative comparison. -/

@[expose] public section
noncomputable section
open CategoryTheory Limits Quillen.TheoremA Quillen.LocalCoefficients
universe u

example {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u}) (n : ℕ)
    (L : System.{u, u} ((realizedReplacementSkeleton H).obj (n + 1))) :
    QuasiIso (replacementCellRelativeChainMap H n L) :=
  replacementCellRelativeChainMap_quasiIso H n L

example {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})
    (L : System.{u, u} ((realizedReplacementSkeleton H).obj 1)) :
    QuasiIso (replacementCellRelativeChainMap H 0 L) :=
  replacementCellRelativeChainMap_quasiIso H 0 L

example {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u}) (n : ℕ)
    (L : System.{u, u} ((realizedReplacementSkeleton H).obj (n + 1))) :
    cokernel.π (pushforwardChainMap
        (subspaceInclusion
          (Quillen.SimplexAttachment.sourceBoundary (replacementCellParameters H n) n))
        (pullback (replacementGeometricCharacteristic H n).hom L)) ≫
      replacementCellRelativeChainMap H n L =
    pushforwardChainMap (replacementGeometricCharacteristic H n).hom L ≫
      cokernel.π (pushforwardChainMap (replacementSkeletonStep H n) L) :=
  replacementCellRelativeChainMap_quotient H n L

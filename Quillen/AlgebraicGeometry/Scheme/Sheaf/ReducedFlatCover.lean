/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatRetracts
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatResolution
public import Mathlib.Algebra.Homology.LeftResolution.Reduced

/-!
# Zero-preserving reductions of actual flat covers

The genuine Karoubi reduction of the flat cover gives a zero-preserving cover
functor, which can safely be applied to complex differentials. Additivity is
not asserted. The resulting cover of complexes is epic in every degree but
is not asserted to be a quasi-isomorphism.
-/
@[expose] public section
open Quillen
open Quillen.SchemeSheaf



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- A zero-preserving left resolution, obtained by actually splitting the reduced idempotent. -/
def reducedFlatSheafLeftResolution (X : Scheme.{u}) :
    Abelian.LeftResolution (stalkwiseFlat X).ι := (flatSheafLeftResolution X).reduced

instance reducedFlatSheafLeftResolution_preservesZero (X : Scheme.{u}) :
    (reducedFlatSheafLeftResolution X).F.PreservesZeroMorphisms := by
  unfold reducedFlatSheafLeftResolution
  infer_instance

/-- The ambient genuine reduced flat cover functor. -/
def reducedFlatCoverFunctor (X : Scheme.{u}) : X.Modules ⥤ X.Modules :=
  (reducedFlatSheafLeftResolution X).F ⋙ (stalkwiseFlat X).ι

instance reducedFlatCoverFunctor_preservesZero (X : Scheme.{u}) :
    (reducedFlatCoverFunctor X).PreservesZeroMorphisms := by
  unfold reducedFlatCoverFunctor
  infer_instance

/-- Every actual reduced cover still consists of a flat module sheaf. -/
theorem reducedFlatCoverFunctor_flat (X : Scheme.{u}) (M : X.Modules) :
    stalkwiseFlat X ((reducedFlatCoverFunctor X).obj M) :=
  ((reducedFlatSheafLeftResolution X).F.obj M).property

/-- The reduced cover retains the proved epimorphic augmentation. -/
def reducedFlatCoverAugmentation (X : Scheme.{u}) : reducedFlatCoverFunctor X ⟶ 𝟭 X.Modules :=
  (reducedFlatSheafLeftResolution X).π

instance reducedFlatCoverAugmentation_epi (X : Scheme.{u}) (M : X.Modules) :
    Epi ((reducedFlatCoverAugmentation X).app M) :=
  (reducedFlatSheafLeftResolution X).epi_π_app M

/-- Unlike the unreduced cover, the actual reduced cover can be safely applied to complexes. -/
def reducedFlatCoverComplex (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  (reducedFlatCoverFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The degreewise reduced cover is genuinely a complex of flat sheaves. -/
theorem reducedFlatCoverComplex_flat (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    stalkwiseFlat X (((reducedFlatCoverComplex X).obj K).X n) :=
  reducedFlatCoverFunctor_flat X (K.X n)

/-- This cover preserves an actual strict upper bound. -/
theorem reducedFlatCoverComplex_boundedAbove (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (b : ℤ) (hb : ∀ n, b < n → IsZero (K.X n)) (n : ℤ) (hn : b < n) :
    IsZero (((reducedFlatCoverComplex X).obj K).X n) :=
  (reducedFlatCoverFunctor X).map_isZero (hb n hn)

/-- The actual degreewise epimorphic map from the flat cover complex to the input complex. -/
def reducedFlatCoverComplexAugmentation (X : Scheme.{u}) :
    reducedFlatCoverComplex X ⟶ 𝟭 (CochainComplex X.Modules ℤ) :=
  NatTrans.mapHomologicalComplex (reducedFlatCoverAugmentation X) (ComplexShape.up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso X.Modules (ComplexShape.up ℤ)).hom

/-- The complex cover is epic in every actual degree; it is not asserted to be a quasiiso. -/
instance reducedFlatCoverComplexAugmentation_degree_epi (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    Epi (((reducedFlatCoverComplexAugmentation X).app K).f n) := by
  change Epi ((reducedFlatCoverAugmentation X).app (K.X n) ≫ 𝟙 _)
  infer_instance

end AlgebraicGeometry.Scheme.Modules

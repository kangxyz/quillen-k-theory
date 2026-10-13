/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Map.CoherenceData
public import Quillen.Topology.ClassifyingSpace.NaturalTransformationTracks
public import Quillen.Topology.HomotopyGroups.PathTransportGroup

/-!
# Original Q-maps and strictly rebased K-maps

The natural isomorphism from a functor to its rebasing realizes to a homotopy
whose specified vertex follows exactly the edge of the supplied base-object
isomorphism. Transport along that actual edge identifies the raw induced map
with the repository's original strictly rebased homotopy-group map.

For an exact functor, the supplied Q-isomorphism is obtained from the canonical
zero-object isomorphism in the original exact category. No zero-object property
in the Q-category is used, and the definition of `ExactFunctor.KMap` is unchanged.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject unitInterval

universe u v

namespace Quillen

section Rebase

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- An equality of the endpoint does not change the parametrized categorical edge. -/
theorem classifyingSpacePath_comp_eqToHom_apply {a b d : D} (f : a ⟶ b)
    (h : b = d) (t : unitInterval) :
    classifyingSpacePath (f ≫ eqToHom h) t = classifyingSpacePath f t := by
  subst d
  simp only [eqToHom_refl, Category.comp_id]

/-- The supplied base-object isomorphism, as a path from the actual image point. -/
def classifyingSpaceIsoBasePath (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    Path (classifyingSpaceMap F (classifyingSpacePoint c)) (classifyingSpacePoint d) :=
  (classifyingSpacePath e.hom).cast (classifyingSpaceMap_point F c) rfl

/-- The original natural isomorphism supplies the homotopy to the rebased map. -/
def rebaseFunctorHomotopy (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    (classifyingSpaceMap F).hom.Homotopy
      (classifyingSpaceMap (rebaseFunctor F c d e)).hom :=
  classifyingSpaceNaturalTransformationHomotopy (rebaseFunctorIso F c d e).hom

/-- The whole rebasing track is the original supplied edge, including its parametrization. -/
theorem rebaseFunctorHomotopy_base_track (F : C ⥤ D) (c : C) (d : D)
    (e : F.obj c ≅ d) :
    ((rebaseFunctorHomotopy F c d e).evalAt (classifyingSpacePoint c)).cast rfl
      (rebaseFunctor_map_point F c d e).symm = classifyingSpaceIsoBasePath F c d e := by
  ext t
  change classifyingSpaceNaturalTransformationHomotopy (rebaseFunctorIso F c d e).hom
    (t, classifyingSpacePoint c) = classifyingSpacePath e.hom t
  rw [classifyingSpaceNaturalTransformationHomotopy_vertex_track,
    rebaseFunctorIso_hom_base]
  exact classifyingSpacePath_comp_eqToHom_apply e.hom _ t

/-- Moving the basepoint along the original rebasing track identifies the actual maps
in every finite homotopy degree, including degree zero. -/
theorem pathTransport_rebaseFunctor_homotopyGroupMap (F : C ⥤ D) (c : C) (d : D)
    (e : F.obj c ≅ d) (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace C) (classifyingSpacePoint c)) :
    pathTransport (classifyingSpaceIsoBasePath F c d e) n
      (homotopyGroupMap (classifyingSpaceMap F).hom rfl a) =
        homotopyGroupMap (classifyingSpaceMap (rebaseFunctor F c d e)).hom
          (rebaseFunctor_map_point F c d e) a := by
  rw [← rebaseFunctorHomotopy_base_track F c d e]
  exact pathTransport_homotopyGroupMap_homotopy_cast
    (rebaseFunctorHomotopy F c d e) (classifyingSpacePoint c) rfl
    (rebaseFunctor_map_point F c d e) n a

/-- The existing strictly pointed map is the original raw map corrected by the actual
supplied isomorphism edge. -/
theorem pointedShiftedHomotopyGroupMap_eq_pathTransport (F : C ⥤ D) (c : C) (d : D)
    (e : F.obj c ≅ d) (n : ℕ) :
    pointedShiftedHomotopyGroupMap F c d e n =
      (pathTransportMulEquiv (classifyingSpaceIsoBasePath F c d e) n).toMonoidHom.comp
        (piMap n (classifyingSpaceMap F).hom rfl) := by
  apply MonoidHom.ext
  intro a
  exact (pathTransport_rebaseFunctor_homotopyGroupMap F c d e (n + 1) a).symm

end Rebase

namespace ExactFunctor

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The raw Q-map's actual basepoint path, obtained from the zero isomorphism before
passing to Q. -/
def qZeroBasePath (F : ExactFunctor EC ED) :
    Path (classifyingSpaceMap F.mapQ EC.kBasepoint) ED.kBasepoint :=
  classifyingSpaceIsoBasePath F.mapQ
    (Q.of EC.deflation EC.inflation (0 : C)) (Q.of ED.deflation ED.inflation (0 : D))
    (ED.qIsoOfIso F.toFunctor.mapZeroObject)

/-- The canonical path is the actual Q-arrow edge, with no change in parametrization. -/
theorem qZeroBasePath_apply (F : ExactFunctor EC ED) (t : unitInterval) :
    F.qZeroBasePath t = classifyingSpacePath
      (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom t := rfl

/-- Any displayed original-category zero isomorphism gives the same actual path.
Uniqueness is used in the original exact category, before applying `qIsoOfIso`. -/
theorem qZeroBasePath_eq_of_zeroIso (F : ExactFunctor EC ED)
    (e : F.toFunctor.obj (0 : C) ≅ (0 : D)) :
    F.qZeroBasePath = classifyingSpaceIsoBasePath F.mapQ
      (Q.of EC.deflation EC.inflation (0 : C)) (Q.of ED.deflation ED.inflation (0 : D))
      (ED.qIsoOfIso e) := by
  have he : F.toFunctor.mapZeroObject = e := by
    apply Iso.ext
    apply Subsingleton.elim
  unfold qZeroBasePath
  rw [he]

/-- The raw Q-map and the normalized map are related by the original rebasing homotopy. -/
def normalizedQHomotopy (F : ExactFunctor EC ED) :
    (classifyingSpaceMap F.mapQ).hom.Homotopy (classifyingSpaceMap F.normalizedQ).hom :=
  rebaseFunctorHomotopy F.mapQ
    (Q.of EC.deflation EC.inflation (0 : C)) (Q.of ED.deflation ED.inflation (0 : D))
    (ED.qIsoOfIso F.toFunctor.mapZeroObject)

/-- Exact description of the basepoint track of the original Q-rebasing homotopy. -/
theorem normalizedQHomotopy_base_track (F : ExactFunctor EC ED) :
    ((F.normalizedQHomotopy).evalAt EC.kBasepoint).cast rfl
      (rebaseFunctor_map_point F.mapQ
        (Q.of EC.deflation EC.inflation (0 : C)) (Q.of ED.deflation ED.inflation (0 : D))
        (ED.qIsoOfIso F.toFunctor.mapZeroObject)).symm = F.qZeroBasePath :=
  rebaseFunctorHomotopy_base_track F.mapQ _ _ _

/-- The original K-map equals the original raw Q-map transported along its canonical
Q-isomorphism edge. This applies to every exact functor and every K-degree. -/
theorem KMap_eq_pathTransport (F : ExactFunctor EC ED) (n : ℕ) :
    F.KMap n =
      (pathTransportMulEquiv F.qZeroBasePath n).toMonoidHom.comp
        (piMap n (classifyingSpaceMap F.mapQ).hom rfl) :=
  pointedShiftedHomotopyGroupMap_eq_pathTransport F.mapQ _ _ _ n

end ExactFunctor

end Quillen

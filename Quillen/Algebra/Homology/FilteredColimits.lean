/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Homology and exact colimits of complexes

For an abelian category with exact colimits of shape `J`, the actual homology
functor preserves `J`-shaped colimits of complexes. The proof exchanges diagrams
with short complexes, uses exactness of the colimit functor, and checks the
original cocone maps. Evaluation of complexes then supplies the chain-level
result for any complex shape.

The resulting comparison is natural in diagrams and its inverse is definitionally
mathlib's canonical `colimit.post`. All universe parameters are independent;
existence and exactness are stated for the actual diagram shape.
-/

@[expose] public section

open CategoryTheory Limits CategoryTheory.Functor
noncomputable section
universe u v w w' t
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C]

namespace CategoryTheory.ShortComplex

/-- The homology diagram is the pointwise homology of the associated complex of functors. -/
def homologyDiagramIso (F : J ⥤ ShortComplex C) :
    F ⋙ homologyFunctor C ≅ ((functorEquivalence J C).inverse.obj F).homology := by
  let S := (functorEquivalence J C).inverse.obj F
  refine NatIso.ofComponents (fun j => S.mapHomologyIso ((evaluation J C).obj j)) ?_
  intro i j f
  change homologyMap (S.mapNatTrans ((evaluation J C).map f)) ≫ _ = _
  rw [homologyMap_mapNatTrans]
  simp [S]
  rfl


variable [HasExactColimitsOfShape J C]

/-- Exact colimits commute with short-complex homology through the original cocone maps. -/
theorem homologyFunctor_preservesColimit (F : J ⥤ ShortComplex C) :
    PreservesColimit F (homologyFunctor C) := by
  let S := (functorEquivalence J C).inverse.obj F
  let e := homologyDiagramIso F
  apply preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv e _).symm (colimit.isColimit S.homology))
    (Cocone.ext (S.mapHomologyIso colim).symm ?_)
  intro j
  dsimp only [Cocone.precompose_obj_ι, NatTrans.comp_app]
  rw [Category.assoc]
  change (S.mapHomologyIso ((evaluation J C).obj j)).hom ≫
    colimit.ι S.homology j ≫ (S.mapHomologyIso colim).inv = _
  exact (S.homologyMap_mapNatTrans (colim.ι j)).symm

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {ι : Type t} (c : ComplexShape ι) (n : ι)

/-- Forming the three-term complex at a degree preserves colimits, degree by degree. -/
theorem shortComplexFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J (shortComplexFunctor C c n) where
  preservesColimit := ⟨fun hs => ⟨ShortComplex.isColimitOfIsColimitπ _
    (isColimitOfPreserves (eval C c (c.prev n)) hs)
    (isColimitOfPreserves (eval C c n) hs)
    (isColimitOfPreserves (eval C c (c.next n)) hs)⟩⟩

variable [HasExactColimitsOfShape J C]

/-- In an abelian category, homology preserves any shape of exact colimits. -/
theorem homologyFunctor_preservesColimitsOfShape_of_exactColimits :
    PreservesColimitsOfShape J (homologyFunctor C c n) := by
  let : PreservesColimitsOfShape J (ShortComplex.homologyFunctor C) :=
    ⟨fun {F} => ShortComplex.homologyFunctor_preservesColimit F⟩
  let := shortComplexFunctor_preservesColimitsOfShape (C := C) (J := J) c n
  exact preservesColimitsOfShape_of_natIso (homologyFunctorIso C c n).symm


/-- The canonical isomorphism from homology of a colimit to colimit of homology. -/
def colimitHomologyIsoOfExactColimits (F : J ⥤ HomologicalComplex C c) :
    (colimit F).homology n ≅ colimit (F ⋙ homologyFunctor C c n) := by
  letI := homologyFunctor_preservesColimitsOfShape_of_exactColimits (C := C) (J := J) c n
  exact preservesColimitIso (homologyFunctor C c n) F

/-- The canonical comparison is natural in the entire diagram of complexes. -/
def colimitHomologyNatIsoOfExactColimits :
    (colim : (J ⥤ HomologicalComplex C c) ⥤ _) ⋙ homologyFunctor C c n ≅
      (whiskeringRight J _ _).obj (homologyFunctor C c n) ⋙ colim := by
  letI := homologyFunctor_preservesColimitsOfShape_of_exactColimits (C := C) (J := J) c n
  exact preservesColimitNatIso (homologyFunctor C c n)

/-- The inverse comparison uses the original homology maps of the colimit legs. -/
@[reassoc]
theorem colimitHomologyIsoOfExactColimits_ι_inv (F : J ⥤ HomologicalComplex C c) (j : J) :
    colimit.ι (F ⋙ homologyFunctor C c n) j ≫
      (colimitHomologyIsoOfExactColimits c n F).inv = homologyMap (colimit.ι F j) n := by
  let := homologyFunctor_preservesColimitsOfShape_of_exactColimits (C := C) (J := J) c n
  exact ι_preservesColimitIso_inv _ _ j

/-- The inverse is precisely mathlib's canonical colimit comparison morphism. -/
@[simp]
theorem colimitHomologyIsoOfExactColimits_inv (F : J ⥤ HomologicalComplex C c) :
    (colimitHomologyIsoOfExactColimits c n F).inv =
      colimit.post F (homologyFunctor C c n) := rfl

end HomologicalComplex

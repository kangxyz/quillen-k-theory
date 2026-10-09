import Quillen.Waldhausen.KTheory
import Quillen.Topology.HomotopyGroups.Map

/-!
# Exact functors and S-construction maps

An exact functor preserves zero objects, cofibrations, weak equivalences,
and pushouts along cofibrations. These structural conditions give the
simplicial map by postcomposition. The induced group map is constructed
from the realized continuous map, with an explicit basepoint equality.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe v u v' u' v'' u''

namespace Quillen.Waldhausen

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]

/-- The structural properties needed to map S-constructions. -/
structure IsExact (cof weq : MorphismProperty C) (cof' weq' : MorphismProperty D)
    (F : C ⥤ D) : Prop where
  /-- Zero objects are preserved. -/
  zero {Z : C} : IsZero Z → IsZero (F.obj Z)
  /-- Cofibrations are preserved. -/
  cofibration {X Y : C} (f : X ⟶ Y) : cof f → cof' (F.map f)
  /-- Weak equivalences are preserved. -/
  weak {X Y : C} (f : X ⟶ Y) : weq f → weq' (F.map f)
  /-- Pushouts along cofibrations are preserved. -/
  pushout {A B D P : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P} :
    cof i → IsPushout i f g j → IsPushout (F.map i) (F.map f) (F.map g) (F.map j)

namespace IsExact

/-- The identity functor is exact. -/
theorem id (cof weq : MorphismProperty C) : IsExact cof weq cof weq (𝟭 C) where
  zero h := h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h

/-- Exactness is stable under composition. -/
theorem comp {cof weq : MorphismProperty C} {cof' weq' : MorphismProperty D}
    {cof'' weq'' : MorphismProperty E} {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact cof weq cof' weq' F) (hG : IsExact cof' weq' cof'' weq'' G) :
    IsExact cof weq cof'' weq'' (F ⋙ G) where
  zero h := hG.zero (hF.zero h)
  cofibration f h := hG.cofibration _ (hF.cofibration f h)
  weak f h := hG.weak _ (hF.weak f h)
  pushout h hP := hG.pushout (hF.cofibration _ h) (hF.pushout h hP)

end IsExact

variable {cof weq : MorphismProperty C} {cof' weq' : MorphismProperty D}
    {F : C ⥤ D} (hF : IsExact cof weq cof' weq' F)

include hF in
/-- Exact functors take S-simplices to S-simplices. -/
theorem IsSimplex.postcomp {n : SimplexCategory} {A : Grid n ⥤ C}
    (hA : IsSimplex cof weq A) : IsSimplex cof' weq' (A ⋙ F) where
  zero t i := hF.zero (hA.zero t i)
  cofibration t i j k hij hjk := hF.cofibration _ (hA.cofibration t i j k hij hjk)
  quotient t i j k hij hjk := hF.pushout (hA.cofibration t i j k hij hjk)
    (hA.quotient t i j k hij hjk)
  weak s t i j hst hij := hF.weak _ (hA.weak s t i j hst hij)

section SameUniverses

variable {D : Type u} [Category.{v} D] {cof' weq' : MorphismProperty D}
    {F : C ⥤ D} (hF : IsExact cof weq cof' weq' F)

/-- The actual map of diagonal S-constructions. -/
def sSetMap : sSet cof weq ⟶ sSet cof' weq' where
  app _ := ↾fun A ↦ ⟨A.1 ⋙ F, A.2.postcomp hF⟩
  naturality _ _ _ := by ext A; rfl

/-- The map of actual geometric realizations. -/
def deloopingMap : delooping cof weq ⟶ delooping cof' weq' :=
  SSet.toTop.map (sSetMap hF)

variable [cof.ContainsIdentities] [weq.ContainsIdentities]
  [cof'.ContainsIdentities] [weq'.ContainsIdentities]

/-- A zero simplex is sent to the zero simplex of its image object. -/
@[simp]
theorem sSetMap_zeroSimplex (Z : C) (hZ : IsZero Z) (n : SimplexCategoryᵒᵖ) :
    (sSetMap hF).app n (zeroSimplex cof weq Z hZ n) =
      zeroSimplex cof' weq' (F.obj Z) (hF.zero hZ) n := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro x y f
  simp [sSetMap, zeroSimplex]

/-- Realization maps preserve the image basepoint. -/
@[simp]
theorem deloopingMap_basepoint (Z : C) (hZ : IsZero Z) :
    deloopingMap hF (basepoint cof weq Z hZ) =
      basepoint cof' weq' (F.obj Z) (hF.zero hZ) := by
  have h := SSet.yonedaEquiv_symm_comp (zeroSimplex cof weq Z hZ (op ⦋0⦌)) (sSetMap hF)
  have h' := congrArg (fun f : (Δ[0] : SSet.{max u v}) ⟶ sSet cof' weq' ↦
    SSet.toTop.map f default) h
  simpa only [Functor.map_comp, TopCat.comp_app, sSetMap_zeroSimplex,
    deloopingMap, basepoint, delooping] using h'

/-- The induced homomorphism on genuine homotopy groups, based at the image
zero object. No weak-equivalence/comparison theorem is assumed. -/
def groupsMap (Z : C) (hZ : IsZero Z) (n : ℕ) :
    groups cof weq Z hZ n →* groups cof' weq' (F.obj Z) (hF.zero hZ) n :=
  Quillen.piMap n (deloopingMap hF).hom (deloopingMap_basepoint hF Z hZ)

/-- A strict equality of chosen zero objects identifies the target basepoint. -/
def groupsMapOfZeroEq (Z : C) (hZ : IsZero Z) (Z' : D) (hZ' : IsZero Z')
    (h : F.obj Z = Z') (n : ℕ) :
    groups cof weq Z hZ n →* groups cof' weq' Z' hZ' n := by
  subst Z'
  exact groupsMap hF Z hZ n

end SameUniverses

end Quillen.Waldhausen

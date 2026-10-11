/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.TelescopeConeBoundary
public import Quillen.CategoryTheory.Limits.SequentialExactness

/-!
# Exact signed groups of the original telescope cone

The actual finite cone sequences form a sequential diagram. Filtered exactness transfers all
three recurring positions through the original source, target and cone colimit isomorphisms.
The telescope arrow, its cone inclusion and the exact stage-compatible boundary are unchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i) (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))

/-- Original stage cone inclusions form the corresponding map of actual stable diagrams. -/
def coneInclusionDiagramMap (d : ℤ) : stageStableDiagram F g d ⟶
    stageStableDiagram (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) d :=
  stageStableDiagramMap F g (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha)
    (fun i ↦ mappingConeInclusion (a i)) (by
      intro i
      apply Hom.ext
      funext k
      ext y
      rfl) d

variable [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((F i).space k)]

/-- The actual colimit of stage inclusions is the unchanged cone inclusion on the telescope. -/
@[reassoc] theorem coneInclusionDiagramMap_colimit (d : ℤ) :
    colimMap (coneInclusionDiagramMap E f F g a ha d) ≫
      (coneStableColimitIso E f F g a ha d).hom =
        (stableColimitIso F g d).hom ≫
          (stableHomotopyFunctor d).map (mappingConeInclusion (map E f F g a ha)) := by
  apply colimit.hom_ext
  intro i
  rw [ι_colimMap_assoc, coneStableColimitIso_ι_hom]
  change (stableHomotopyFunctor d).map (mappingConeInclusion (a i)) ≫
    (stableHomotopyFunctor d).map (coneStageMap E f F g a ha i) =
      colimit.ι (stageStableDiagram F g d) i ≫ stableColimitComparison F g d ≫ _
  rw [← Category.assoc, stableColimitComparison_ι, ← Functor.map_comp, ← Functor.map_comp]
  congr 1

private theorem exact_of_colimit_iso {A B C : ℕ ⥤ AddCommGrpCat.{u}}
    (α : A ⟶ B) (β : B ⟶ C) (h : ∀ i, Function.Exact (α.app i) (β.app i))
    {X Y Z : AddCommGrpCat.{u}} (x : colimit A ≅ X) (y : colimit B ≅ Y)
    (z : colimit C ≅ Z) (p : X ⟶ Y) (q : Y ⟶ Z)
    (hp : colimMap α ≫ y.hom = x.hom ≫ p) (hq : colimMap β ≫ z.hom = y.hom ≫ q) :
    Function.Exact p q := by
  exact (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    (colimMap α).hom (colimMap β).hom p.hom q.hom x.hom.hom y.hom.hom z.hom.hom
    (congrArg AddCommGrpCat.Hom.hom hp.symm) (congrArg AddCommGrpCat.Hom.hom hq.symm)
    (ConcreteCategory.bijective_of_isIso x.hom).surjective
    (ConcreteCategory.bijective_of_isIso y.hom)
    (ConcreteCategory.bijective_of_isIso z.hom).injective).mp
      (sequentialColimit_exact α β h)

variable (h : ∀ i, IsStableEquivalence (mappingConeFiberComparison (a i)))

include h in
/-- The unchanged telescope arrow and its original cone inclusion are exact on signed groups.
-/
theorem cone_stable_exact_target (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor d).map (map E f F g a ha))
      ((stableHomotopyFunctor d).map (mappingConeInclusion (map E f F g a ha))) :=
  exact_of_colimit_iso (stageStableDiagramMap E f F g a ha d)
    (coneInclusionDiagramMap E f F g a ha d)
    (fun i ↦ stableMappingCone_exact_target (a i) (h i) d)
    (stableColimitIso E f d) (stableColimitIso F g d) (coneStableColimitIso E f F g a ha d)
    _ _ (stableColimitIso_naturality E f F g a ha d)
    (coneInclusionDiagramMap_colimit E f F g a ha d)

/-- The colimit-defined original boundary is exact before the unchanged telescope arrow. -/
theorem coneStableConnecting_exact_source (d : ℤ) :
    Function.Exact (coneStableConnecting E f F g a ha h d)
      ((stableHomotopyFunctor d).map (map E f F g a ha)) := by
  apply exact_of_colimit_iso (coneBoundaryDiagramMap E f F g a ha h d)
    (stageStableDiagramMap E f F g a ha d)
    (fun i ↦ stableMappingConeConnecting_exact_source (a i) (h i) d)
    (coneStableColimitIso E f F g a ha (d + 1)) (stableColimitIso E f d)
    (stableColimitIso F g d)
  · simp only [coneStableConnecting, Iso.hom_inv_id_assoc]
  · exact stableColimitIso_naturality E f F g a ha d

/-- The original cone inclusion is exact before the signed boundary on the unchanged cone. -/
theorem coneStableConnecting_exact_cone (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map
      (mappingConeInclusion (map E f F g a ha))) (coneStableConnecting E f F g a ha h d) := by
  apply exact_of_colimit_iso (coneInclusionDiagramMap E f F g a ha (d + 1))
    (coneBoundaryDiagramMap E f F g a ha h d)
    (fun i ↦ stableMappingConeConnecting_exact_cone (a i) (h i) d)
    (stableColimitIso F g (d + 1)) (coneStableColimitIso E f F g a ha (d + 1))
    (stableColimitIso E f d)
  · exact coneInclusionDiagramMap_colimit E f F g a ha (d + 1)
  · simp only [coneStableConnecting, Iso.hom_inv_id_assoc]

end Quillen.LoopPrespectrum.Telescope

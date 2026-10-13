/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ModuleScalars
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.RankOneGluing
public import Quillen.CategoryTheory.Limits.SplitColumnCokernel

/-!
# Graph columns for arbitrary module sheaves

Original graph and cograph columns into the restricted module square have reciprocal scalar
transition on the actual overlap. Their naturality and unit specialization retain the original
inclusions.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SchemeSheaf
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (M : X.Modules) (s : Γ(U, ⊤))

/-- The graph column (1,s) into the actual restricted module square. -/
def moduleFirstColumn : M.restrict j ⟶ (M ⨯ M).restrict j := by
  let := restrict_prodComparison_isIso j M M
  exact graphColumn (moduleMul (M.restrict j) s) ≫
    inv (prodComparison (Scheme.Modules.restrictFunctor j) M M)

/-- The cograph column (s,1) into the actual restricted module square. -/
def moduleSecondColumn : M.restrict j ⟶ (M ⨯ M).restrict j := by
  let := restrict_prodComparison_isIso j M M
  exact cographColumn (moduleMul (M.restrict j) s) ≫
    inv (prodComparison (Scheme.Modules.restrictFunctor j) M M)

lemma moduleFirstColumn_fst :
    moduleFirstColumn j M s ≫ (Scheme.Modules.restrictFunctor j).map prod.fst = 𝟙 _ := by
  let := restrict_prodComparison_isIso j M M
  simp [moduleFirstColumn, graphColumn, Category.assoc, inv_prodComparison_map_fst]

lemma moduleFirstColumn_snd :
    moduleFirstColumn j M s ≫ (Scheme.Modules.restrictFunctor j).map prod.snd =
      moduleMul (M.restrict j) s := by
  let := restrict_prodComparison_isIso j M M
  simp [moduleFirstColumn, graphColumn, Category.assoc, inv_prodComparison_map_snd]

lemma moduleSecondColumn_fst :
    moduleSecondColumn j M s ≫ (Scheme.Modules.restrictFunctor j).map prod.fst =
      moduleMul (M.restrict j) s := by
  let := restrict_prodComparison_isIso j M M
  simp [moduleSecondColumn, cographColumn, Category.assoc, inv_prodComparison_map_fst]

lemma moduleSecondColumn_snd :
    moduleSecondColumn j M s ≫ (Scheme.Modules.restrictFunctor j).map prod.snd = 𝟙 _ := by
  let := restrict_prodComparison_isIso j M M
  simp [moduleSecondColumn, cographColumn, Category.assoc, inv_prodComparison_map_snd]

instance moduleFirstColumn_mono : Mono (moduleFirstColumn j M s) := by
  have : Mono (moduleFirstColumn j M s ≫ (Scheme.Modules.restrictFunctor j).map prod.fst) := by
    rw [moduleFirstColumn_fst]
    infer_instance
  exact mono_of_mono (moduleFirstColumn j M s)
    ((Scheme.Modules.restrictFunctor j).map prod.fst)

instance moduleSecondColumn_mono : Mono (moduleSecondColumn j M s) := by
  have : Mono (moduleSecondColumn j M s ≫ (Scheme.Modules.restrictFunctor j).map prod.snd) := by
    rw [moduleSecondColumn_snd]
    infer_instance
  exact mono_of_mono (moduleSecondColumn j M s)
    ((Scheme.Modules.restrictFunctor j).map prod.snd)

/-- Scalar multiplication followed by the original overlap restriction comparison. -/
def moduleColumnTransition {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : X.Modules)
    (v : (Γ(pullback j k, ⊤))ˣ) :
    (M.restrict j).restrict (pullback.fst j k) ≅
      (M.restrict k).restrict (pullback.snd j k) :=
  moduleMulIso _ v ≪≫ (Quillen.CoherentScheme.overlapRestrictIso j k).app M

lemma moduleColumns_compatible {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] (M : X.Modules)
    (s : Γ(U, ⊤)) (t : Γ(V, ⊤)) (v : (Γ(pullback j k, ⊤))ˣ)
    (hs : (pullback.fst j k).appTop.hom s = ↑v)
    (ht : (pullback.snd j k).appTop.hom t = ↑v⁻¹) :
    (Scheme.Modules.restrictFunctor (pullback.fst j k)).map (moduleFirstColumn j M s) ≫
        (Quillen.CoherentScheme.overlapRestrictIso j k).hom.app (M ⨯ M) =
      (moduleColumnTransition j k M v).hom ≫
        (Scheme.Modules.restrictFunctor (pullback.snd j k)).map (moduleSecondColumn k M t) := by
  apply (isLimitOfPreserves
    (Scheme.Modules.restrictFunctor k ⋙ Scheme.Modules.restrictFunctor (pullback.snd j k))
    (prodIsProd M M)).hom_ext
  rintro (_ | _)
  · change (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
        ((Scheme.Modules.restrictFunctor k).map prod.fst) = (_ ≫ _) ≫
        (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
          ((Scheme.Modules.restrictFunctor k).map prod.fst)
    have hn := (Quillen.CoherentScheme.overlapRestrictIso j k).hom.naturality
      (show M ⨯ M ⟶ M from prod.fst)
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp,
      moduleFirstColumn_fst, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [Category.assoc, ← Functor.map_comp, moduleSecondColumn_fst, moduleMul_restrict]
    simp only [moduleColumnTransition, Iso.trans_hom, moduleMulIso, Iso.app_hom, Category.assoc]
    rw [← moduleMul_naturality, ← Category.assoc, ← moduleMul_mul, ht]
    simp only [Units.mul_inv, moduleMul_one, Category.id_comp]
  · change (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
        ((Scheme.Modules.restrictFunctor k).map prod.snd) = (_ ≫ _) ≫
        (Scheme.Modules.restrictFunctor (pullback.snd j k)).map
          ((Scheme.Modules.restrictFunctor k).map prod.snd)
    have hn := (Quillen.CoherentScheme.overlapRestrictIso j k).hom.naturality
      (show M ⨯ M ⟶ M from prod.snd)
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp,
      moduleFirstColumn_snd, moduleMul_restrict, hs]
    rw [Category.assoc, ← Functor.map_comp, moduleSecondColumn_snd,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rfl

lemma moduleFirstColumn_naturality {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N) (s : Γ(U, ⊤)) :
    (Scheme.Modules.restrictFunctor j).map f ≫ moduleFirstColumn j N s =
      moduleFirstColumn j M s ≫ (Scheme.Modules.restrictFunctor j).map (prod.map f f) := by
  apply (isLimitOfPreserves (Scheme.Modules.restrictFunctor j) (prodIsProd N N)).hom_ext
  rintro (_ | _)
  · change (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.fst =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.fst
    rw [Category.assoc, moduleFirstColumn_fst, Category.comp_id,
      Category.assoc, ← Functor.map_comp, prod.map_fst, Functor.map_comp,
      ← Category.assoc, moduleFirstColumn_fst, Category.id_comp]
  · change (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.snd =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.snd
    rw [Category.assoc, moduleFirstColumn_snd, Category.assoc, ← Functor.map_comp,
      prod.map_snd, Functor.map_comp, ← Category.assoc, moduleFirstColumn_snd]
    exact (moduleMul_naturality ((Scheme.Modules.restrictFunctor j).map f) s).symm

lemma moduleSecondColumn_naturality {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N) (s : Γ(U, ⊤)) :
    (Scheme.Modules.restrictFunctor j).map f ≫ moduleSecondColumn j N s =
      moduleSecondColumn j M s ≫ (Scheme.Modules.restrictFunctor j).map (prod.map f f) := by
  apply (isLimitOfPreserves (Scheme.Modules.restrictFunctor j) (prodIsProd N N)).hom_ext
  rintro (_ | _)
  · change (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.fst =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.fst
    rw [Category.assoc, moduleSecondColumn_fst, Category.assoc, ← Functor.map_comp,
      prod.map_fst, Functor.map_comp, ← Category.assoc, moduleSecondColumn_fst]
    exact (moduleMul_naturality ((Scheme.Modules.restrictFunctor j).map f) s).symm
  · change (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.snd =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.snd
    rw [Category.assoc, moduleSecondColumn_snd, Category.comp_id,
      Category.assoc, ← Functor.map_comp, prod.map_snd, Functor.map_comp,
      ← Category.assoc, moduleSecondColumn_snd, Category.id_comp]

end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (s : Γ(U, ⊤))

lemma moduleFirstColumn_unit :
    moduleFirstColumn j (SheafOfModules.unit X.ringCatSheaf) s =
      (Scheme.Modules.restrictUnitIso j).hom ≫ firstColumn j s := by
  apply (isLimitOfPreserves (Scheme.Modules.restrictFunctor j)
    (prodIsProd (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf))).hom_ext
  rintro (_ | _)
  · change _ ≫ (Scheme.Modules.restrictFunctor j).map prod.fst =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.fst
    rw [moduleFirstColumn_fst, Category.assoc, firstColumn_fst, Iso.hom_inv_id]
  · change _ ≫ (Scheme.Modules.restrictFunctor j).map prod.snd =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.snd
    rw [moduleFirstColumn_snd, Category.assoc, firstColumn_snd]
    rw [← moduleMul_unit, ← Category.assoc, ← moduleMul_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

lemma moduleSecondColumn_unit :
    moduleSecondColumn j (SheafOfModules.unit X.ringCatSheaf) s =
      (Scheme.Modules.restrictUnitIso j).hom ≫ secondColumn j s := by
  apply (isLimitOfPreserves (Scheme.Modules.restrictFunctor j)
    (prodIsProd (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf))).hom_ext
  rintro (_ | _)
  · change _ ≫ (Scheme.Modules.restrictFunctor j).map prod.fst =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.fst
    rw [moduleSecondColumn_fst, Category.assoc, secondColumn_fst]
    rw [← moduleMul_unit, ← Category.assoc, ← moduleMul_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · change _ ≫ (Scheme.Modules.restrictFunctor j).map prod.snd =
      (_ ≫ _) ≫ (Scheme.Modules.restrictFunctor j).map prod.snd
    rw [moduleSecondColumn_snd, Category.assoc, secondColumn_snd, Iso.hom_inv_id]
end Quillen.SchemeSheaf

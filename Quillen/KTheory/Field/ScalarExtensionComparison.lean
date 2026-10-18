/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Field.FiniteModuleRingEquivalence
public import Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal
public import Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExact
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Actual scalar extension and finite right projectives over fields

The finite-module functor is the restriction of `ModuleCat.extendScalars`.
The comparison with the original matrix-image base change uses its proved
universal property, the actual opposite-ring restriction equivalences and the
tensor-extension adjunction.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Field

variable {F L : Type u} [Field F] [Field L] (f : F →+* L)

/-- Literal tensor extension restricted to the existing finite-module categories. -/
def finiteModuleExtension : FGModuleCat.{u} F ⥤ FGModuleCat.{u} L :=
  ObjectProperty.lift _ ((ModuleCat.finiteModule F).ι ⋙ ModuleCat.extendScalars f)
    (fun M => by
      let := f.toAlgebra
      change Module.Finite L (L ⊗[F] M.obj)
      infer_instance)

instance finiteModuleExtension_additive : (finiteModuleExtension f).Additive where
  map_add := by
    intro X Y a b
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (ModuleCat.extendScalars f)
    let := Functor.additive_of_preservesBinaryBiproducts (ModuleCat.extendScalars f)
    apply FGModuleCat.hom_ext
    exact congrArg ModuleCat.Hom.hom
      (Functor.map_add (ModuleCat.extendScalars f) (f := a.hom) (g := b.hom))

instance finiteModuleExtension_preservesFiniteLimits :
    PreservesFiniteLimits (finiteModuleExtension f) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.Flat.of_isField (Field.toIsField F) f)
  have : PreservesFiniteLimits
      (finiteModuleExtension f ⋙ (ModuleCat.finiteModule L).ι) := by
    change PreservesFiniteLimits
      (forget₂ (FGModuleCat F) (ModuleCat F) ⋙ ModuleCat.extendScalars f)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (finiteModuleExtension f)
    (ModuleCat.finiteModule L).ι

instance finiteModuleExtension_preservesFiniteColimits :
    PreservesFiniteColimits (finiteModuleExtension f) := by
  have : PreservesFiniteColimits
      (finiteModuleExtension f ⋙ (ModuleCat.finiteModule L).ι) := by
    change PreservesFiniteColimits
      (forget₂ (FGModuleCat F) (ModuleCat F) ⋙ ModuleCat.extendScalars f)
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (finiteModuleExtension f)
    (ModuleCat.finiteModule L).ι

/-- Exactness of the same literal tensor-extension functor over fields. -/
def finiteModuleExtensionExact : ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} F)
    (ModuleCat.finiteModuleExactStructure.{u, u} L) where
  toFunctor := finiteModuleExtension f
  map_conflation _ h := h.map_of_exact _

/-- The actual inclusion and opposite-ring scalar restriction, before SmallModel transport. -/
def rightProjectiveToModuleExact (F : Type u) [Field F] :
    ExactFunctor (FiniteProjectiveModule.exactStructure Fᵐᵒᵖ)
      (ModuleCat.finiteModuleExactStructure.{u, u} F) :=
  (FiniteProjectiveModule.toFiniteModuleExact Fᵐᵒᵖ).comp
    (finiteModuleRingExact (RingEquiv.toOpposite F))

/-- The same Hom bijection for the actual right-module base change and literal tensor extension. -/
def extensionComparisonHomEquiv
    (P : FiniteProjectiveModule.Category.{u, u} Fᵐᵒᵖ) (N : ModuleCat.{u} L) :
    (((rightProjectiveToModuleExact L).toFunctor.obj
      ((FiniteProjectiveModule.rightBaseChange f).obj P)).obj ⟶ N) ≃
    ((ModuleCat.extendScalars f).obj
      ((rightProjectiveToModuleExact F).toFunctor.obj P).obj ⟶ N) := by
  let eF := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.toOpposite F)
  let eL := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.toOpposite L)
  exact (eL.toAdjunction.homEquiv _ N).trans
    ((FiniteProjectiveModule.rightBaseChangeModuleHomEquiv f P (eL.inverse.obj N)).toEquiv.trans
      ((eF.toAdjunction.homEquiv P.obj ((ModuleCat.restrictScalars f).obj N)).symm.trans
        ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ N).symm))

section Comparison

variable (P : FiniteProjectiveModule.Category.{u, u} Fᵐᵒᵖ)

/-- The native base-change module after the actual opposite-ring restriction. -/
abbrev baseChangedModule := ((rightProjectiveToModuleExact L).toFunctor.obj
  ((FiniteProjectiveModule.rightBaseChange f).obj P)).obj
/-- The literal left tensor extension of the same original right module. -/
abbrev tensorExtendedModule := (ModuleCat.extendScalars f).obj
  ((rightProjectiveToModuleExact F).toFunctor.obj P).obj

local notation "A" => baseChangedModule f P
local notation "B" => tensorExtendedModule f P

/-- The universal comparison preserves the original semilinear base-change unit. -/
theorem extensionComparisonHomEquiv_unit (N : ModuleCat.{u} L) (h : A ⟶ N) (x : P.obj) :
    extensionComparisonHomEquiv f P N h ((1 : L) ⊗ₜ[F,f] x) =
      h (FiniteProjectiveModule.rightBaseChangeUnit f P x) := by
  change (1 : L) • h (FiniteProjectiveModule.rightBaseChangeUnit f P x) = _
  exact one_smul L _

/-- The Hom comparison is covariantly natural in its arbitrary target module. -/
theorem extensionComparisonHomEquiv_naturality
    {N N' : ModuleCat.{u} L} (h : A ⟶ N) (k : N ⟶ N') :
    extensionComparisonHomEquiv f P N' (h ≫ k) =
      extensionComparisonHomEquiv f P N h ≫ k := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact (extensionComparisonHomEquiv_unit f P N' (h ≫ k) x).trans
    (congrArg k (extensionComparisonHomEquiv_unit f P N h x).symm)

/-- The unique comparison between literal tensor extension and native matrix-image base change. -/
def extensionComparisonIso : B ≅ A where
  hom := extensionComparisonHomEquiv f P A (𝟙 A)
  inv := (extensionComparisonHomEquiv f P B).symm (𝟙 B)
  hom_inv_id := by
    have h := extensionComparisonHomEquiv_naturality f P (𝟙 A)
      ((extensionComparisonHomEquiv f P B).symm (𝟙 B))
    simpa only [Category.id_comp, Equiv.apply_symm_apply] using h.symm
  inv_hom_id := by
    apply (extensionComparisonHomEquiv f P A).injective
    rw [extensionComparisonHomEquiv_naturality, Equiv.apply_symm_apply, Category.id_comp]

/-- The concrete comparison sends the tensor unit to the original matrix-image unit. -/
theorem extensionComparisonIso_unit (x : P.obj) :
    (extensionComparisonIso f P).hom ((1 : L) ⊗ₜ[F,f] x) =
      FiniteProjectiveModule.rightBaseChangeUnit f P x :=
  extensionComparisonHomEquiv_unit f P A (𝟙 A) x

end Comparison

/-- Scalar extension and the actual right-to-left inclusion commute by the canonical unit. -/
def rightProjectiveExtensionIso :
    (rightProjectiveToModuleExact F).toFunctor ⋙ finiteModuleExtension f ≅
      FiniteProjectiveModule.rightBaseChange f ⋙ (rightProjectiveToModuleExact L).toFunctor :=
  NatIso.ofComponents (fun P => (ModuleCat.finiteModule L).isoMk (extensionComparisonIso f P))
    (by
      intro P Q g
      apply ObjectProperty.hom_ext
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change (extensionComparisonIso f Q).hom
        ((ModuleCat.extendScalars f).map
          ((rightProjectiveToModuleExact F).toFunctor.map g).hom ((1 : L) ⊗ₜ[F,f] x)) =
        ((FiniteProjectiveModule.rightBaseChange f).map g).hom
          ((extensionComparisonIso f P).hom ((1 : L) ⊗ₜ[F,f] x))
      erw [ModuleCat.ExtendScalars.map_tmul, extensionComparisonIso_unit,
        extensionComparisonIso_unit]
      exact (DFunLike.congr_fun (FiniteProjectiveModule.rightBaseChangeUnit_naturality f g)
        x).symm)

/-- The actual original exact-functor K-maps commute with literal tensor extension. -/
theorem rightProjectiveToModuleKMap_baseChange (n : ℕ) :
    ((rightProjectiveToModuleExact L).KMap n).comp
        ((FiniteProjectiveModule.rightBaseChangeExact f).KMap n) =
      ((finiteModuleExtensionExact f).KMap n).comp
        ((rightProjectiveToModuleExact F).KMap n) := by
  rw [← ExactFunctor.KMap_comp, ← ExactFunctor.KMap_comp]
  exact ExactFunctor.KMap_eq_of_natIso (rightProjectiveExtensionIso f).symm n


/-- The same actual scalar-extension square on the client's upper finite-module group. -/
theorem rightProjectiveUpperModuleKEquiv_baseChange (n : ℕ)
    (a : (FiniteProjectiveModule.exactStructure Fᵐᵒᵖ).K n) :
    rightProjectiveUpperModuleKEquiv L n
        ((FiniteProjectiveModule.rightBaseChangeExact f).KMap n a) =
      (finiteModuleExtensionExact f).smallKMap.{u+1} n
        (rightProjectiveUpperModuleKEquiv F n a) := by
  let EF := ModuleCat.finiteModuleExactStructure.{u, u} F
  let EL := ModuleCat.finiteModuleExactStructure.{u, u} L
  apply (EL.smallModelToOriginal.{u+1}.commonAmbientKEquiv n).injective
  change EL.smallModelToOriginal.{u+1}.commonAmbientKMap n
      (rightProjectiveUpperModuleKEquiv L n
        ((FiniteProjectiveModule.rightBaseChangeExact f).KMap n a)) =
    EL.smallModelToOriginal.{u+1}.commonAmbientKMap n
      ((finiteModuleExtensionExact f).smallKMap.{u+1} n
        (rightProjectiveUpperModuleKEquiv F n a))
  calc
    _ = (finiteModuleRingExact (RingEquiv.toOpposite L)).KMap n
        ((FiniteProjectiveModule.toFiniteModuleExact.{u, u} Lᵐᵒᵖ).KMap n
          ((FiniteProjectiveModule.rightBaseChangeExact f).KMap n a)) :=
      rightProjectiveUpperModuleKEquiv_toOriginal L n _
    _ = (finiteModuleExtensionExact f).KMap n
        ((finiteModuleRingExact (RingEquiv.toOpposite F)).KMap n
          ((FiniteProjectiveModule.toFiniteModuleExact.{u, u} Fᵐᵒᵖ).KMap n a)) := by
      simpa only [rightProjectiveToModuleExact, ExactFunctor.KMap_comp,
        MonoidHom.comp_apply] using
        DFunLike.congr_fun (rightProjectiveToModuleKMap_baseChange f n) a
    _ = (finiteModuleExtensionExact f).KMap n
        (EF.smallModelToOriginal.{u+1}.commonAmbientKMap n
          (rightProjectiveUpperModuleKEquiv F n a)) :=
      congrArg ((finiteModuleExtensionExact f).KMap n)
        (rightProjectiveUpperModuleKEquiv_toOriginal F n a).symm
    _ = _ := (DFunLike.congr_fun
      ((finiteModuleExtensionExact f).smallModelToOriginal_commonAmbientKMap_naturality.{u+1, u} n)
        (rightProjectiveUpperModuleKEquiv F n a)).symm

/-- Homomorphism form of scalar-extension naturality after the actual SmallModel transport. -/
theorem rightProjectiveUpperModuleKEquiv_baseChange_hom (n : ℕ) :
    (rightProjectiveUpperModuleKEquiv L n).toMonoidHom.comp
        ((FiniteProjectiveModule.rightBaseChangeExact f).KMap n) =
      ((finiteModuleExtensionExact f).smallKMap.{u+1} n).comp
        (rightProjectiveUpperModuleKEquiv F n).toMonoidHom := by
  ext a
  exact rightProjectiveUpperModuleKEquiv_baseChange f n a

end Quillen.Field

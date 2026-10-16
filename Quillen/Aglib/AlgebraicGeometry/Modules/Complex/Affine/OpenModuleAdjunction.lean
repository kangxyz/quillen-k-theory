/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.InjectivePushforwardAdjunction
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.Affine.OpenPushforwardCounit
public import Quillen.Aglib.AlgebraicGeometry.Cohomology.Affine.InjectiveResolution
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

/-!
# The original module adjunction over an affine open

The actual associated-sheaf, restriction, direct-image and sections adjunctions
are composed on chain complexes. The original counit and chain transpose retain
their literal factorization and homotopy formulas. For a lower-bounded injective
complex with quasicoherent homology on a quasi-compact affine open, that counit
is a quasi-isomorphism. No quasicoherence of the injective terms is required.

These statements apply to a global module target and its associated sheaf.
They do not assert exactness of ordinary direct image on arbitrary sheaf
complexes or a module model for an arbitrary non-quasicoherent target.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- The genuine tilde--global-sections adjunction on actual complexes. -/
def associatedSectionsComplexAdjunction (R : CommRingCat.{u}) :
    associatedComplex R ⊣ sectionsComplex R :=
  (tilde.adjunction (R := R)).mapHomologicalComplex (.up ℤ)

lemma associatedSectionsComplexAdjunction_counit (R : CommRingCat.{u})
    (J : CochainComplex (Spec R).Modules ℤ) :
    (associatedSectionsComplexAdjunction R).counit.app J = associatedSectionsCounit R J := by
  ext n : 1
  rfl

variable (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Original chain adjunction for associated modules restricted to the chosen open. -/
def openModuleComplexAdjunction :
    associatedComplex R ⋙ restrict j ⊣ pushforwardComplex j ⋙ sectionsComplex R :=
  (associatedSectionsComplexAdjunction R).comp (restrictPushforwardComplexAdjunction j)

/-- The actual composite counit, without any derived-model replacement. -/
def openModuleComplexCounit (I : CochainComplex U.Modules ℤ) :
    (restrict j).obj ((associatedComplex R).obj ((sectionsComplex R).obj
      ((pushforwardComplex j).obj I))) ⟶ I :=
  (restrict j).map (associatedSectionsCounit R ((pushforwardComplex j).obj I)) ≫
    (pushforwardComplexRestrictIso j).hom.app I

lemma openModuleComplexAdjunction_counit (I : CochainComplex U.Modules ℤ) :
    (openModuleComplexAdjunction R j).counit.app I = openModuleComplexCounit R j I := by
  rw [openModuleComplexAdjunction, Adjunction.comp_counit_app,
    associatedSectionsComplexAdjunction_counit, restrictPushforwardComplexAdjunction_counit]
  rfl

/-- The genuine module transpose of the original open chain map. -/
def openModuleChainAdjoint {P : ModuleComplex R} {I : CochainComplex U.Modules ℤ}
    (q : (restrict j).obj ((associatedComplex R).obj P) ⟶ I) :
    P ⟶ (sectionsComplex R).obj ((pushforwardComplex j).obj I) :=
  (openModuleComplexAdjunction R j).homEquiv P I q

@[reassoc]
lemma openModuleChainAdjoint_counit {P : ModuleComplex R} {I : CochainComplex U.Modules ℤ}
    (q : (restrict j).obj ((associatedComplex R).obj P) ⟶ I) :
    (restrict j).map ((associatedComplex R).map (openModuleChainAdjoint R j q)) ≫
      openModuleComplexCounit R j I = q := by
  rw [← openModuleComplexAdjunction_counit]
  exact ((openModuleComplexAdjunction R j).homEquiv P I).symm_apply_apply q

lemma quasiIso_openModuleComplexCounit (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (I : CochainComplex W.toScheme.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) :
    QuasiIso (openModuleComplexCounit R W.ι I) := by
  have := quasiIso_openPushforward_associatedSectionsCounit W hW I a hbound hinj hqc
  dsimp [openModuleComplexCounit]
  infer_instance

/-- The actual module unit induced by a local injective-resolution arrow is
weak after the original associated-sheaf restriction. -/
lemma quasiIso_restrict_associated_openModuleChainAdjoint (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) {B : ModuleComplex R}
      {I : CochainComplex W.toScheme.Modules ℤ}
    (a : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent)
    (q : (restrict W.ι).obj ((associatedComplex R).obj B) ⟶ I) [QuasiIso q] :
    QuasiIso ((restrict W.ι).map ((associatedComplex R).map (openModuleChainAdjoint R W.ι q))) := by
  have := quasiIso_openModuleComplexCounit R W hW I a hbound hinj hqc
  rw [← quasiIso_iff_comp_right _ (openModuleComplexCounit R W.ι I), openModuleChainAdjoint_counit]
  infer_instance

/-- Every original open derived arrow into the chosen injective model has an
actual module chain transpose with the exact original counit equation. -/
lemma exists_openModuleChainAdjoint (P : ModuleComplex R) (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (α : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj ((associatedComplex R).obj P)) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj I) :
    ∃ f : P ⟶ (sectionsComplex R).obj ((pushforwardComplex j).obj I),
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map ((associatedComplex R).map f)) ≫
        (DerivedCategory.Q (C := U.Modules)).map (openModuleComplexCounit R j I) = α := by
  have := isKInjective_of_lowerBounded_injective I a hbound hinj
  obtain ⟨q, hq⟩ := _root_.CochainComplex.exists_chain_representative_of_isKInjective α
  refine ⟨openModuleChainAdjoint R j q, ?_⟩
  rw [← (DerivedCategory.Q (C := U.Modules)).map_comp, openModuleChainAdjoint_counit]
  exact hq

/-- The actual open/module transpose preserves an original chain homotopy. -/
def openModuleChainAdjointHomotopy {P : ModuleComplex R} {I : CochainComplex U.Modules ℤ}
    {f g : (restrict j).obj ((associatedComplex R).obj P) ⟶ I} (H : Homotopy f g) :
    Homotopy (openModuleChainAdjoint R j f) (openModuleChainAdjoint R j g) := by
  simp only [openModuleChainAdjoint, Adjunction.homEquiv_unit]
  exact ((Scheme.Modules.pushforward j ⋙ moduleSpecΓFunctor).mapHomotopy H).compLeft
    ((openModuleComplexAdjunction R j).unit.app P)

@[reassoc]
lemma openModuleChainAdjoint_precomp {P B : ModuleComplex R} {I : CochainComplex U.Modules ℤ}
    (f : P ⟶ B) (q : (restrict j).obj ((associatedComplex R).obj B) ⟶ I) :
    openModuleChainAdjoint R j ((restrict j).map ((associatedComplex R).map f) ≫ q) =
      f ≫ openModuleChainAdjoint R j q :=
  (openModuleComplexAdjunction R j).homEquiv_naturality_left f q

/-- An original open derived equality becomes an actual module homotopy after
the same genuine transpose of the target's injective-resolution arrow. -/
def openModuleChainAdjointCompHomotopyOfDerivedEq
    {P B : ModuleComplex R} (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (q : (restrict j).obj ((associatedComplex R).obj B) ⟶ I) (f g : P ⟶ B)
    (hfg : (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map ((associatedComplex R).map f))
      =
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map ((associatedComplex R).map g))) :
    Homotopy (f ≫ openModuleChainAdjoint R j q) (g ≫ openModuleChainAdjoint R j q) := by
  have := isKInjective_of_lowerBounded_injective I a hbound hinj
  let H := _root_.CochainComplex.homotopyOfDerivedEqOfIsKInjective
    ((restrict j).map ((associatedComplex R).map f) ≫ q)
    ((restrict j).map ((associatedComplex R).map g) ≫ q) (by
      rw [(DerivedCategory.Q (C := U.Modules)).map_comp,
        (DerivedCategory.Q (C := U.Modules)).map_comp, hfg])
  rw [← openModuleChainAdjoint_precomp, ← openModuleChainAdjoint_precomp]
  exact openModuleChainAdjointHomotopy R j H

end Quillen.PerfectComplexes.Affine

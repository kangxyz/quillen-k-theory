/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.Basic
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Basic

/-!
# Finite presentations of affine coherent sheaves

A finite module over a noetherian ring has finitely many generators and
relations. Applying the actual tilde functor gives a finite presentation of
its sheaf. Consequently every object of the affine coherent category is a
finitely presented sheaf in the existing sheaf-theoretic sense.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- A finite module over a noetherian ring gives a genuinely finitely presented
sheaf on its spectrum. -/
theorem finitePresentation_tilde (M : ModuleCat.{u} R) [Module.Finite R M] :
    (tilde M).IsFinitePresentation := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := R) (M := M))
  let f : ((s : Set M) →₀ R) →ₗ[R] M := Finsupp.linearCombination R (fun x : (s : Set M) => x.1)
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (LinearMap.ker f)
  let P := presentationTilde M (s : Set M) hs (t : Set ((s : Set M) →₀ R)) ht
  have : P.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set M))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set ((s : Set M) →₀ R)))⟩ }
  exact SchemeSheaf.finitePresentation_of_presentation P

/-- Affine coherent sheaves satisfy the local finite-presentation predicate;
this is a proved comparison, rather than a renaming of unrelated categories. -/
theorem affineCoherent_finitePresentation (M : AffineFiniteType R) :
    ((affineFiniteTypeToModules R).obj M).IsFinitePresentation := by
  let N := (affineFiniteTypeToModules R).obj M
  have : N.IsQuasicoherent := M.obj.property
  have : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
    (asIso N.fromTildeΓ) (finitePresentation_tilde R (moduleSpecΓFunctor.obj N))

/-- The inclusion of affine coherent sheaves into the actual full subcategory
of finitely presented sheaves. -/
def affineCoherentToFinitePresentation :
    AffineFiniteType R ⥤ SchemeSheaf.FinitePresentation (Spec R) :=
  (SchemeSheaf.finitePresentation (Spec R)).lift (affineFiniteTypeToModules R)
    (affineCoherent_finitePresentation R)

end Quillen.CoherentScheme

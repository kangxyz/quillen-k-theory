/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomNegativeColumn

/-! Original precomposed binary rows are determined by their full reference endpoint.
This lemma requires the actual row normal form; functor endpoints alone do not suffice. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
variable {V : Model.{u + 1}} {X Y Z : Scheme.{u}}
  (F : V ⟶ modelOf (boundedFlatPerfectWaldhausen X))
  (P : V ⟶ modelOf (boundedFlatPerfectWaldhausen Z))
  (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The original binary nodes and both original reference transformations after precomposition. -/
def preBinaryNodes
    (ρ : F.functor ≅ (P ≫ BinaryNormalizationSimplex.sourceMap f g).functor) (i : Fin 3) :
    Σ G : V ⟶ modelOf (boundedFlatPerfectWaldhausen X), F.functor ≅ G.functor :=
  ⟨P ≫ (binaryNodes f g i).1, ρ ≪≫ isoWhiskerLeft P.functor (binaryNodes f g i).2⟩

variable {F P f g}
variable {ρ σ : F.functor ≅ (P ≫ BinaryNormalizationSimplex.sourceMap f g).functor}

theorem preBinaryNodes_source_ref : (preBinaryNodes F P f g ρ 0).2 = ρ := by
  change ρ ≪≫ isoWhiskerLeft P.functor (Iso.refl _) = ρ
  rw [isoWhiskerLeft_refl]
  exact Iso.trans_refl ρ

theorem preBinaryNodes_target_ref : (preBinaryNodes F P f g ρ 2).2 =
    ρ ≪≫ isoWhiskerLeft P.functor (BinaryNormalizationSimplex.total f g) := rfl

/-- Equality of full source nodes retains the whole original precomposed binary row. -/
theorem preBinaryNodes_of_source
    (he : preBinaryNodes F P f g ρ 0 = preBinaryNodes F P f g σ 0) (i : Fin 3) :
    preBinaryNodes F P f g ρ i = preBinaryNodes F P f g σ i := by
  have hs : (preBinaryNodes F P f g ρ 0).2 = (preBinaryNodes F P f g σ 0).2 :=
    eq_of_heq (Sigma.mk.inj he).2
  rw [preBinaryNodes_source_ref, preBinaryNodes_source_ref] at hs
  exact congrArg (fun η ↦ preBinaryNodes F P f g η i) hs

/-- Equal full normalized endpoints retain the whole actual binary row by iso cancellation. -/
theorem preBinaryNodes_of_target
    (he : preBinaryNodes F P f g ρ 2 = preBinaryNodes F P f g σ 2) (i : Fin 3) :
    preBinaryNodes F P f g ρ i = preBinaryNodes F P f g σ i := by
  have hs : (preBinaryNodes F P f g ρ 2).2 = (preBinaryNodes F P f g σ 2).2 :=
    eq_of_heq (Sigma.mk.inj he).2
  rw [preBinaryNodes_target_ref, preBinaryNodes_target_ref] at hs
  have hc := congrArg
    (fun η ↦ η ≪≫ (isoWhiskerLeft P.functor (BinaryNormalizationSimplex.total f g)).symm) hs
  have hρ : ρ = σ := by simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hc
  exact congrArg (fun η ↦ preBinaryNodes F P f g η i) hρ

variable (F P f g)
/-- Actual scheme-factor equalities and full source equality preserve the entire original row. -/
theorem preBinaryNodes_source_congr {f' : X ⟶ Y} {g' : Y ⟶ Z} (hf : f = f') (hg : g = g')
    (ρ : F.functor ≅ (P ≫ BinaryNormalizationSimplex.sourceMap f g).functor)
    (σ : F.functor ≅ (P ≫ BinaryNormalizationSimplex.sourceMap f' g').functor)
    (he : preBinaryNodes F P f g ρ 0 = preBinaryNodes F P f' g' σ 0) (i : Fin 3) :
    preBinaryNodes F P f g ρ i = preBinaryNodes F P f' g' σ i := by
  subst f'
  subst g'
  exact preBinaryNodes_of_source he i

/-- Actual scheme-factor equalities and full target equality preserve both normalization pieces. -/
theorem preBinaryNodes_target_congr {f' : X ⟶ Y} {g' : Y ⟶ Z} (hf : f = f') (hg : g = g')
    (ρ : F.functor ≅ (P ≫ BinaryNormalizationSimplex.sourceMap f g).functor)
    (σ : F.functor ≅ (P ≫ BinaryNormalizationSimplex.sourceMap f' g').functor)
    (he : preBinaryNodes F P f g ρ 2 = preBinaryNodes F P f' g' σ 2) (i : Fin 3) :
    preBinaryNodes F P f g ρ i = preBinaryNodes F P f' g' σ i := by
  subst f'
  subst g'
  exact preBinaryNodes_of_target he i

end Quillen.PerfectComplexes.BassH0Merge

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.BoundedFlat.PairPullback
import Quillen.PerfectComplexes.DerivedPullbackFunctor

/-!
# Original supported and relative-open perfect K-functors

For arbitrary commutative open-pair squares with qc ambient schemes, actual
bounded-flat pullback gives maps on the original supported/relative K-groups
through the proved literal inclusion equivalences. Representative squares,
identity/composition and naturality of the original support-forgetting and
change-weak maps are proved in all connective degrees. The actual model
comparisons are natural isomorphisms. Connecting-map naturality and comparison
with all perfect K-theory of the open remain separate steps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes
variable {A B C : Quillen.Scheme.QuasiCompactOpenPairs.{u}}

/-- Original supported K-pullback through the proved literal bounded-flat inclusion. -/
def perfectSupportedKPullback (f : A ⟶ B) (n : ℕ) :
    PerfectSupportedK B.obj.obj.hom n →* PerfectSupportedK A.obj.obj.hom n :=
  (boundedFlatPerfectSupportedKEquiv A.obj.obj.hom n).toMonoidHom.comp
    ((boundedFlatPerfectSupportedKPullback f.hom n).comp (boundedFlatPerfectSupportedKEquiv B.obj.obj.hom n).symm.toMonoidHom)

theorem perfectSupportedKPullback_comp_boundedFlat (f : A ⟶ B) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (boundedFlatPerfectSupportedToPerfectSupportedKMap B.obj.obj.hom n) =
      (boundedFlatPerfectSupportedToPerfectSupportedKMap A.obj.obj.hom n).comp (boundedFlatPerfectSupportedKPullback f.hom n) := by
  ext x
  change boundedFlatPerfectSupportedKEquiv A.obj.obj.hom n
    (boundedFlatPerfectSupportedKPullback f.hom n ((boundedFlatPerfectSupportedKEquiv B.obj.obj.hom n).symm
      (boundedFlatPerfectSupportedKEquiv B.obj.obj.hom n x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem perfectSupportedKPullback_unique (f : A ⟶ B) (n : ℕ)
    (k : PerfectSupportedK B.obj.obj.hom n →* PerfectSupportedK A.obj.obj.hom n)
    (hk : k.comp (boundedFlatPerfectSupportedToPerfectSupportedKMap B.obj.obj.hom n) =
      (boundedFlatPerfectSupportedToPerfectSupportedKMap A.obj.obj.hom n).comp (boundedFlatPerfectSupportedKPullback f.hom n)) :
    k = perfectSupportedKPullback f n := by
  ext x
  obtain ⟨y, rfl⟩ := (boundedFlatPerfectSupportedToPerfectSupportedKMap_bijective B.obj.obj.hom n).surjective x
  exact DFunLike.congr_fun (hk.trans (perfectSupportedKPullback_comp_boundedFlat f n).symm) y

@[simp] theorem perfectSupportedKPullback_id (A : Quillen.Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ) :
    perfectSupportedKPullback (𝟙 A) n = MonoidHom.id _ := by
  symm
  apply perfectSupportedKPullback_unique
  change (MonoidHom.id _).comp (boundedFlatPerfectSupportedToPerfectSupportedKMap A.obj.obj.hom n) =
    (boundedFlatPerfectSupportedToPerfectSupportedKMap A.obj.obj.hom n).comp (boundedFlatPerfectSupportedKPullback (𝟙 A.obj) n)
  simp only [boundedFlatPerfectSupportedKPullback_id, MonoidHom.id_comp, MonoidHom.comp_id]

@[simp] theorem perfectSupportedKPullback_comp (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    perfectSupportedKPullback (f ≫ g) n = (perfectSupportedKPullback f n).comp (perfectSupportedKPullback g n) := by
  symm
  apply perfectSupportedKPullback_unique
  rw [MonoidHom.comp_assoc, perfectSupportedKPullback_comp_boundedFlat,
    ← MonoidHom.comp_assoc, perfectSupportedKPullback_comp_boundedFlat, MonoidHom.comp_assoc]
  change _ = (boundedFlatPerfectSupportedToPerfectSupportedKMap A.obj.obj.hom n).comp (boundedFlatPerfectSupportedKPullback (f.hom ≫ g.hom) n)
  rw [boundedFlatPerfectSupportedKPullback_comp]

def PerfectSupportedKFunctor (n : ℕ) : Quillen.Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (PerfectSupportedK X.unop.obj.obj.hom n)
  map f := GrpCat.ofHom (perfectSupportedKPullback f.unop n)
  map_id X := by apply GrpCat.hom_ext; exact perfectSupportedKPullback_id X.unop n
  map_comp f g := by apply GrpCat.hom_ext; exact perfectSupportedKPullback_comp g.unop f.unop n

/-- Original open K-pullback through the proved literal bounded-flat inclusion. -/
def perfectOpenKPullback (f : A ⟶ B) (n : ℕ) :
    PerfectOpenK B.obj.obj.hom n →* PerfectOpenK A.obj.obj.hom n :=
  (boundedFlatPerfectOpenKEquiv A.obj.obj.hom n).toMonoidHom.comp
    ((boundedFlatPerfectOpenKPullback f.hom n).comp (boundedFlatPerfectOpenKEquiv B.obj.obj.hom n).symm.toMonoidHom)

theorem perfectOpenKPullback_comp_boundedFlat (f : A ⟶ B) (n : ℕ) :
    (perfectOpenKPullback f n).comp (boundedFlatPerfectOpenToPerfectOpenKMap B.obj.obj.hom n) =
      (boundedFlatPerfectOpenToPerfectOpenKMap A.obj.obj.hom n).comp (boundedFlatPerfectOpenKPullback f.hom n) := by
  ext x
  change boundedFlatPerfectOpenKEquiv A.obj.obj.hom n
    (boundedFlatPerfectOpenKPullback f.hom n ((boundedFlatPerfectOpenKEquiv B.obj.obj.hom n).symm
      (boundedFlatPerfectOpenKEquiv B.obj.obj.hom n x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem perfectOpenKPullback_unique (f : A ⟶ B) (n : ℕ)
    (k : PerfectOpenK B.obj.obj.hom n →* PerfectOpenK A.obj.obj.hom n)
    (hk : k.comp (boundedFlatPerfectOpenToPerfectOpenKMap B.obj.obj.hom n) =
      (boundedFlatPerfectOpenToPerfectOpenKMap A.obj.obj.hom n).comp (boundedFlatPerfectOpenKPullback f.hom n)) :
    k = perfectOpenKPullback f n := by
  ext x
  obtain ⟨y, rfl⟩ := (boundedFlatPerfectOpenToPerfectOpenKMap_bijective B.obj.obj.hom n).surjective x
  exact DFunLike.congr_fun (hk.trans (perfectOpenKPullback_comp_boundedFlat f n).symm) y

@[simp] theorem perfectOpenKPullback_id (A : Quillen.Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ) :
    perfectOpenKPullback (𝟙 A) n = MonoidHom.id _ := by
  symm
  apply perfectOpenKPullback_unique
  change (MonoidHom.id _).comp (boundedFlatPerfectOpenToPerfectOpenKMap A.obj.obj.hom n) =
    (boundedFlatPerfectOpenToPerfectOpenKMap A.obj.obj.hom n).comp (boundedFlatPerfectOpenKPullback (𝟙 A.obj) n)
  simp only [boundedFlatPerfectOpenKPullback_id, MonoidHom.id_comp, MonoidHom.comp_id]

@[simp] theorem perfectOpenKPullback_comp (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    perfectOpenKPullback (f ≫ g) n = (perfectOpenKPullback f n).comp (perfectOpenKPullback g n) := by
  symm
  apply perfectOpenKPullback_unique
  rw [MonoidHom.comp_assoc, perfectOpenKPullback_comp_boundedFlat,
    ← MonoidHom.comp_assoc, perfectOpenKPullback_comp_boundedFlat, MonoidHom.comp_assoc]
  change _ = (boundedFlatPerfectOpenToPerfectOpenKMap A.obj.obj.hom n).comp (boundedFlatPerfectOpenKPullback (f.hom ≫ g.hom) n)
  rw [boundedFlatPerfectOpenKPullback_comp]

def PerfectOpenKFunctor (n : ℕ) : Quillen.Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (PerfectOpenK X.unop.obj.obj.hom n)
  map f := GrpCat.ofHom (perfectOpenKPullback f.unop n)
  map_id X := by apply GrpCat.hom_ext; exact perfectOpenKPullback_id X.unop n
  map_comp f g := by apply GrpCat.hom_ext; exact perfectOpenKPullback_comp g.unop f.unop n

theorem perfectSupportedKMap_pullback (f : A ⟶ B) (n : ℕ) :
    (perfectKPullback f.hom.hom.right n).comp (perfectSupportedKMap B.obj.obj.hom n) =
      (perfectSupportedKMap A.obj.obj.hom n).comp (perfectSupportedKPullback f n) := by
  ext x
  obtain ⟨y, rfl⟩ := (boundedFlatPerfectSupportedToPerfectSupportedKMap_bijective B.obj.obj.hom n).surjective x
  have h₁ := DFunLike.congr_fun (boundedFlatPerfectSupportedToPerfectSupported_comp B.obj.obj.hom n) y
  have h₂ := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat f n) y
  simp only [MonoidHom.comp_apply] at h₁ h₂ ⊢
  rw [h₁, h₂]
  have h₃ := DFunLike.congr_fun (perfectKPullback_comp_boundedFlat f.hom.hom.right n)
    (boundedFlatPerfectSupportedKMap B.obj.obj.hom n y)
  have h₄ := DFunLike.congr_fun (boundedFlatPerfectSupportedToPerfectSupported_comp A.obj.obj.hom n)
    (boundedFlatPerfectSupportedKPullback f.hom n y)
  have h₅ := DFunLike.congr_fun (boundedFlatPerfectSupportedKMap_pullback f.hom n) y
  simp only [MonoidHom.comp_apply] at h₃ h₄ h₅
  rw [h₃, h₄]
  exact congrArg (boundedFlatPerfectToPerfectKMap A.obj.obj.right n) h₅

theorem perfectOpenKMap_pullback (f : A ⟶ B) (n : ℕ) :
    (perfectOpenKPullback f n).comp (perfectOpenKMap B.obj.obj.hom n) =
      (perfectOpenKMap A.obj.obj.hom n).comp (perfectKPullback f.hom.hom.right n) := by
  ext x
  obtain ⟨y, rfl⟩ := (boundedFlatPerfectToPerfectKMap_bijective B.obj.obj.right n).surjective x
  have h₁ := DFunLike.congr_fun (boundedFlatPerfectOpenToPerfectOpen_comp B.obj.obj.hom n) y
  have h₂ := DFunLike.congr_fun (perfectKPullback_comp_boundedFlat f.hom.hom.right n) y
  simp only [MonoidHom.comp_apply] at h₁ h₂ ⊢
  rw [← h₁, h₂]
  have h₃ := DFunLike.congr_fun (perfectOpenKPullback_comp_boundedFlat f n)
    (boundedFlatPerfectOpenKMap B.obj.obj.hom n y)
  have h₄ := DFunLike.congr_fun (boundedFlatPerfectOpenToPerfectOpen_comp A.obj.obj.hom n)
    (boundedFlatPerfectKPullback f.hom.hom.right n y)
  have h₅ := DFunLike.congr_fun (boundedFlatPerfectOpenKMap_pullback f.hom n) y
  simp only [MonoidHom.comp_apply] at h₃ h₄ h₅
  rw [h₃, ← h₄]
  exact congrArg (boundedFlatPerfectOpenToPerfectOpenKMap A.obj.obj.hom n) h₅

def perfectSupportedNatTrans (n : ℕ) :
    PerfectSupportedKFunctor.{u} n ⟶ Quillen.Scheme.quasiCompactOpenPairsBase.op ⋙ PerfectKFunctor n where
  app X := GrpCat.ofHom (perfectSupportedKMap X.unop.obj.obj.hom n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (perfectSupportedKMap_pullback f.unop n).symm

def perfectOpenNatTrans (n : ℕ) :
    Quillen.Scheme.quasiCompactOpenPairsBase.op ⋙ PerfectKFunctor n ⟶ PerfectOpenKFunctor.{u} n where
  app X := GrpCat.ofHom (perfectOpenKMap X.unop.obj.obj.hom n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (perfectOpenKMap_pullback f.unop n).symm

/-- The literal original supported inclusion comparison is naturally invertible. -/
def boundedFlatPerfectSupportedNatIso (n : ℕ) :
    Quillen.Scheme.quasiCompactOpenPairsInclusion.op ⋙ BoundedFlatPerfectSupportedKFunctor.{u} n ≅
      PerfectSupportedKFunctor n :=
  NatIso.ofComponents (fun X => (boundedFlatPerfectSupportedKEquiv X.unop.obj.obj.hom n).toGrpIso)
    (fun f => by
      apply GrpCat.hom_ext
      exact (perfectSupportedKPullback_comp_boundedFlat f.unop n).symm)

@[simp] theorem boundedFlatPerfectSupportedNatIso_hom_app (n : ℕ)
    (X : Quillen.Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ) :
    ((boundedFlatPerfectSupportedNatIso n).hom.app X).hom = boundedFlatPerfectSupportedToPerfectSupportedKMap X.unop.obj.obj.hom n := rfl

/-- The literal original open inclusion comparison is naturally invertible. -/
def boundedFlatPerfectOpenNatIso (n : ℕ) :
    Quillen.Scheme.quasiCompactOpenPairsInclusion.op ⋙ BoundedFlatPerfectOpenKFunctor.{u} n ≅
      PerfectOpenKFunctor n :=
  NatIso.ofComponents (fun X => (boundedFlatPerfectOpenKEquiv X.unop.obj.obj.hom n).toGrpIso)
    (fun f => by
      apply GrpCat.hom_ext
      exact (perfectOpenKPullback_comp_boundedFlat f.unop n).symm)

@[simp] theorem boundedFlatPerfectOpenNatIso_hom_app (n : ℕ)
    (X : Quillen.Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ) :
    ((boundedFlatPerfectOpenNatIso n).hom.app X).hom = boundedFlatPerfectOpenToPerfectOpenKMap X.unop.obj.obj.hom n := rfl

end Quillen.PerfectComplexes

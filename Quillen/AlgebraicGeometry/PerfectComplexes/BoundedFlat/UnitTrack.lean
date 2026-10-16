/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.GlobalUnitPullback
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationTrackPasting
public import Quillen.Topology.Prespectrum.RelativeHomotopyReparam
public import Quillen.Topology.Prespectrum.RelativeHomotopyHorizontal

/-! Unit naturality along the unchanged geometric and binary-normalization composition tracks. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- Postwhiskering an actual unit commutes relatively with the original composition track. -/
def boundedFlatPerfectUnitTrackPostcomp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(Y, ⊤))ˣ) :
    ((boundedFlatPerfectPrespectrumCompHomotopy f g).trans
      ((boundedFlatPerfectUnitHomotopy g r).postcomp
        (boundedFlatPerfectPrespectrumMap f))).RelHomotopy
    ((boundedFlatPerfectUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).trans
      (boundedFlatPerfectPrespectrumCompHomotopy f g)) := by
  let W := boundedFlatPerfectWaldhausen Z
  let U := boundedFlatPerfectWaldhausen X
  let hA := boundedFlatPerfectPullback_exact (f ≫ g)
  let hB := (boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f)
  let e := boundedFlatPerfectPullbackCompIso f g
  let a := boundedFlatPerfectPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)
  let b := Functor.isoWhiskerRight (boundedFlatPerfectPullbackUnitIso g r)
    (boundedFlatPerfectPullback f)
  let G := exactOriginalPrespectrumIsoHomotopy W U hA hB e
  let B := exactOriginalPrespectrumIsoHomotopy W U hB hB b
  let A := boundedFlatPerfectUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)
  let N := exactOriginalPrespectrumMapCompHomotopy W (boundedFlatPerfectWaldhausen Y) U
    (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullback_exact f)
  let D := (boundedFlatPerfectUnitHomotopy g r).postcomp (boundedFlatPerfectPrespectrumMap f)
  have JG : (G.trans B).RelHomotopy (A.trans G) :=
    exactOriginalPrespectrumPastingHomotopy W U hA hB hA hB
      e.hom b.hom a.hom e.hom (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (boundedFlatPerfectPullbackUnitIso_comp f g r)
  have JN : (B.trans N).RelHomotopy (N.trans D) :=
    exactNormalizationLeftTrackPasting (boundedFlatPerfectPullback_exact g)
      (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullback_exact f)
      (boundedFlatPerfectPullbackUnitIso g r).hom
      (fun _ ↦ (boundedFlatPerfectWaldhausen Y).weq_iso _ inferInstance)
  exact (Homotopy.RelHomotopy.transAssoc G N D).trans
    (((Homotopy.RelHomotopy.refl G).hcomp JN.symm).trans
      ((Homotopy.RelHomotopy.transAssoc G B N).symm.trans
        ((JG.hcomp (Homotopy.RelHomotopy.refl N)).trans
          (Homotopy.RelHomotopy.transAssoc A G N))))

/-- The target scalar intertwines the genuine geometric pullback composition comparison. -/
lemma boundedFlatPerfectPullbackUnitIso_comp_target {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectPullbackCompIso f g).hom ≫
      Functor.whiskerLeft (boundedFlatPerfectPullback g)
        (boundedFlatPerfectPullbackUnitIso f r).hom =
    (boundedFlatPerfectPullbackUnitIso (f ≫ g) r).hom ≫
      (boundedFlatPerfectPullbackCompIso f g).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, boundedFlatPerfectPullbackUnitIso, Iso.trans_hom,
    Iso.symm_hom, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  exact (boundedFlatPerfectGlobalUnitIso X r).hom.naturality _

/-- Prewhiskering an actual unit commutes relatively with the original composition track. -/
def boundedFlatPerfectUnitTrackPrecomp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(X, ⊤))ˣ) :
    ((boundedFlatPerfectPrespectrumCompHomotopy f g).trans
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
        (boundedFlatPerfectUnitHomotopy f r))).RelHomotopy
    ((boundedFlatPerfectUnitHomotopy (f ≫ g) r).trans
      (boundedFlatPerfectPrespectrumCompHomotopy f g)) := by
  let W := boundedFlatPerfectWaldhausen Z
  let U := boundedFlatPerfectWaldhausen X
  let hA := boundedFlatPerfectPullback_exact (f ≫ g)
  let hB := (boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f)
  let e := boundedFlatPerfectPullbackCompIso f g
  let a := boundedFlatPerfectPullbackUnitIso (f ≫ g) r
  let b := Functor.isoWhiskerLeft (boundedFlatPerfectPullback g)
    (boundedFlatPerfectPullbackUnitIso f r)
  let G := exactOriginalPrespectrumIsoHomotopy W U hA hB e
  let B := exactOriginalPrespectrumIsoHomotopy W U hB hB b
  let A := boundedFlatPerfectUnitHomotopy (f ≫ g) r
  let N := exactOriginalPrespectrumMapCompHomotopy W (boundedFlatPerfectWaldhausen Y) U
    (boundedFlatPerfectPullback_exact g) (boundedFlatPerfectPullback_exact f)
  let D := Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
    (boundedFlatPerfectUnitHomotopy f r)
  have JG : (G.trans B).RelHomotopy (A.trans G) :=
    exactOriginalPrespectrumPastingHomotopy W U hA hB hA hB
      e.hom b.hom a.hom e.hom (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (boundedFlatPerfectPullbackUnitIso_comp_target f g r)
  have JN : (B.trans N).RelHomotopy (N.trans D) :=
    exactNormalizationRightTrackPasting (boundedFlatPerfectPullback_exact g)
      (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectPullback_exact f)
      (boundedFlatPerfectPullbackUnitIso f r).hom
      (fun _ ↦ U.weq_iso _ inferInstance)
  exact (Homotopy.RelHomotopy.transAssoc G N D).trans
    (((Homotopy.RelHomotopy.refl G).hcomp JN.symm).trans
      ((Homotopy.RelHomotopy.transAssoc G B N).symm.trans
        ((JG.hcomp (Homotopy.RelHomotopy.refl N)).trans
          (Homotopy.RelHomotopy.transAssoc A G N))))

end Quillen.PerfectComplexes

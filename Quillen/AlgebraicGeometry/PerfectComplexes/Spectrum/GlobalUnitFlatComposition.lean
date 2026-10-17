/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnit
public import Quillen.Aglib.AlgebraicGeometry.Modules.Scalar.Pullback
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationTrackPasting
public import Quillen.Waldhausen.SConstruction.Iterated.ExactPastingHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyReparam
public import Quillen.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationIntertwining
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationNaturality

/-!
# Whole original Perfect unit tracks under flat composition

The actual global scalar commutes with geometric flat pullback on locally perfect complexes.
Its two categorical composition squares give whole relative prespectrum homotopies along the
original geometric comparison followed by binary normalization. Their all-degree K-operation
consequences retain the original maps, units, and every input, including degree zero.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- Faithful inclusion retains the original global-unit component on ambient complexes. -/
theorem perfectGlobalUnitIso_hom_original (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : Perfect X) :
    (locallyPerfect X).ι.map ((perfectGlobalUnitIso X r).hom.app K) =
      (complexGlobalUnitIso X r).hom.app K.obj := by
  simp only [perfectGlobalUnitIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    ObjectProperty.ι_obj]

/-- Actual flat pullback carries the original scalar automorphism to its pulled-back unit. -/
theorem perfectFlatPullback_map_globalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (r : (Γ(Y, ⊤))ˣ) (K : Perfect Y) :
    (perfectFlatPullback f).map ((perfectGlobalUnitIso Y r).hom.app K) =
      (perfectGlobalUnitIso X (Units.map f.appTop.hom.toMonoidHom r)).hom.app
        ((perfectFlatPullback f).obj K) := by
  apply (locallyPerfect X).ι.map_injective
  change (Scheme.Modules.Complex.pullback f).map
    ((locallyPerfect Y).ι.map ((perfectGlobalUnitIso Y r).hom.app K)) = _
  rw [perfectGlobalUnitIso_hom_original, perfectGlobalUnitIso_hom_original]
  apply HomologicalComplex.hom_ext
  intro n
  change (Scheme.Modules.pullback f).map (((complexGlobalUnitIso Y r).hom.app K.obj).f n) = _
  rw [complexGlobalUnitIso_original_terms, complexGlobalUnitIso_original_terms]
  exact AlgebraicGeometry.Scheme.Modules.pullback_map_globalScalar f (↑r) (K.obj.X n)

/-- The original geometric composition iso intertwines the actual pulled-back source unit. -/
theorem perfectFlatPullbackUnitIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] (r : (Γ(Y, ⊤))ˣ) :
    (perfectFlatPullbackCompIso f g).hom ≫
      Functor.whiskerRight (perfectFlatPullbackUnitIso g r).hom (perfectFlatPullback f) =
    (perfectFlatPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).hom ≫
      (perfectFlatPullbackCompIso f g).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, perfectFlatPullbackUnitIso, Iso.trans_hom,
    Iso.symm_hom, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  rw [perfectFlatPullback_map_globalUnit]
  exact (perfectGlobalUnitIso X (Units.map f.appTop.hom.toMonoidHom r)).hom.naturality _

/-- Postwhiskering an actual unit commutes relatively with the original composition track. -/
def perfectFlatUnitTrackPostcomp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] (r : (Γ(Y, ⊤))ˣ) :
    ((perfectFlatPrespectrumCompHomotopy f g).trans
      ((perfectFlatUnitHomotopy g r).postcomp
        (perfectFlatPrespectrumMap f))).RelHomotopy
    ((perfectFlatUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)).trans
      (perfectFlatPrespectrumCompHomotopy f g)) := by
  let W := perfectWaldhausen Z
  let U := perfectWaldhausen X
  let hA := perfectFlatPullback_waldhausenExact (f ≫ g)
  let hB := (perfectFlatPullback_waldhausenExact g).comp (perfectFlatPullback_waldhausenExact f)
  let e := perfectFlatPullbackCompIso f g
  let a := perfectFlatPullbackUnitIso (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)
  let b := Functor.isoWhiskerRight (perfectFlatPullbackUnitIso g r)
    (perfectFlatPullback f)
  let G := exactOriginalPrespectrumIsoHomotopy W U hA hB e
  let B := exactOriginalPrespectrumIsoHomotopy W U hB hB b
  let A := perfectFlatUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)
  let N := exactOriginalPrespectrumMapCompHomotopy W (perfectWaldhausen Y) U
    (perfectFlatPullback_waldhausenExact g) (perfectFlatPullback_waldhausenExact f)
  let D := (perfectFlatUnitHomotopy g r).postcomp (perfectFlatPrespectrumMap f)
  have JG : (G.trans B).RelHomotopy (A.trans G) :=
    exactOriginalPrespectrumPastingHomotopy W U hA hB hA hB
      e.hom b.hom a.hom e.hom (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (perfectFlatPullbackUnitIso_comp f g r)
  have JN : (B.trans N).RelHomotopy (N.trans D) :=
    exactNormalizationLeftTrackPasting (perfectFlatPullback_waldhausenExact g)
      (perfectFlatPullback_waldhausenExact g) (perfectFlatPullback_waldhausenExact f)
      (perfectFlatPullbackUnitIso g r).hom
      (fun _ ↦ (perfectWaldhausen Y).weq_iso _ inferInstance)
  exact (Homotopy.RelHomotopy.transAssoc G N D).trans
    (((Homotopy.RelHomotopy.refl G).hcomp JN.symm).trans
      ((Homotopy.RelHomotopy.transAssoc G B N).symm.trans
        ((JG.hcomp (Homotopy.RelHomotopy.refl N)).trans
          (Homotopy.RelHomotopy.transAssoc A G N))))

/-- The target scalar intertwines the genuine geometric pullback composition comparison. -/
lemma perfectFlatPullbackUnitIso_comp_target {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] (r : (Γ(X, ⊤))ˣ) :
    (perfectFlatPullbackCompIso f g).hom ≫
      Functor.whiskerLeft (perfectFlatPullback g)
        (perfectFlatPullbackUnitIso f r).hom =
    (perfectFlatPullbackUnitIso (f ≫ g) r).hom ≫
      (perfectFlatPullbackCompIso f g).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, perfectFlatPullbackUnitIso, Iso.trans_hom,
    Iso.symm_hom, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  exact (perfectGlobalUnitIso X r).hom.naturality _

/-- Prewhiskering an actual unit commutes relatively with the original composition track. -/
def perfectFlatUnitTrackPrecomp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] (r : (Γ(X, ⊤))ˣ) :
    ((perfectFlatPrespectrumCompHomotopy f g).trans
      (Homotopy.precomp (perfectFlatPrespectrumMap g)
        (perfectFlatUnitHomotopy f r))).RelHomotopy
    ((perfectFlatUnitHomotopy (f ≫ g) r).trans
      (perfectFlatPrespectrumCompHomotopy f g)) := by
  let W := perfectWaldhausen Z
  let U := perfectWaldhausen X
  let hA := perfectFlatPullback_waldhausenExact (f ≫ g)
  let hB := (perfectFlatPullback_waldhausenExact g).comp (perfectFlatPullback_waldhausenExact f)
  let e := perfectFlatPullbackCompIso f g
  let a := perfectFlatPullbackUnitIso (f ≫ g) r
  let b := Functor.isoWhiskerLeft (perfectFlatPullback g)
    (perfectFlatPullbackUnitIso f r)
  let G := exactOriginalPrespectrumIsoHomotopy W U hA hB e
  let B := exactOriginalPrespectrumIsoHomotopy W U hB hB b
  let A := perfectFlatUnitHomotopy (f ≫ g) r
  let N := exactOriginalPrespectrumMapCompHomotopy W (perfectWaldhausen Y) U
    (perfectFlatPullback_waldhausenExact g) (perfectFlatPullback_waldhausenExact f)
  let D := Homotopy.precomp (perfectFlatPrespectrumMap g)
    (perfectFlatUnitHomotopy f r)
  have JG : (G.trans B).RelHomotopy (A.trans G) :=
    exactOriginalPrespectrumPastingHomotopy W U hA hB hA hB
      e.hom b.hom a.hom e.hom (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
      (fun _ ↦ U.weq_iso _ inferInstance) (perfectFlatPullbackUnitIso_comp_target f g r)
  have JN : (B.trans N).RelHomotopy (N.trans D) :=
    exactNormalizationRightTrackPasting (perfectFlatPullback_waldhausenExact g)
      (perfectFlatPullback_waldhausenExact f) (perfectFlatPullback_waldhausenExact f)
      (perfectFlatPullbackUnitIso f r).hom
      (fun _ ↦ U.weq_iso _ inferInstance)
  exact (Homotopy.RelHomotopy.transAssoc G N D).trans
    (((Homotopy.RelHomotopy.refl G).hcomp JN.symm).trans
      ((Homotopy.RelHomotopy.transAssoc G B N).symm.trans
        ((JG.hcomp (Homotopy.RelHomotopy.refl N)).trans
          (Homotopy.RelHomotopy.transAssoc A G N))))


/-- Flat target pullback preserves the complete original unit operation in every degree. -/
theorem perfectFlatUnitHomotopy_originalKOperation_postcomp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g]
    (r : (Γ(Y, ⊤))ˣ) (n : ℕ) :
    (perfectKFlatPullback f (n + 1)).comp
      (originalKSelfTrackOperation (perfectWaldhausen Z) (perfectWaldhausen Y)
        (perfectFlatUnitHomotopy g r) n) =
    originalKSelfTrackOperation (perfectWaldhausen Z) (perfectWaldhausen X)
      (perfectFlatUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r)) n := by
  unfold perfectKFlatPullback
  rw [← originalKSelfTrackOperation_postcomp]
  exact (originalKSelfTrackOperation_intertwine (perfectWaldhausen Z) (perfectWaldhausen X)
    (perfectFlatUnitHomotopy (f ≫ g) (Units.map f.appTop.hom.toMonoidHom r))
    ((perfectFlatUnitHomotopy g r).postcomp (perfectFlatPrespectrumMap f))
    (perfectFlatPrespectrumCompHomotopy f g) (perfectFlatUnitTrackPostcomp f g r).symm n).symm

/-- Flat source pullback preserves the complete original unit operation in every degree. -/
theorem perfectFlatUnitHomotopy_originalKOperation_precomp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g]
    (q : (Γ(X, ⊤))ˣ) (n : ℕ) :
    (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
      (perfectFlatUnitHomotopy f q) n).comp (perfectKFlatPullback g n) =
    originalKSelfTrackOperation (perfectWaldhausen Z) (perfectWaldhausen X)
      (perfectFlatUnitHomotopy (f ≫ g) q) n := by
  unfold perfectKFlatPullback
  rw [← originalKSelfTrackOperation_precomp]
  exact (originalKSelfTrackOperation_intertwine (perfectWaldhausen Z) (perfectWaldhausen X)
    (perfectFlatUnitHomotopy (f ≫ g) q)
    (Homotopy.precomp (perfectFlatPrespectrumMap g) (perfectFlatUnitHomotopy f q))
    (perfectFlatPrespectrumCompHomotopy f g) (perfectFlatUnitTrackPrecomp f g q).symm n).symm

end Quillen.PerfectComplexes

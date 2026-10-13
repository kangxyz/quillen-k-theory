/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.QuasicoherentHomology
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenPushforwardQuasicoherent
public import Quillen.AlgebraicGeometry.PerfectComplexes.InjectivePushforwardAdjunction

/-! # The actual open restriction-unit cone

The cone of the original chain adjoint into an actual injective direct image
has quasicoherent homology, vanishes after original restriction when its local
input is a quasi-isomorphism, and retains the exact lower cohomological bound.
These are proved for the literal all-sheaf cone. Its global perfection is not
assumed or asserted. The support conclusion needs no compactness; quasicoherence
uses quasi-compactness of the open immersion.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
/-- The standard upper-universe derived category used in restriction-cone comparisons. -/
local instance restrictionConeDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The actual adjoint cone has QC homology for a quasi-compact open immersion. -/
lemma quasicoherent_homology_restrictionUnitCone {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (K : Complex X) (I : Complex U) (a : ℤ)
    (hb : ∀ n, n < a → IsZero (I.X n)) (hi : ∀ n, Injective (I.X n))
    (hK : ∀ n, (K.homology n).IsQuasicoherent)
    (hI : ∀ n, (I.homology n).IsQuasicoherent)
    (q : (restrict j).obj K ⟶ I) (n : ℤ) :
    ((CochainComplex.mappingCone
      ((restrictPushforwardComplexAdjunction j).homEquiv K I q)).homology n).IsQuasicoherent :=
  quasicoherent_homology_mappingCone _ hK
    (openPushforward_quasicoherent_homology j I a hb hi hI) n

/-- An original local weak replacement makes the literal adjoint cone vanish on the open. -/
lemma isZero_restrict_restrictionUnitCone {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : Complex X) (I : Complex U)
    (q : (restrict j).obj K ⟶ I) [QuasiIso q] :
    IsZero ((toDerived U).obj ((restrict j).obj (CochainComplex.mappingCone
      ((restrictPushforwardComplexAdjunction j).homEquiv K I q)))) := by
  let f := (restrictPushforwardComplexAdjunction j).homEquiv K I q
  let := quasiIso_restrict_chain_adjoint j q
  have hz : IsZero ((toDerived U).obj (CochainComplex.mappingCone ((restrict j).map f))) := by
    apply CategoryTheory.Pretriangulated.Triangle.isZero₃_of_isIso₁ _
      (mappingConeTriangle_distinguished _)
    change IsIso ((toDerived U).map ((restrict j).map f))
    infer_instance
  exact hz.of_iso ((toDerived U).mapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (Scheme.Modules.restrictFunctor j)))

/-- A lower term bound on the injective target gives the exact global cone bound. -/
lemma restrictionUnitCone_isGE {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : Complex X) (I : Complex U) (a b : ℤ)
    (hb : ∀ n, n < a → IsZero (I.X n)) [K.IsGE b]
    (q : (restrict j).obj K ⟶ I) :
    (CochainComplex.mappingCone ((restrictPushforwardComplexAdjunction j).homEquiv K I q)).IsGE
      (min (b-1) a) := by
  have : I.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff I a).mpr hb
  have : ((pushforwardComplex j).obj I).IsStrictlyGE a := by
    dsimp only [pushforwardComplex]
    infer_instance
  exact mappingCone_isGE _ b a

/-- The genuine local replacement alone supplies target QC homology. The literal
original adjoint cone has QC homology, the exact lower bound, and zero restriction. -/
theorem restrictionUnitCone_properties {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (K : Complex X) (I : Complex U) (a b : ℤ)
    (hb : ∀ n, n < a → IsZero (I.X n)) (hi : ∀ n, Injective (I.X n))
    (hK : ∀ n, (K.homology n).IsQuasicoherent) [K.IsGE b]
    (q : (restrict j).obj K ⟶ I) [QuasiIso q] :
    let C := CochainComplex.mappingCone ((restrictPushforwardComplexAdjunction j).homEquiv K I q)
    (∀ n, (C.homology n).IsQuasicoherent) ∧ C.IsGE (min (b-1) a) ∧
      IsZero ((toDerived U).obj ((restrict j).obj C)) := by
  have hI (n : ℤ) : (I.homology n).IsQuasicoherent := by
    have : IsIso (HomologicalComplex.homologyMap q n) :=
      (quasiIsoAt_iff_isIso_homologyMap q n).mp inferInstance
    exact (SheafOfModules.isQuasicoherent U.ringCatSheaf).prop_of_iso
      (asIso (HomologicalComplex.homologyMap q n))
      (Affine.quasicoherent_homology_restrict j K hK n)
  exact ⟨quasicoherent_homology_restrictionUnitCone j K I a hb hi hK hI q,
    restrictionUnitCone_isGE j K I a b hb q,
    isZero_restrict_restrictionUnitCone j K I q⟩

end Quillen.PerfectComplexes

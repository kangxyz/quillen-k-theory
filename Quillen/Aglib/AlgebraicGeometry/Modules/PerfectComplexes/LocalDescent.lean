/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Complex.Homology
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure
public import Quillen.Aglib.AlgebraicGeometry.Modules.Restriction.OpenCoverVanishing
public import Aglib.Algebra.Homology.MappingCone.QuasiIso
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
/-! # Actual local perfection, acyclicity and quasi-isomorphism descent

Local neighborhoods are pushed forward using their actual scheme image
isomorphisms. Actual restriction and stalk/homology identities detect
acyclicity and quasi-isomorphisms. Covers may be arbitrarily large; no
quasi-compactness or supplied global strict representative is required.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u w
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.PerfectComplexes

/-- Local perfection patches from arbitrary actual open neighborhoods. -/
theorem locallyPerfect_of_openNeighborhoods {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    (hK : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ locallyPerfect U.toScheme ((restrict U.ι).obj K)) :
    locallyPerfect X K := by
  intro x
  obtain ⟨U,hx,hU⟩ := hK x
  obtain ⟨T,hT,P,⟨eP⟩⟩ := hU ⟨x,hx⟩
  let O : X.Opens := U.ι ''ᵁ T
  let e : T.toScheme ≅ O.toScheme := U.ι.isoImage T
  let ec : (restrict U.ι ⋙ restrict T.ι) ⋙ restrict e.inv ≅ restrict O.ι :=
    Functor.isoWhiskerRight (restrictCompIso T.ι U.ι) (restrict e.inv) ≪≫
      restrictCompIso e.inv (T.ι ≫ U.ι) ≪≫
      eqToIso (restrict_congr (U.ι.isoImage_inv_ι T))
  refine ⟨O, ?_, ⟨(restrict e.inv).obj P.obj, strictPerfect_restrict _ P.property⟩, ?_⟩
  · exact ⟨⟨x,hx⟩,hT,rfl⟩
  · exact ⟨(DerivedCategory.Q (C := O.toScheme.Modules)).mapIso
      (ec.app K).symm ≪≫ restrictDerivedIso e.inv eP⟩

/-- Arbitrary covers detect actual local perfection; no finite cover is required. -/
theorem locallyPerfect_of_openCover {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ} {ι : Type w}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hK : ∀ i, locallyPerfect (U i).toScheme ((restrict (U i).ι).obj K)) : locallyPerfect X K :=
  locallyPerfect_of_openNeighborhoods fun x => by
    obtain ⟨i,hi⟩ := hU x
    exact ⟨U i,hi,hK i⟩

/-- A pair of actual opens covering the scheme detects local perfection. -/
theorem locallyPerfect_of_binaryOpenCover {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (hU : locallyPerfect U.toScheme ((restrict U.ι).obj K))
    (hV : locallyPerfect V.toScheme ((restrict V.ι).obj K)) : locallyPerfect X K := by
  apply locallyPerfect_of_openNeighborhoods
  intro x
  have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
  rcases hx with hx | hx
  · exact ⟨U,hx,hU⟩
  · exact ⟨V,hx,hV⟩
end Quillen.PerfectComplexes


namespace Quillen.PerfectComplexes
/-- Actual acyclicity is detected by arbitrary open covers. -/
theorem acyclic_of_openCover {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) {ι : Type w}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hK : ∀ i, ((restrict (U i).ι).obj K).Acyclic) : K.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply AlgebraicGeometry.Scheme.Modules.isZero_of_openCover _ U hU
  intro i
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (hK i n)).of_iso
    (restrictHomologyIso (U i).ι K n).symm

/-- Actual quasi-isomorphisms are detected by arbitrary open covers. -/
theorem quasiIso_of_openCover {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    {ι : Type w}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hf : ∀ i, QuasiIso ((restrict (U i).ι).map f)) : QuasiIso f := by
  apply CochainComplex.quasiIso_of_mappingCone_acyclic
  apply acyclic_of_openCover _ U hU
  intro i
  let := hf i
  intro n
  exact (CochainComplex.mappingCone_acyclic_of_quasiIso
    ((restrict (U i).ι).map f) n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (Scheme.Modules.restrictFunctor (U
      i).ι)).symm
end Quillen.PerfectComplexes

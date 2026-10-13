/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedStructure
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.QuasicoherentClosure
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.Support
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Quasicoherent cohomology of the actual locally perfect complexes

The homology of any locally perfect complex is quasicoherent. The proof uses
actual derived isomorphisms and exact geometric restriction, followed by local
presentations on an affine refinement. On a quasi-compact scheme, a finite
subcover also gives uniform cohomological bounds. There is no termwise quasicoherence or
affine strictification hypothesis on the original complex.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Quillen.CoherentScheme

/-- Quasicoherence is local on actual open neighborhoods. -/
theorem quasicoherent_of_openNeighborhoods {X : Scheme.{u}} (M : X.Modules)
    (hM : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (M.restrict U.ι).IsQuasicoherent) :
    M.IsQuasicoherent := by
  classical
  have h (x : X) : ∃ V : X.affineOpens, x ∈ V.1 ∧
      (M.restrict V.2.fromSpec).IsQuasicoherent := by
    obtain ⟨U, hxU, hU⟩ := hM x
    obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    let j := X.homOfLE hVU
    have : ((M.restrict U.ι).restrict j).IsQuasicoherent := inferInstance
    let e : (M.restrict U.ι).restrict j ≅ M.restrict V.ι :=
      ((Scheme.Modules.restrictFunctorComp j U.ι).app M).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (by simp [j])).app M
    have : (M.restrict V.ι).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso e inferInstance
    have : ((M.restrict V.ι).restrict hV.isoSpec.inv).IsQuasicoherent := inferInstance
    let e' : (M.restrict V.ι).restrict hV.isoSpec.inv ≅ M.restrict hV.fromSpec :=
      ((Scheme.Modules.restrictFunctorComp hV.isoSpec.inv V.ι).app M).symm
    exact ⟨⟨V, hV⟩, hxV,
      (SheafOfModules.isQuasicoherent (Spec Γ(X, V)).ringCatSheaf).prop_of_iso e' inferInstance⟩
  choose V hV hq using h
  let q : M.QuasicoherentData :=
    { I := X
      X := fun x => (V x).1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover]
        apply top_unique
        intro x _
        exact Opens.mem_iSup.mpr ⟨x, hV x⟩
      presentation x := affinePresentationToOver M (V x)
        (affineQuasicoherent_exists_presentation _ (M.restrict (V x).2.fromSpec)).some }
  exact q.isQuasicoherent

/-- Homology of an actual termwise quasicoherent sheaf complex is
quasicoherent, on an arbitrary scheme. -/
theorem quasicoherent_homology {X : Scheme.{u}} (K : Quillen.PerfectComplexes.Complex X)
    (hK : ∀ i, (K.X i).IsQuasicoherent) (i : ℤ) : (K.homology i).IsQuasicoherent := by
  let S := K.sc i
  have : S.X₁.IsQuasicoherent := hK _
  have : S.X₂.IsQuasicoherent := hK _
  have : S.X₃.IsQuasicoherent := hK _
  have : (kernel S.g).IsQuasicoherent := quasicoherent_kernel S.g
  have h := quasicoherent_cokernel (kernel.lift S.g S.f S.zero)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    S.homologyIsoCokernelLift.symm h

end Quillen.CoherentScheme

namespace Quillen.PerfectComplexes

/-- The standard derived-category structure on sheaves of modules on `X`, used for the homology of
locally perfect complexes. -/
local instance standardDerivedSheaves (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- An isomorphism in the original quasi-isomorphism localization induces
an isomorphism on the actual sheaf homology. -/
def homologyIsoOfDerivedIso {X : Scheme.{u}} {K L : Complex X}
    (e : (toDerived X).obj K ≅ (toDerived X).obj L) (i : ℤ) :
    K.homology i ≅ L.homology i :=
  ((DerivedCategory.homologyFunctorFactors X.Modules i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor X.Modules i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors X.Modules i).app L

/-- Actual open restriction commutes with sheaf homology. -/
def restrictHomologyIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Complex X) (i : ℤ) :
    ((restrict j).obj K).homology i ≅ (Scheme.Modules.restrictFunctor j).obj (K.homology i) :=
  (K.sc i).mapHomologyIso (Scheme.Modules.restrictFunctor j)

/-- Every locally perfect complex has quasicoherent cohomology in the
ambient derived category of all module sheaves, with no global strict model
or termwise quasicoherence assumed. -/
theorem locallyPerfect_quasicoherent_homology {X : Scheme.{u}} {K : Complex X}
    (hK : locallyPerfect X K) (i : ℤ) : (K.homology i).IsQuasicoherent := by
  apply CoherentScheme.quasicoherent_of_openNeighborhoods
  intro x
  obtain ⟨U, hxU, P, ⟨e⟩⟩ := hK x
  have hP : (P.obj.homology i).IsQuasicoherent :=
    CoherentScheme.quasicoherent_homology P.obj (fun n => by
      let := P.property.2 n
      infer_instance) i
  exact ⟨U, hxU,
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((homologyIsoOfDerivedIso e i).symm ≪≫ restrictHomologyIso U.ι K i) hP⟩


/-- A local strict model gives actual vanishing of homology sheaves outside
its term bounds, on the same neighborhood. -/
theorem locallyPerfect_exists_local_homology_bounds {X : Scheme.{u}} {K : Complex X}
    (hK : locallyPerfect X K) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj (K.homology i)) := by
  obtain ⟨U, hxU, P, ⟨e⟩⟩ := hK x
  obtain ⟨⟨a, b, hb⟩, _⟩ := P.property
  refine ⟨U, hxU, a, b, fun i hi => ?_⟩
  have hz : IsZero (P.obj.homology i) :=
    (P.obj.sc i).isZero_homology_of_isZero_X₂ (hb i hi)
  exact hz.of_iso ((restrictHomologyIso U.ι K i).symm ≪≫ homologyIsoOfDerivedIso e i)

/-- On a quasi-compact scheme, the actual cohomology sheaves of every
locally perfect complex vanish outside a single finite interval. The finite
subcover argument does not construct a global strict representative. -/
theorem locallyPerfect_homology_bounded {X : Scheme.{u}} [CompactSpace X]
    {K : Complex X} (hK : locallyPerfect X K) :
    ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.homology i) := by
  classical
  choose U hx a b hvan using locallyPerfect_exists_local_homology_bounds hK
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  obtain ⟨A, hA⟩ := (s.finite_toSet.image a).bddBelow
  obtain ⟨B, hB⟩ := (s.finite_toSet.image b).bddAbove
  refine ⟨A, B, fun i hi => ?_⟩
  apply (SchemeSheaf.isZero_iff_stalks _).mpr
  intro y
  obtain ⟨x, hxs, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
  have hAx : A ≤ a x := hA ⟨x, hxs, rfl⟩
  have hxB : b x ≤ B := hB ⟨x, hxs, rfl⟩
  have hz := hvan x i (by rcases hi with hi | hi <;> omega)
  have hs := (SchemeSheaf.isZero_iff_stalks _).mp hz ⟨y, hy⟩
  exact hs.of_iso ((Scheme.Modules.restrictStalkNatIso (U x).ι ⟨y, hy⟩).app
    (K.homology i)).symm

end Quillen.PerfectComplexes

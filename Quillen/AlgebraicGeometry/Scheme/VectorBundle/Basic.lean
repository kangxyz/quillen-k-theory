/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Finite presentation and finite locally free sheaves on a scheme

The predicates in this file refer to actual sheaves of modules on the Zariski
site of a scheme. Finite local freeness is witnessed by one family of local
bases whose index sets are finite. A local basis gives a finite presentation
with no relations, so every finite locally free sheaf is of finite
presentation and quasicoherent.

This file does not identify finite presentation with coherence, or install an
exact structure on either full subcategory. Those require additional closure
theorems.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v v' w w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

namespace Quillen.SchemeSheaf

section Presentation

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type w'} [Category.{v'} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [HasSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transporting generating sections by an isomorphism preserves the basis condition. -/
instance generatingSections_ofEpi_isIso {M N : SheafOfModules.{u} R}
    (G : M.GeneratingSections) (f : M ⟶ N) [IsIso f] [IsIso G.π] :
    IsIso (G.ofEpi f).π := by
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

/-- A colimit-preserving functor which preserves the unit carries finite
presentations to finite presentations: the generator and relation index sets
are unchanged. -/
instance finitePresentation_map_isFinite {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) :
    (P.map F η).IsFinite where
  isFiniteType_generators := by
    constructor
    change Finite P.generators.I
    infer_instance
  isFiniteType_relations := by
    constructor
    change Finite P.relations.I
    infer_instance

end Presentation

variable (X : Scheme.{u})

private theorem hasSheafifyOver :
    ∀ U : TopologicalSpace.Opens X,
      HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} :=
  fun _ => inferInstance

private theorem hasWeakSheafifyOver :
    ∀ U : TopologicalSpace.Opens X,
      HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} :=
  fun U => (hasSheafifyOver X U).isRightAdjoint

private theorem wEqualsLocallyBijectiveOver :
    ∀ U : TopologicalSpace.Opens X,
      ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
  fun _ => inferInstance

attribute [local instance] hasSheafifyOver hasWeakSheafifyOver wEqualsLocallyBijectiveOver

/-- Sheaves admitting finite local presentations on the Zariski site of `X`. -/
abbrev finitePresentation : ObjectProperty X.Modules :=
  SheafOfModules.isFinitePresentation X.ringCatSheaf

/-- The full category of sheaves of modules of finite presentation on `X`. -/
abbrev FinitePresentation := (finitePresentation X).FullSubcategory

/-- A finite locally free sheaf has a single local generating family which
is both a basis and finite on every member of its cover. -/
class IsFiniteLocallyFree (M : X.Modules) : Prop where
  exists_localBasis : ∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
    q.IsLocallyFreeData ∧ q.IsFiniteType

/-- The property of being finite locally free. -/
abbrev finiteLocallyFree : ObjectProperty X.Modules := IsFiniteLocallyFree X

/-- The full category of finite locally free sheaves on `X`. -/
abbrev FiniteLocallyFree := (finiteLocallyFree X).FullSubcategory

variable {X}

instance finitePresentation_obj (M : FinitePresentation X) :
    SheafOfModules.IsFinitePresentation.{u} M.obj := M.property

instance finiteLocallyFree_obj (M : FiniteLocallyFree X) :
    IsFiniteLocallyFree X M.obj := M.property

/-- A finite global presentation gives a finite presentation on the Zariski site. -/
theorem finitePresentation_of_presentation {M : X.Modules}
    (P : SheafOfModules.Presentation M) [P.IsFinite] : finitePresentation X M := by
  refine SheafOfModules.IsFinitePresentation.mk (M := M) ⟨P.quasicoherentData, ?_⟩
  constructor
  intro U
  dsimp [SheafOfModules.Presentation.quasicoherentData]
  infer_instance

/-- Forgetting finiteness of the local bases gives local freeness. -/
instance isLocallyFree_of_finiteLocallyFree (M : X.Modules)
    [h : IsFiniteLocallyFree X M] : SheafOfModules.IsLocallyFree.{u} M := by
  obtain ⟨q, hq, _⟩ := h.exists_localBasis
  exact q.isLocallyFree

/-- A finite local basis presents the sheaf with an empty family of relations. -/
theorem finitePresentation_of_localBasis {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{u} M)
    [q.IsLocallyFreeData] [hq : q.IsFiniteType] :
    SheafOfModules.IsFinitePresentation.{u} M := by
  refine SheafOfModules.IsFinitePresentation.mk (M := M) ⟨q.quasiCoherentData, ?_⟩
  constructor
  intro i
  constructor
  · exact hq.isFiniteType i
  · constructor
    change Finite (ULift Empty)
    infer_instance

/-- Finite locally free sheaves have finite presentations. -/
instance isFinitePresentation_of_finiteLocallyFree (M : X.Modules)
    [h : IsFiniteLocallyFree X M] : SheafOfModules.IsFinitePresentation.{u} M := by
  obtain ⟨q, hq, hf⟩ := h.exists_localBasis
  exact finitePresentation_of_localBasis q

/-- Finite local presentations in particular give quasicoherence. The
scheme-specific instance keeps this implication available across the opaque
`Scheme.Modules` wrapper. -/
instance isQuasicoherent_of_finitePresentation (M : X.Modules)
    [SheafOfModules.IsFinitePresentation.{u} M] :
    SheafOfModules.IsQuasicoherent.{u} M :=
  SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M

/-- The inclusion of finite locally free sheaves among finitely presented
sheaves is justified by the local presentations with no relations. -/
theorem finiteLocallyFree_le_finitePresentation :
    finiteLocallyFree X ≤ finitePresentation X := by
  intro M hM
  exact isFinitePresentation_of_finiteLocallyFree M

/-- The fully faithful inclusion of finite locally free sheaves into sheaves
of finite presentation. -/
abbrev finiteLocallyFreeToFinitePresentation :
    FiniteLocallyFree X ⥤ FinitePresentation X :=
  ObjectProperty.ιOfLE (finiteLocallyFree_le_finitePresentation (X := X))

/-- Forgetting the finiteness condition does not change the underlying sheaf
or any morphisms. -/
abbrev finitePresentationForget : FinitePresentation X ⥤ X.Modules :=
  (finitePresentation X).ι

/-- Forgetting the local bases does not change the underlying sheaf or morphisms. -/
abbrev finiteLocallyFreeForget : FiniteLocallyFree X ⥤ X.Modules :=
  (finiteLocallyFree X).ι

/-- Both ways of forgetting a finite locally free sheaf agree. -/
theorem finiteLocallyFreeToFinitePresentation_comp_forget :
    finiteLocallyFreeToFinitePresentation (X := X) ⋙ finitePresentationForget =
      finiteLocallyFreeForget := rfl

/-- Finite presentation is invariant under isomorphism of scheme modules. -/
theorem finitePresentation_iff_of_iso {M N : X.Modules} (e : M ≅ N) :
    finitePresentation X M ↔ finitePresentation X N :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_iff_of_iso e

instance finitePresentation_closedUnderIsomorphisms :
    (finitePresentation X).IsClosedUnderIsomorphisms where
  of_iso e h := (finitePresentation_iff_of_iso e).mp h

/-- Transport the chosen local bases along an isomorphism. -/
def localBasisOfIso {M N : X.Modules} (e : M ≅ N)
    (q : SheafOfModules.LocalGeneratorsData.{u} M) :
    SheafOfModules.LocalGeneratorsData.{u} N where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi (e.hom.over (q.X i))

instance localBasisOfIso_isLocallyFreeData {M N : X.Modules} (e : M ≅ N)
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [q.IsLocallyFreeData] :
    (localBasisOfIso e q).IsLocallyFreeData where
  isIso i := by
    dsimp [localBasisOfIso]
    infer_instance

instance localBasisOfIso_isFiniteType {M N : X.Modules} (e : M ≅ N)
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [hq : q.IsFiniteType] :
    (localBasisOfIso e q).IsFiniteType where
  isFiniteType i := ⟨(hq.isFiniteType i).finite⟩

/-- Finite local freeness is invariant under isomorphism. -/
theorem finiteLocallyFree_of_iso {M N : X.Modules} (e : M ≅ N)
    [h : IsFiniteLocallyFree X M] : IsFiniteLocallyFree X N := by
  obtain ⟨q, hq, hf⟩ := h.exists_localBasis
  exact ⟨localBasisOfIso e q, inferInstance, inferInstance⟩

instance finiteLocallyFree_closedUnderIsomorphisms :
    (finiteLocallyFree X).IsClosedUnderIsomorphisms where
  of_iso e _h := finiteLocallyFree_of_iso e

/-- Finite local freeness is equivalent for isomorphic sheaves. -/
theorem finiteLocallyFree_iff_of_iso {M N : X.Modules} (e : M ≅ N) :
    finiteLocallyFree X M ↔ finiteLocallyFree X N :=
  (finiteLocallyFree X).prop_iff_of_iso e

/-- A finite free sheaf is finite locally free. -/
instance finiteLocallyFree_free (I : Type u) [Finite I] :
    IsFiniteLocallyFree X (SheafOfModules.free (R := X.ringCatSheaf) I) := by
  let q := (SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).localGeneratorsData
  refine ⟨q, inferInstance, ?_⟩
  constructor
  intro i
  constructor
  change Finite I
  infer_instance

/-- A free sheaf on a finite index set admits a finite local presentation. -/
theorem finitePresentation_free (I : Type u) [Finite I] :
    finitePresentation X (SheafOfModules.free (R := X.ringCatSheaf) I) :=
  inferInstance

/-- The free sheaf on the empty set is a zero sheaf. -/
theorem isZero_free_empty :
    IsZero (SheafOfModules.free (R := X.ringCatSheaf) (ULift Empty)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply (SheafOfModules.freeHomEquiv _).injective
  funext i
  exact i.down.elim

/-- Every zero scheme module is finite locally free, of rank zero. -/
theorem finiteLocallyFree_of_isZero {M : X.Modules} (hM : IsZero M) :
    IsFiniteLocallyFree X M :=
  finiteLocallyFree_of_iso ((isZero_free_empty (X := X)).iso hM)

instance finiteLocallyFree_zero : IsFiniteLocallyFree X (0 : X.Modules) :=
  finiteLocallyFree_of_isZero (isZero_zero _)

instance finiteLocallyFree_containsZero : (finiteLocallyFree X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, inferInstance⟩

instance finitePresentation_containsZero : (finitePresentation X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, inferInstance⟩

/-- In particular every zero module admits a finite local presentation. -/
theorem finitePresentation_of_isZero {M : X.Modules} (hM : IsZero M) :
    finitePresentation X M := (finitePresentation X).prop_of_isZero hM

/-- The finite free sheaf of a specified rank, as a finite locally free object. -/
def finiteFree (n : ℕ) : FiniteLocallyFree X :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) (ULift (Fin n)), inferInstance⟩

/-- The finite locally free object associated to a sheaf equipped with finite local bases. -/
def ofFiniteLocallyFree (M : X.Modules) [IsFiniteLocallyFree X M] :
    FiniteLocallyFree X := ⟨M, inferInstance⟩

/-- The finitely presented object associated to a sheaf with finite presentations. -/
def ofFinitePresentation (M : X.Modules) [SheafOfModules.IsFinitePresentation.{u} M] :
    FinitePresentation X := ⟨M, inferInstance⟩

end Quillen.SchemeSheaf

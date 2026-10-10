/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.FlatPullback
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GlobalUnit
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopy
public import Quillen.Waldhausen.SConstruction.Iterated.ExactCoherence
public import Quillen.Topology.Prespectrum.HomotopyLoop

/-!
The literal sheaf scalar acts termwise on original perfect complexes and gives a whole coherent
spectrum homotopy for genuine flat pullback. Original normalized composition homotopies are
retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum

/-- Actual degreewise multiplication by a global unit on the original ambient complexes. -/
def complexGlobalUnitIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    𝟭 (Complex X) ≅ 𝟭 (Complex X) :=
  (Functor.mapHomologicalComplexIdIso _ _).symm ≪≫
    NatIso.mapHomologicalComplex (Quillen.SchemeSheaf.globalUnitIso X r) (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ _

/-- The same actual scalar automorphism on the original locally-perfect category. -/
def perfectGlobalUnitIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    𝟭 (Perfect X) ≅ 𝟭 (Perfect X) :=
  Functor.fullyFaithfulCancelRight (locallyPerfect X).ι
    (Functor.isoWhiskerLeft (locallyPerfect X).ι (complexGlobalUnitIso X r))

/-- The global unit acts on the actual geometric flat pullback functor. -/
def perfectFlatPullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (r : (Γ(X, ⊤))ˣ) : perfectFlatPullback f ≅ perfectFlatPullback f :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (perfectFlatPullback f) (perfectGlobalUnitIso X r) ≪≫
      Functor.rightUnitor _

lemma complexGlobalUnitIso_original_terms (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : Complex X) (n : ℤ) :
    ((complexGlobalUnitIso X r).hom.app K).f n =
      (SchemeSheaf.globalUnitIso X r).hom.app (K.X n) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rfl

/-- The actual normalized spectrum map of a genuinely flat geometric morphism. -/
def perfectFlatPrespectrumMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    originalPrespectrum (perfectWaldhausen Y) ⟶ originalPrespectrum (perfectWaldhausen X) :=
  exactOriginalPrespectrumMap _ _ (perfectFlatPullback_waldhausenExact f)

/-- An original global unit gives the full structure-compatible self-homotopy of flat pullback. -/
def perfectFlatUnitHomotopy {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (r : (Γ(X, ⊤))ˣ) :
    LoopPrespectrum.Homotopy (perfectFlatPrespectrumMap f) (perfectFlatPrespectrumMap f) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (perfectFlatPullback_waldhausenExact f)
    (perfectFlatPullback_waldhausenExact f) (perfectFlatPullbackUnitIso f r)

/-- The actual flat geometric composition comparison, including canonical spectrum normalization. -/
def perfectFlatPrespectrumCompHomotopy {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Flat f] [Flat g] :
    Homotopy (perfectFlatPrespectrumMap (f ≫ g))
      (perfectFlatPrespectrumMap g ≫ perfectFlatPrespectrumMap f) :=
  (exactOriginalPrespectrumIsoHomotopy _ _ (perfectFlatPullback_waldhausenExact (f ≫ g))
    ((perfectFlatPullback_waldhausenExact g).comp (perfectFlatPullback_waldhausenExact f))
    (perfectFlatPullbackCompIso f g)).trans
      (exactOriginalPrespectrumMap_comp_homotopy _ _ _
        (perfectFlatPullback_waldhausenExact g) (perfectFlatPullback_waldhausenExact f))


end Quillen.PerfectComplexes

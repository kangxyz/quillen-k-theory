/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.SigmaChains
public import Quillen.Topology.LocalCoefficients.MapSquares
public import Quillen.Topology.LocalCoefficients.Abelian
public import Quillen.Topology.Realization.Coproduct
public import Quillen.Algebra.Category.ModuleCat.CoproductHomology

/-!
# Original twisted maps on topological disjoint unions

The actual chain coproduct isomorphisms intertwine the original componentwise
spatial map with the coproduct of the original component maps and their specified
pullback coefficient conversions. Quasi-isomorphisms therefore assemble, including
for possibly nonconstant abelian-monodromy target systems.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.LocalCoefficients
variable {ι : Type u} {X Y : ι → Type u}
  [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
  (f : ∀ i, C(X i, Y i))

/-- The original coefficient conversion on a component of a sigma spatial map. -/
def sigmaMapComponentPullbackIso (A : System.{u, u} (Σ i, Y i)) (i : ι) :
    pullback (ContinuousMap.sigmaMk i) (pullback (Quillen.sigmaContinuousMap f) A) ≅
      pullback (f i) (pullback (ContinuousMap.sigmaMk i) A) :=
  pullbackSquareIso (ContinuousMap.sigmaMk i) (ContinuousMap.sigmaMk i) (f i)
    (Quillen.sigmaContinuousMap f) rfl A

/-- The original sigma map is the actual coproduct of its coefficient-corrected components. -/
theorem sigmaChainComplexIso_naturality (A : System.{u, u} (Σ i, Y i)) :
    (sigmaChainComplexIso X (pullback (Quillen.sigmaContinuousMap f) A)).hom ≫
        pushforwardChainMap (Quillen.sigmaContinuousMap f) A =
      Limits.Sigma.map (fun i ↦ coefficientChainMap (sigmaMapComponentPullbackIso f A i).hom ≫
        pushforwardChainMap (f i) (pullback (ContinuousMap.sigmaMk i) A)) ≫
          (sigmaChainComplexIso Y A).hom := by
  apply Sigma.hom_ext
  intro i
  simp only [sigmaChainComplexIso_inclusion_assoc, Sigma.ι_map_assoc,
    Category.assoc, sigmaChainComplexIso_inclusion]
  exact (pushforwardChainMap_square (ContinuousMap.sigmaMk i) (ContinuousMap.sigmaMk i)
    (f i) (Quillen.sigmaContinuousMap f) rfl A).symm

/-- Actual component quasi-isomorphisms imply the quasi-isomorphism of the original sigma map. -/
theorem sigmaContinuousMap_quasiIso (A : System.{u, u} (Σ i, Y i))
    (hf : ∀ i, QuasiIso (pushforwardChainMap (f i) (pullback (ContinuousMap.sigmaMk i) A))) :
    QuasiIso (pushforwardChainMap (Quillen.sigmaContinuousMap f) A) := by
  let φ (i : ι) := coefficientChainMap (sigmaMapComponentPullbackIso f A i).hom ≫
    pushforwardChainMap (f i) (pullback (ContinuousMap.sigmaMk i) A)
  have (i : ι) : QuasiIso (φ i) := by
    have := hf i
    change QuasiIso ((coefficientChainIso (sigmaMapComponentPullbackIso f A i)).hom ≫
      pushforwardChainMap (f i) (pullback (ContinuousMap.sigmaMk i) A))
    infer_instance
  have : QuasiIso (Limits.Sigma.map φ) :=
    ModuleCat.quasiIso_sigma_map ℤ ι (ComplexShape.down ℕ) φ
  have : QuasiIso ((sigmaChainComplexIso X (pullback (Quillen.sigmaContinuousMap f) A)).hom ≫
      pushforwardChainMap (Quillen.sigmaContinuousMap f) A) := by
    rw [sigmaChainComplexIso_naturality]
    exact inferInstanceAs (QuasiIso (Limits.Sigma.map φ ≫ (sigmaChainComplexIso Y A).hom))
  exact quasiIso_of_comp_left
    (sigmaChainComplexIso X (pullback (Quillen.sigmaContinuousMap f) A)).hom
    (pushforwardChainMap (Quillen.sigmaContinuousMap f) A)

/-- The original disjoint-union map preserves all possibly nonconstant abelian target systems
when each original component map does. -/
theorem sigmaContinuousMap_abelian_quasiIso
    (hf : ∀ i (A : System.{u, u} (Y i)), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (f i) A))
    (A : System.{u, u} (Σ i, Y i)) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap (Quillen.sigmaContinuousMap f) A) := by
  apply sigmaContinuousMap_quasiIso f A
  intro i
  exact hf i _ (pullback_abelianMonodromy (ContinuousMap.sigmaMk i) hA)

end Quillen.LocalCoefficients

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarUnitTrackTransport
public import Quillen.Waldhausen.Fibration.SpectrumComparison
public import Quillen.Topology.Prespectrum.FiberHomotopySquare
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# The unchanged canonical acyclic null under the scalar/unit comparison

The actual raw-to-flat comparison is reversed first and followed by the whole old canonical
acyclic null after restriction. The original fiber-square producer retains every point of both
pieces, including level zero. No separate geometric Laurent null is identified with this one.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual rebase path is reversed before the entire original acyclic null. -/
def perfectOpenNormalizedAcyclicNullHomotopy :
    Homotopy
      (acyclicInclusionPrespectrumMap (perfectOpenNested j) ≫
        exactOriginalPrespectrumMap _ _ (changeWeak_exact (perfectOpenNested j)))
      (zeroHom (originalPrespectrum (acyclicStructure (perfectOpenNested j)))
        (originalPrespectrum (perfectOpenWeakWaldhausen j))) :=
  (Homotopy.precomp (acyclicInclusionPrespectrumMap (perfectOpenNested j))
    (perfectOpenChangeWeakNormalizationHomotopy j).symm).trans
      (acyclicPrespectrumNullhomotopy (perfectOpenNested j))

/-- The raw-to-flat fiber square uses the reversed original comparison, with levels fixed. -/
def perfectOpenFlatFiberSquareHomotopy :
    Homotopy ((𝟙 _) ≫ perfectFlatPrespectrumMap j)
      (changeWeakPrespectrumMap (perfectOpenNested j) ≫ perfectOpenScalarRestrictionMap j) :=
  (perfectOpenOriginalRestrictionFlatHomotopy j).symm.cast
    (Category.id_comp _).symm rfl

/-- The original canonical fiber map transported by precisely that actual homotopy square. -/
def perfectOpenFlatCanonicalFiberMap :
    originalPrespectrum (acyclicStructure (perfectOpenNested j)) ⟶
      homotopyFiber (perfectFlatPrespectrumMap j) :=
  canonicalFiberPrespectrumMap (perfectOpenNested j) ≫
    homotopyFiberSquareMap (changeWeakPrespectrumMap (perfectOpenNested j))
      (perfectFlatPrespectrumMap j) (𝟙 _) (perfectOpenScalarRestrictionMap j)
      (perfectOpenFlatFiberSquareHomotopy j)

/-- Its source is the unchanged original acyclic inclusion at every level. -/
theorem perfectOpenFlatCanonicalFiberMap_source (n : ℕ)
    (x : (originalPrespectrum (acyclicStructure (perfectOpenNested j))).space n) :
    ((perfectOpenFlatCanonicalFiberMap j).map n x).1.1 =
      (acyclicInclusionPrespectrumMap (perfectOpenNested j)).map n x := rfl

/-- Every point of the path is the reversed comparison followed by the original restricted null. -/
theorem perfectOpenFlatCanonicalFiberMap_path (n : ℕ)
    (x : (originalPrespectrum (acyclicStructure (perfectOpenNested j))).space n)
    (s : unitInterval) :
    ((perfectOpenFlatCanonicalFiberMap j).map n x).1.2 s =
      (((Homotopy.precomp (acyclicInclusionPrespectrumMap (perfectOpenNested j))
        (perfectOpenOriginalRestrictionFlatHomotopy j).symm).levelHomotopy n).trans
        (((acyclicPrespectrumNullhomotopy (perfectOpenNested j)).postcomp
          (perfectOpenScalarRestrictionMap j)).levelHomotopy n)) (s, x) := rfl

/-- The first half retains the entire original comparison in the required reversed direction. -/
theorem perfectOpenFlatCanonicalFiberMap_first_half (n : ℕ)
    (x : (originalPrespectrum (acyclicStructure (perfectOpenNested j))).space n)
    (t : unitInterval) :
    ((perfectOpenFlatCanonicalFiberMap j).map n x).1.2
        ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩ =
      (perfectOpenOriginalRestrictionFlatHomotopy j).level n
        (unitInterval.symm t, (acyclicInclusionPrespectrumMap (perfectOpenNested j)).map n x) :=
  homotopyFiberSquareMap_first_half _ _ _ _ (perfectOpenFlatFiberSquareHomotopy j) n
    ((canonicalFiberPrespectrumMap (perfectOpenNested j)).map n x) t

/-- The second half retains the whole old reversed zero-to-inclusion null after restriction. -/
theorem perfectOpenFlatCanonicalFiberMap_second_half (n : ℕ)
    (x : (originalPrespectrum (acyclicStructure (perfectOpenNested j))).space n)
    (t : unitInterval) :
    ((perfectOpenFlatCanonicalFiberMap j).map n x).1.2
        ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩ =
      (perfectOpenScalarRestrictionMap j).map n
        ((acyclicPrespectrumNullhomotopy (perfectOpenNested j)).level n (t, x)) := by
  rw [perfectOpenFlatCanonicalFiberMap_path, ContinuousMap.HomotopyRel.trans_apply]
  split
  · rename_i h
    have ht : t = 0 := by
      apply Subtype.ext
      change (t : ℝ) = 0
      change (1 + (t : ℝ)) / 2 ≤ 1 / 2 at h
      linarith [t.2.1]
    subst t
    change (perfectOpenOriginalRestrictionFlatHomotopy j).level n
        (⟨1 - 2 * ((1 + (0 : ℝ)) / 2), _⟩,
          (acyclicInclusionPrespectrumMap (perfectOpenNested j)).map n x) = _
    have hs : ∀ h, (⟨1 - 2 * ((1 + (0 : ℝ)) / 2), h⟩ : unitInterval) = 0 := by
      intro h
      apply Subtype.ext
      norm_num
    rw [hs, Homotopy.at_zero, Homotopy.at_zero]
    rfl
  · change (perfectOpenScalarRestrictionMap j).map n
        ((acyclicPrespectrumNullhomotopy (perfectOpenNested j)).level n
          (⟨2 * ((1 + (t : ℝ)) / 2) - 1, _⟩, x)) = _
    congr 2
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      ring
    · rfl

/-- The old ordinary canonical null is retained at every point of the second level-one half. -/
theorem perfectOpenFlatCanonicalFiberMap_level_one_second_half
    (x : (acyclicStructure (perfectOpenNested j)).Delooping) (t : unitInterval) :
    ((perfectOpenFlatCanonicalFiberMap j).map 1
        ((acyclicStructure (perfectOpenNested j)).smallModelDeloopingHomeomorph x)).1.2
        ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩ =
      (perfectOpenScalarRestrictionMap j).map 1
        ((perfectOpenWeakWaldhausen j).smallModelDeloopingHomeomorph
          (acyclicNullhomotopy (perfectOpenNested j) (t, x))) := by
  rw [perfectOpenFlatCanonicalFiberMap_second_half,
    acyclicPrespectrumNullhomotopy_level_one]
  rfl

end Quillen.PerfectComplexes

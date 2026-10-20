/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.PushoutHomotopySquare
public import Quillen.Topology.Prespectrum.RelativeHomotopySquarePasting
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering
public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting
public import Quillen.Topology.Prespectrum.PushoutMovingHomotopy
public import Quillen.Topology.Prespectrum.ConeHomotopySquare
public import Quillen.Topology.Prespectrum.HomotopySquareInterchange
public import Quillen.Topology.Prespectrum.HomotopySquareBoundary

/-!
# Input maps of split two-chart squares

A split square retains two independently specified tracks from a common map to its positive
and negative composites. An input consists of three vertex maps, their four square tracks,
and two proved chart-pasting comparisons with the displayed endpoint casts. These pastings
produce the actual overlap square, pushout comparison homotopy, cone map and parameter-looped
map, with their complete chart, cylinder and collapse equations.

The chart pastings are hypotheses of this reusable adapter. No application-specific filler,
strict functor law, localization nullhomotopy or seed comparison is supplied here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum

/-- Two chart maps with specified split tracks from one common map. -/
structure SplitSquare where
  /-- The source spectrum. -/
  A : LoopPrespectrum.{u}
  /-- The spectrum of either chart. -/
  P : LoopPrespectrum.{u}
  /-- The common target spectrum. -/
  L : LoopPrespectrum.{u}
  /-- The common projection to each chart. -/
  pi : A ⟶ P
  /-- The positive chart map. -/
  p : P ⟶ L
  /-- The negative chart map. -/
  m : P ⟶ L
  /-- The common unsplit map. -/
  l : A ⟶ L
  /-- The specified positive splitting. -/
  Dp : Homotopy l (pi ≫ p)
  /-- The specified negative splitting. -/
  Dm : Homotopy l (pi ≫ m)

namespace SplitSquare

variable (S : SplitSquare.{u})

/-- The overlap traverses the positive splitting backwards and the negative splitting forwards. -/
def squareHomotopy := S.Dp.symm.trans S.Dm

/-- The two copies of the chart joined along the common projection. -/
def span : LoopPrespectrum.{u} := HomotopyPushout.prespectrum S.pi S.pi

/-- The prescribed overlap descends to the common target. -/
def comparison : S.span ⟶ S.L :=
  HomotopyPushout.desc S.pi S.pi S.p S.m S.squareHomotopy

/-- The positive endpoint retains the specified chart map. -/
@[simp] theorem inl_comparison : HomotopyPushout.inl S.pi S.pi ≫ S.comparison = S.p :=
  HomotopyPushout.inl_desc _ _ _ _ _

/-- The negative endpoint retains the specified chart map. -/
@[simp] theorem inr_comparison : HomotopyPushout.inr S.pi S.pi ≫ S.comparison = S.m :=
  HomotopyPushout.inr_desc _ _ _ _ _

/-- Every cylinder height retains the specified overlap. -/
theorem comparison_cylinder (n : ℕ) (s : unitInterval) (x : S.A.space n) :
    S.comparison.map n (HomotopyPushout.cylinder S.pi S.pi n (s, x)) =
      S.squareHomotopy.level n (s, x) := rfl

/-- The parameter-looped cone of the split-square comparison. -/
def step : LoopPrespectrum.{u} := parameterLooping (mappingCone S.comparison)

/-- The positive source leg into the two-chart span. -/
def sourceLeg : S.A ⟶ S.span := S.pi ≫ HomotopyPushout.inl S.pi S.pi

/-- The source leg recovers the positive composite. -/
theorem sourceLeg_comparison : S.sourceLeg ≫ S.comparison = S.pi ≫ S.p := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- An input between split squares retains the exact two chart-pasting hypotheses.
The common outer track is shared by both comparisons, but their chart tracks remain independent. -/
structure Input (S S' : SplitSquare.{u}) where
  /-- The source map. -/
  a : S.A ⟶ S'.A
  /-- The chart map. -/
  b : S.P ⟶ S'.P
  /-- The target map. -/
  c : S.L ⟶ S'.L
  /-- The projection square. -/
  Q : Homotopy (S.pi ≫ b) (a ≫ S'.pi)
  /-- The positive chart square. -/
  Hp : Homotopy (S.p ≫ c) (b ≫ S'.p)
  /-- The negative chart square. -/
  Hm : Homotopy (S.m ≫ c) (b ≫ S'.m)
  /-- The common outer square. -/
  T : Homotopy (S.l ≫ c) (a ≫ S'.l)
  /-- The proved positive pasting, with its specified associations and endpoint casts. -/
  Jp :
    (((Homotopy.precomp S.pi Hp).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
        (Q.postcomp S'.p)).RelHomotopy
      ((S.Dp.postcomp c).symm.trans
        (T.trans ((Homotopy.precomp a S'.Dp).cast rfl (Category.assoc _ _ _).symm)))
  /-- The proved negative pasting, with the same common outer square. -/
  Jm :
    (((Homotopy.precomp S.pi Hm).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
        (Q.postcomp S'.m)).RelHomotopy
      ((S.Dm.postcomp c).symm.trans
        (T.trans ((Homotopy.precomp a S'.Dm).cast rfl (Category.assoc _ _ _).symm)))

namespace Input
variable {S S' : SplitSquare.{u}} (i : Input S S')

/-- Arbitrary input change supplies an actual map of the two-chart pushouts. -/
def spanMap : S.span ⟶ S'.span :=
  HomotopyPushout.mapOfHomotopies _ _ _ _ i.a i.b i.b i.Q i.Q

/-- The original left chart endpoint is retained literally. -/
@[simp]
lemma inl_spanMap :
    HomotopyPushout.inl _ _ ≫ spanMap i = i.b ≫ HomotopyPushout.inl _ _ :=
  HomotopyPushout.inl_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- The original right chart endpoint is retained literally. -/
@[simp]
lemma inr_spanMap :
    HomotopyPushout.inr _ _ ≫ spanMap i = i.b ≫ HomotopyPushout.inr _ _ :=
  HomotopyPushout.inr_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- Every cylinder point retains the specified pasted comparison tracks. -/
lemma spanMap_cylinder (n : ℕ) (s : unitInterval) (x : S.A.space n) :
    (spanMap i).map n (HomotopyPushout.cylinder S.pi S.pi n (s, x)) =
      (HomotopyPushout.mapSquareHomotopy _ _ _ _ i.a i.b i.b i.Q i.Q).level n (s, x) := rfl

/-- The two specified chart pastings cancel their common outer square and give
an actual relative boundary comparison, retaining the prescribed concatenation associations. -/
def inputBoundary :=
  Homotopy.RelHomotopy.pasteTwoSquares i.Jp i.Jm

/-- The right-associated target cylinder retains both original chart-square tracks. -/
def inputTargetTrack :=
  (i.Q.postcomp S'.p).trans
    (((Homotopy.precomp i.a S'.squareHomotopy).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
      (i.Q.symm.postcomp S'.m))

/-- The precise outer left association required by the moving-square conversion. -/
def inputPastedTrack :=
  (((Homotopy.precomp S.pi i.Hp).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    (inputTargetTrack i)).trans
    ((Homotopy.precomp S.pi i.Hm).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).symm

/-- The initial boundary is the entire split-square overlap under input change. -/
theorem inputBoundary_source_level (n : ℕ) :
    (S.squareHomotopy.postcomp i.c).level n =
      ((inputBoundary i).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  simp only [squareHomotopy, Homotopy.postcomp_trans,
    Homotopy.postcomp_symm]

/-- The constructed boundary ends at the target overlap cylinder with exact associations. -/
theorem inputBoundary_target_level (n : ℕ) :
    (inputPastedTrack i).level n =
      ((inputBoundary i).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · rfl
    · apply Homotopy.trans_level_congr
      · rfl
      · apply Homotopy.trans_level_congr
        · unfold squareHomotopy
          rw [Homotopy.precomp_trans, Homotopy.precomp_symm]
          apply Homotopy.trans_level_congr
          · apply Homotopy.symm_level_congr
            rfl
          · rfl
        · exact congrArg (fun H ↦ H.level n)
            (Homotopy.postcomp_symm i.Q S'.m)
  · rfl

/-- The specified overlap satisfies the actual input pasted-track relation. -/
def inputPasting :
    (S.squareHomotopy.postcomp i.c).RelHomotopy (inputPastedTrack i) :=
  Homotopy.RelHomotopy.ofLevels (inputBoundary i) _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using
      inputBoundary_source_level i n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using
      inputBoundary_target_level i n)

/-- Regroup the source endpoint maps to the literal span-comparison composition maps. -/
def inputSourceDescTrack :=
  (S.squareHomotopy.postcomp i.c).cast (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Regroup the target endpoints to the literal chart composite maps. -/
def inputTargetDescTrack :=
  (inputTargetTrack i).cast (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The exact boundary now uses the untransported precompositions of both target squares. -/
def inputPastedDescTrack :=
  ((Homotopy.precomp S.pi i.Hp).trans (inputTargetDescTrack i)).trans
    (Homotopy.precomp S.pi i.Hm).symm

/-- The specified boundary filler in the exact moving-pushout descent interface. -/
def inputDescPasting :
    (inputSourceDescTrack i).RelHomotopy
      (inputPastedDescTrack i) :=
  Homotopy.RelHomotopy.ofLevels (inputPasting i) _ _ (fun _ ↦ rfl)
    (by
      intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr <;> rfl
      · apply Homotopy.symm_level_congr
        rfl)

/-- The target track is the chart-span cylinder followed by the split-square comparison. -/
theorem inputTargetDescTrack_level (n : ℕ) :
    (inputTargetDescTrack i).level n =
      ((HomotopyPushout.mapSquareHomotopy S.pi S.pi S'.pi S'.pi
        i.a i.b i.b i.Q i.Q).postcomp S'.comparison).level n := by
  simp only [inputTargetDescTrack, Homotopy.cast_level,
    inputTargetTrack, HomotopyPushout.mapSquareHomotopy,
    Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- The source descent equals the literal split-square comparison followed by target change. -/
theorem inputSourceDesc_eq :
    HomotopyPushout.desc S.pi S.pi (S.p ≫ i.c) (S.m ≫ i.c) (inputSourceDescTrack i) =
      S.comparison ≫ i.c := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- The target descent equals the original chart-span map followed by split-square comparison. -/
theorem inputTargetDesc_eq :
    HomotopyPushout.desc S.pi S.pi (i.b ≫ S'.p) (i.b ≫ S'.m) (inputTargetDescTrack i) =
      spanMap i ≫ S'.comparison := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (inputTargetDescTrack_level i n) (s, x)

/-- The constructed moving square descends to the two unchanged input composites. -/
def inputComparisonHomotopy :
    Homotopy (S.comparison ≫ i.c) (spanMap i ≫ S'.comparison) :=
  (HomotopyPushout.descSquareHomotopy S.pi S.pi i.Hp i.Hm
    (inputDescPasting i).toSquare).cast
      (inputSourceDesc_eq i) (inputTargetDesc_eq i)

/-- The left chart endpoint moves through its unchanged positive target square. -/
theorem inputComparisonHomotopy_inl (n : ℕ) (r : unitInterval)
    (x : S.P.space n) :
    (inputComparisonHomotopy i).level n
      (r, (HomotopyPushout.inl S.pi S.pi).map n x) = i.Hp.level n (r, x) := rfl

/-- The right chart endpoint moves through its distinct negative target square. -/
theorem inputComparisonHomotopy_inr (n : ℕ) (r : unitInterval)
    (x : S.P.space n) :
    (inputComparisonHomotopy i).level n
      (r, (HomotopyPushout.inr S.pi S.pi).map n x) = i.Hm.level n (r, x) := rfl

/-- The whole actual cylinder retains the square constructed from the proved chart pasting. -/
theorem inputComparisonHomotopy_cylinder (n : ℕ) (r s : unitInterval)
    (x : S.A.space n) :
    (inputComparisonHomotopy i).level n
      (r, HomotopyPushout.cylinder S.pi S.pi n (s, x)) =
      (inputDescPasting i).toSquare.level n (r, (s, x)) := rfl

/-- The original relative comparison is recovered on every collapsed parameter-square point. -/
theorem inputComparisonHomotopy_collapse (n : ℕ)
    (z : unitInterval × unitInterval)
    (x : S.A.space n) :
    (inputComparisonHomotopy i).level n
      ((Quillen.ThreeSideSquare.collapse z).1,
        HomotopyPushout.cylinder S.pi S.pi n ((Quillen.ThreeSideSquare.collapse z).2, x)) =
      (inputDescPasting i).level n (z.1, (z.2, x)) :=
  (inputDescPasting i).toSquare_collapse n z x

/-- The comparison homotopy induces an actual map of the split-square comparison cones. -/
def coneMap : mappingCone S.comparison ⟶ mappingCone S'.comparison :=
  mappingConeSquareMap _ _ (spanMap i) i.c (inputComparisonHomotopy i)

/-- Parameter-correct looping gives a map between the actual one-step split-square spectra. -/
def map : S.step ⟶ S'.step :=
  parameterLoopingMap (coneMap i)

/-- The literal target inclusion commutes with the actual input cone map. -/
lemma coneMap_inclusion :
    mappingConeInclusion S.comparison ≫ coneMap i = i.c ≫ mappingConeInclusion S'.comparison :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- Parameter looping retains the literal target-inclusion square. -/
theorem map_inclusion :
    parameterLoopingMap (mappingConeInclusion S.comparison) ≫ map i =
      parameterLoopingMap i.c ≫ parameterLoopingMap (mappingConeInclusion S'.comparison) :=
  mappingConeSquareMap_parameterLooping_inclusion _ _ _ _ _

/-- The whole cone cylinder retains the actual input comparison and target cone null track. -/
lemma coneMap_cylinder (n : ℕ) (s : unitInterval)
    (x : S.span.space n) :
    (coneMap i).map n
      (ReducedMappingCone.cylinder _ _ (S.comparison.map n) (s, x)) =
    (((inputComparisonHomotopy i).postcomp
      (mappingConeInclusion S'.comparison)).trans
      (Homotopy.precomp (spanMap i)
        (mappingConeHomotopy S'.comparison))).level n (s, x) := rfl

/-- The unchanged positive source leg maps to its literal chart endpoint. -/
theorem sourceLeg_spanMap :
    S.sourceLeg ≫ spanMap i =
      (S.pi ≫ i.b) ≫ HomotopyPushout.inl S'.pi S'.pi := by
  unfold sourceLeg
  rw [Category.assoc, inl_spanMap, Category.assoc]

/-- The specified chart square moves the unchanged positive source leg. -/
def sourceLegInputHomotopy :
    Homotopy (S.sourceLeg ≫ spanMap i) (i.a ≫ S'.sourceLeg) :=
  (i.Q.postcomp (HomotopyPushout.inl S'.pi S'.pi)).cast
      (sourceLeg_spanMap i).symm (Category.assoc _ _ _)

/-- Source movement and the original raw cone contraction keep their parameters independent. -/
def sourceLegInputConeSquare :=
  Homotopy.Square.interchange (sourceLegInputHomotopy i)
    (mappingConeHomotopy S'.comparison)

/-- Both independent parameters retain the source-leg movement and the target cone contraction. -/
theorem sourceLegInputConeSquare_apply (n : ℕ) (r s : unitInterval)
    (x : S.A.space n) :
    (sourceLegInputConeSquare i).level n (r, (s, x)) =
      (mappingConeHomotopy S'.comparison).level n
        (s, (sourceLegInputHomotopy i).level n (r, x)) := rfl

/-- The positive source-leg movement retains its complete original cone boundary. -/
def sourceLegInputConeBoundary :=
  (sourceLegInputConeSquare i).toBoundary

/-- Parameter looping applies the same raw cone map at each independent loop coordinate. -/
theorem map_apply (n : ℕ) (s : unitInterval)
    (x : S.step.space n) :
    Path.toContinuousMap ((map i).map n x) s =
      (coneMap i).map n (Path.toContinuousMap x s) := rfl

end Input
end SplitSquare
end Quillen.LoopPrespectrum

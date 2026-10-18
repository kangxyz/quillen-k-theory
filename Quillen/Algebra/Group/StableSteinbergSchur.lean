/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.RepresentationTheory.Homological.GroupHomology.CentralBarLifts
public import Quillen.Algebra.Group.StableSteinbergUniversal
public import Quillen.Algebra.Group.StableSteinbergCentrality
public import Quillen.Aglib.Algebra.Group.Hom.CentralLifts
public import Quillen.Algebra.Group.StableSteinbergSymbols
public import Quillen.Aglib.RepresentationTheory.Homological.GroupHomology.IntegralBar
public import Quillen.Aglib.RepresentationTheory.Homological.GroupHomology.Torus

/-!
# The original stable Steinberg Schur comparison and ordered torus marking

The original chains, signs, maps, basepoints and stated hypotheses are retained.
-/
@[expose] public section

section

open groupHomology.IntegralBar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Quillen.StableSteinberg.Schur
variable (F : Type u) [Field F]

/-- The constructed actual integral bar extension of the original stable elementary group. -/
abbrev ElementaryBarExtension := IntegralBarExtension (StableGeneralLinear.elementary F)

/-- The original Steinberg universal lift into the explicit native H-two bar extension. -/
def steinbergToBar : StableSteinberg.Group F →* ElementaryBarExtension F :=
  StableSteinberg.liftToCentralExtension F
    (barProjection (ULift.{u} ℤ) (StableGeneralLinear.elementary F))
    (barProjection_surjective (ULift.{u} ℤ) (StableGeneralLinear.elementary F))
    (barProjection_ker_le_center (ULift.{u} ℤ) (StableGeneralLinear.elementary F))

/-- The original elementary projection is retained exactly. -/
theorem steinbergToBar_over :
    (barProjection (ULift.{u} ℤ) (StableGeneralLinear.elementary F)).comp (steinbergToBar F) =
      StableSteinberg.toElementary F :=
  StableSteinberg.liftToCentralExtension_over F _
    (barProjection_surjective (ULift.{u} ℤ) (StableGeneralLinear.elementary F))
    (barProjection_ker_le_center (ULift.{u} ℤ) (StableGeneralLinear.elementary F))

/-- The actual bar-cycle evaluation constructs a reverse map into the ORIGINAL Steinberg group. -/
def barToSteinberg : ElementaryBarExtension F →* StableSteinberg.Group F :=
  barLift (StableSteinberg.toElementary F) (StableSteinberg.toElementary_surjective F)
    (StableSteinberg.ker_toElementary_le_center F)

/-- Its actual projection equation is proved by the bar construction. -/
theorem barToSteinberg_over :
    (StableSteinberg.toElementary F).comp (barToSteinberg F) =
      barProjection (ULift.{u} ℤ) (StableGeneralLinear.elementary F) :=
  barLift_over (StableSteinberg.toElementary F) (StableSteinberg.toElementary_surjective F)
    (StableSteinberg.ker_toElementary_le_center F)

/-- Original Steinberg universal uniqueness makes the constructed reverse map a left inverse. -/
theorem barToSteinberg_left_inverse :
    (barToSteinberg F).comp (steinbergToBar F) = MonoidHom.id (StableSteinberg.Group F) := by
  apply StableSteinberg.liftToCentralExtension_unique F (StableSteinberg.toElementary F)
    (StableSteinberg.ker_toElementary_le_center F)
  · calc
      _ = ((StableSteinberg.toElementary F).comp (barToSteinberg F)).comp (steinbergToBar F) := rfl
      _ = (barProjection (ULift.{u} ℤ) (StableGeneralLinear.elementary F)).comp
          (steinbergToBar F) :=
            congrArg (fun p => p.comp (steinbergToBar F)) (barToSteinberg_over F)
      _ = _ := steinbergToBar_over F
  · rfl

/-- Injectivity follows from that actual constructed inverse, not from perfectness alone. -/
theorem steinbergToBar_injective : Function.Injective (steinbergToBar F) := by
  intro a b hab
  have ha := congrArg (fun h : StableSteinberg.Group F →* StableSteinberg.Group F => h a)
    (barToSteinberg_left_inverse F)
  have hb := congrArg (fun h : StableSteinberg.Group F →* StableSteinberg.Group F => h b)
    (barToSteinberg_left_inverse F)
  exact ha.symm.trans ((congrArg (barToSteinberg F) hab).trans hb)

/-- Proved integral-bar perfectness supplies surjectivity of the ORIGINAL universal lift. -/
theorem steinbergToBar_surjective : Function.Surjective (steinbergToBar F) := by
  let := integralBar_isPerfect (StableGeneralLinear.elementary F)
  apply MonoidHom.surjective_of_central_ker_of_surjective_comp (steinbergToBar F)
    (barProjection (ULift.{u} ℤ) (StableGeneralLinear.elementary F))
    (barProjection_ker_le_center (ULift.{u} ℤ) (StableGeneralLinear.elementary F))
  rw [steinbergToBar_over]
  exact StableSteinberg.toElementary_surjective F

/-- The original stable Steinberg group is the concrete native integral bar extension. -/
def steinbergBarEquiv : StableSteinberg.Group F ≃* ElementaryBarExtension F :=
  MulEquiv.ofBijective (steinbergToBar F) ⟨steinbergToBar_injective F, steinbergToBar_surjective F⟩

/-- Restrict the original universal lift to its original elementary-map kernel. -/
def steinbergKernelToBarKernel : (StableSteinberg.toElementary F).ker →*
    (barProjection (ULift.{u} ℤ) (StableGeneralLinear.elementary F)).ker where
  toFun a := ⟨steinbergToBar F a, by
    change barProjection (ULift.{u} ℤ) (StableGeneralLinear.elementary F) (steinbergToBar F a) = 1
    exact (congrArg (fun p : StableSteinberg.Group F →* StableGeneralLinear.elementary F => p a)
      (steinbergToBar_over F)).trans a.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul (steinbergToBar F) a.val b.val)

/-- The exact restricted original lift is bijective. -/
theorem steinbergKernelToBarKernel_bijective :
    Function.Bijective (steinbergKernelToBarKernel F) := by
  constructor
  · intro a b h
    apply Subtype.ext
    exact steinbergToBar_injective F (congrArg Subtype.val h)
  · intro a
    obtain ⟨b, hb⟩ := steinbergToBar_surjective F a.val
    have hk : StableSteinberg.toElementary F b = 1 := by
      rw [← steinbergToBar_over]
      change barProjection (ULift.{u} ℤ) (StableGeneralLinear.elementary F) (steinbergToBar F b) = 1
      rw [hb]
      exact a.property
    exact ⟨⟨b, hk⟩, Subtype.ext hb⟩

/-- The actual stable Steinberg kernel is the existing native group H-two with lifted integers.
This theorem makes no identification with singular H-two or the original completion Pi two. -/
def nativeSchurKernelEquiv : (StableSteinberg.toElementary F).ker ≃*
    Multiplicative (groupHomology.H2
      (coefficients (ULift.{u} ℤ) (StableGeneralLinear.elementary F))) :=
  (MulEquiv.ofBijective (steinbergKernelToBarKernel F)
    (steinbergKernelToBarKernel_bijective F)).trans
      (barKernelEquiv (ULift.{u} ℤ) (StableGeneralLinear.elementary F)).symm

end Quillen.StableSteinberg.Schur

end

section

open groupHomology.IntegralBar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Finsupp
open scoped commutatorElement
namespace Quillen.StableSteinberg.Schur

variable (F : Type u) [Field F]

/-- Commuting original elementary images put the actual Steinberg commutator in its kernel. -/
def steinbergCommutatorKernel (a b : StableSteinberg.Group F)
    (hab : Commute (StableSteinberg.toElementary F a) (StableSteinberg.toElementary F b)) :
    (StableSteinberg.toElementary F).ker :=
  ⟨⁅a, b⁆, by
    change StableSteinberg.toElementary F ⁅a, b⁆ = 1
    rw [map_commutatorElement]
    exact hab.commutator_eq⟩

/-- The original stable Steinberg Schur map evaluates those commutators to minus the
literal bar torus cycle. No homotopy-fiber or ordered-symbol identification is assumed. -/
theorem nativeSchurKernelEquiv_commutator (a b : StableSteinberg.Group F)
    (hab : Commute (StableSteinberg.toElementary F a) (StableSteinberg.toElementary F b)) :
    nativeSchurKernelEquiv F (steinbergCommutatorKernel F a b hab) =
      Multiplicative.ofAdd (-groupHomology.H2π
        (coefficients (ULift.{u} ℤ) (StableGeneralLinear.elementary F))
        (torusCycle (ULift.{u} ℤ) (StableGeneralLinear.elementary F)
          (StableSteinberg.toElementary F a) (StableSteinberg.toElementary F b) hab)) := by
  have hbase (a : StableSteinberg.Group F) :
      (steinbergToBar F a).base = StableSteinberg.toElementary F a :=
    congrArg (fun p : StableSteinberg.Group F →* StableGeneralLinear.elementary F => p a)
      (steinbergToBar_over F)
  have hc : Commute (steinbergToBar F a).base (steinbergToBar F b).base := by
    rw [hbase, hbase]
    exact hab
  change Multiplicative.ofAdd (steinbergToBar F ⁅a, b⁆).homology = _
  rw [map_commutatorElement]
  have h := congrArg BarExtension.homology
    (barCommutator (ULift.{u} ℤ) (StableGeneralLinear.elementary F)
      (steinbergToBar F a) (steinbergToBar F b) hc)
  exact congrArg Multiplicative.ofAdd (by simpa only [hbase] using h)

end Quillen.StableSteinberg.Schur

end

section

open groupHomology.IntegralBar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open scoped commutatorElement
namespace Quillen.StableSteinberg.Schur
variable (F : Type u) [Field F]

/-- The actual rank-three torus elements have commuting original elementary images. -/
theorem elementary_torus_commute (a b : Fˣ) :
    Commute (StableSteinberg.toElementary F (StableSteinberg.h a))
      (StableSteinberg.toElementary F (StableSteinberg.h02 b)) := by
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement, StableSteinberg.commutator_h_h02]
  exact (StableSteinberg.torusDefectKernel a b).property

/-- The native Schur kernel equivalence sends each ORIGINAL torus defect to minus the
literal bar torus cycle of its original rank-three elementary images. -/
theorem nativeSchurKernelEquiv_torusDefect (a b : Fˣ) :
    nativeSchurKernelEquiv F (StableSteinberg.torusDefectKernel a b) =
      Multiplicative.ofAdd (-groupHomology.H2π
        (coefficients (ULift.{u} ℤ) (StableGeneralLinear.elementary F))
        (torusCycle (ULift.{u} ℤ) (StableGeneralLinear.elementary F)
          (StableSteinberg.toElementary F (StableSteinberg.h a))
          (StableSteinberg.toElementary F (StableSteinberg.h02 b))
          (elementary_torus_commute F a b))) := by
  have he : steinbergCommutatorKernel F (StableSteinberg.h a) (StableSteinberg.h02 b)
      (elementary_torus_commute F a b) = StableSteinberg.torusDefectKernel a b :=
    Subtype.ext (StableSteinberg.commutator_h_h02 a b)
  rw [← he]
  exact nativeSchurKernelEquiv_commutator F _ _ (elementary_torus_commute F a b)

end Quillen.StableSteinberg.Schur

end

section

open groupHomology.IntegralBar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open scoped commutatorElement
namespace Quillen.StableSteinberg.Schur
variable (F : Type u) [Field F] {G : Type (max u v)} [_root_.Group G] [_root_.Group.IsPerfect G]
  (e : G ≃* StableGeneralLinear.elementary F)

/-- The actual bar projection followed by the displayed ORIGINAL elementary identification. -/
def barProjectionAlong : IntegralBarExtension G →* StableGeneralLinear.elementary F :=
  e.toMonoidHom.comp (barProjection (ULift.{max u v} ℤ) G)

/-- The projection along the actual identification remains surjective. -/
theorem barProjectionAlong_surjective : Function.Surjective (barProjectionAlong F e) :=
  e.surjective.comp (barProjection_surjective (ULift.{max u v} ℤ) G)

/-- Its kernel is unchanged by the actual group isomorphism. -/
theorem barProjectionAlong_central :
    (barProjectionAlong F e).ker ≤ Subgroup.center (IntegralBarExtension G) := by
  rw [barProjectionAlong, MonoidHom.ker_comp_of_injective _ _ e.injective]
  exact barProjection_ker_le_center (ULift.{max u v} ℤ) G

/-- The ORIGINAL Steinberg projection lifted to the same universe as the actual cover group. -/
def liftedSteinbergProjection : ULift.{max u v} (StableSteinberg.Group F) →* G :=
  e.symm.toMonoidHom.comp
    ((StableSteinberg.toElementary F).comp (MulEquiv.ulift.toMonoidHom))

omit [_root_.Group.IsPerfect G] in
/-- The lifted projection is genuinely surjective. -/
theorem liftedSteinbergProjection_surjective :
    Function.Surjective (liftedSteinbergProjection F e) :=
  e.symm.surjective.comp
    ((StableSteinberg.toElementary_surjective F).comp MulEquiv.ulift.surjective)

omit [_root_.Group.IsPerfect G] in
/-- Only the genuine ULift group isomorphism is used to transport original Steinberg centrality. -/
theorem liftedSteinbergProjection_central :
    (liftedSteinbergProjection F e).ker ≤
      Subgroup.center (ULift.{max u v} (StableSteinberg.Group F)) := by
  intro a ha
  have ha' : StableSteinberg.toElementary F a.down = 1 := e.symm.map_eq_one_iff.mp ha
  have hz := StableSteinberg.ker_toElementary_le_center F ha'
  apply Subgroup.mem_center_iff.mpr
  intro b
  apply MulEquiv.ulift.injective
  exact Subgroup.mem_center_iff.mp hz b.down

/-- The original universal Steinberg map into the bar extension of the actual higher-universe G. -/
def steinbergToBarAlong : StableSteinberg.Group F →* IntegralBarExtension G :=
  StableSteinberg.liftToCentralExtension F (barProjectionAlong F e)
    (barProjectionAlong_surjective F e) (barProjectionAlong_central F e)

/-- The actual original elementary projection is retained. -/
theorem steinbergToBarAlong_over :
    (barProjectionAlong F e).comp (steinbergToBarAlong F e) = StableSteinberg.toElementary F :=
  StableSteinberg.liftToCentralExtension_over F (barProjectionAlong F e)
    (barProjectionAlong_surjective F e) (barProjectionAlong_central F e)

/-- The constructed bar lift followed by the genuine ULift inverse returns to ORIGINAL St. -/
def barToSteinbergAlong : IntegralBarExtension G →* StableSteinberg.Group F :=
  MulEquiv.ulift.toMonoidHom.comp
    (barLift (liftedSteinbergProjection F e) (liftedSteinbergProjection_surjective F e)
      (liftedSteinbergProjection_central F e))

/-- The reverse map has its actual original elementary projection. -/
theorem barToSteinbergAlong_over :
    (StableSteinberg.toElementary F).comp (barToSteinbergAlong F e) = barProjectionAlong F e := by
  apply MonoidHom.ext
  intro a
  have h := congrArg (fun p : IntegralBarExtension G →* G => p a)
    (barLift_over (liftedSteinbergProjection F e) (liftedSteinbergProjection_surjective F e)
      (liftedSteinbergProjection_central F e))
  have he := congrArg e h
  simpa only [barToSteinbergAlong, liftedSteinbergProjection, barProjectionAlong,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using he

/-- Original Steinberg uniqueness proves an actual left inverse across these universes. -/
theorem barToSteinbergAlong_left_inverse :
    (barToSteinbergAlong F e).comp (steinbergToBarAlong F e) =
      MonoidHom.id (StableSteinberg.Group F) := by
  apply StableSteinberg.liftToCentralExtension_unique F (StableSteinberg.toElementary F)
    (StableSteinberg.ker_toElementary_le_center F)
  · calc
      _ = ((StableSteinberg.toElementary F).comp (barToSteinbergAlong F e)).comp
          (steinbergToBarAlong F e) := rfl
      _ = (barProjectionAlong F e).comp (steinbergToBarAlong F e) :=
        congrArg (fun p => p.comp (steinbergToBarAlong F e)) (barToSteinbergAlong_over F e)
      _ = _ := steinbergToBarAlong_over F e
  · rfl

/-- The original map is injective by its constructed left inverse. -/
theorem steinbergToBarAlong_injective : Function.Injective (steinbergToBarAlong F e) := by
  intro a b hab
  have ha := congrArg (fun p : StableSteinberg.Group F →* StableSteinberg.Group F => p a)
    (barToSteinbergAlong_left_inverse F e)
  have hb := congrArg (fun p : StableSteinberg.Group F →* StableSteinberg.Group F => p b)
    (barToSteinbergAlong_left_inverse F e)
  exact ha.symm.trans ((congrArg (barToSteinbergAlong F e) hab).trans hb)

/-- Proved actual integral-bar perfectness supplies surjectivity of the original lift. -/
theorem steinbergToBarAlong_surjective : Function.Surjective (steinbergToBarAlong F e) := by
  let := integralBar_isPerfect G
  apply MonoidHom.surjective_of_central_ker_of_surjective_comp (steinbergToBarAlong F e)
    (barProjectionAlong F e) (barProjectionAlong_central F e)
  rw [steinbergToBarAlong_over]
  exact StableSteinberg.toElementary_surjective F

/-- The actual base coordinate is precisely the original elementary image
under the supplied inverse. -/
theorem steinbergToBarAlong_base (a : StableSteinberg.Group F) :
    (steinbergToBarAlong F e a).base = e.symm (StableSteinberg.toElementary F a) := by
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  exact congrArg (fun p : StableSteinberg.Group F →* StableGeneralLinear.elementary F => p a)
    (steinbergToBarAlong_over F e)

/-- Restrict the actual lift to the original elementary-map kernel and the actual G-bar kernel. -/
def schurAlongKernelMap : (StableSteinberg.toElementary F).ker →*
    (barProjection (ULift.{max u v} ℤ) G).ker where
  toFun a := ⟨steinbergToBarAlong F e a, by
    change (steinbergToBarAlong F e a).base = 1
    rw [steinbergToBarAlong_base, a.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul (steinbergToBarAlong F e) a.val b.val)

/-- Both directions of the original restricted map are proved. -/
theorem schurAlongKernelMap_bijective : Function.Bijective (schurAlongKernelMap F e) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact steinbergToBarAlong_injective F e (congrArg Subtype.val hab)
  · intro a
    obtain ⟨b, hb⟩ := steinbergToBarAlong_surjective F e a.val
    have hk : StableSteinberg.toElementary F b = 1 := by
      rw [← steinbergToBarAlong_over F e]
      change e ((steinbergToBarAlong F e b).base) = 1
      rw [hb, show a.val.base = 1 from a.property, map_one]
    exact ⟨⟨b, hk⟩, Subtype.ext hb⟩

/-- The ORIGINAL Steinberg kernel identifies with native H-two of the SAME actual cover group G. -/
def nativeSchurAlongEquiv : (StableSteinberg.toElementary F).ker ≃*
    Multiplicative (groupHomology.H2 (coefficients (ULift.{max u v} ℤ) G)) :=
  (MulEquiv.ofBijective (schurAlongKernelMap F e) (schurAlongKernelMap_bijective F e)).trans
    (barKernelEquiv (ULift.{max u v} ℤ) G).symm

omit [_root_.Group.IsPerfect G] in
/-- Original commuting elementary images have the actual commuting preimages in G. -/
theorem preimage_commute (a b : StableSteinberg.Group F)
    (hab : Commute (StableSteinberg.toElementary F a) (StableSteinberg.toElementary F b)) :
    Commute (e.symm (StableSteinberg.toElementary F a))
      (e.symm (StableSteinberg.toElementary F b)) := hab.map e.symm.toMonoidHom

/-- The same-universe bar marking retains the original St commutator and its exact negative sign. -/
theorem nativeSchurAlongEquiv_commutator (a b : StableSteinberg.Group F)
    (hab : Commute (StableSteinberg.toElementary F a) (StableSteinberg.toElementary F b)) :
    nativeSchurAlongEquiv F e (steinbergCommutatorKernel F a b hab) =
      Multiplicative.ofAdd (-groupHomology.H2π (coefficients (ULift.{max u v} ℤ) G)
        (torusCycle (ULift.{max u v} ℤ) G (e.symm (StableSteinberg.toElementary F a))
          (e.symm (StableSteinberg.toElementary F b)) (preimage_commute F e a b hab))) := by
  have hc : Commute (steinbergToBarAlong F e a).base (steinbergToBarAlong F e b).base := by
    rw [steinbergToBarAlong_base, steinbergToBarAlong_base]
    exact preimage_commute F e a b hab
  change Multiplicative.ofAdd (steinbergToBarAlong F e ⁅a, b⁆).homology = _
  rw [map_commutatorElement]
  have h := congrArg BarExtension.homology
    (barCommutator (ULift.{max u v} ℤ) G
      (steinbergToBarAlong F e a) (steinbergToBarAlong F e b) hc)
  exact congrArg Multiplicative.ofAdd (by simpa only [steinbergToBarAlong_base] using h)

/-- The actual SAME-G Schur comparison with the original integral-module H-two interface. -/
def integerSchurAlongEquiv : (StableSteinberg.toElementary F).ker ≃*
    Multiplicative (integerBarH2 G) :=
  (nativeSchurAlongEquiv F e).trans (integerBarH2AddEquiv G).symm.toMultiplicative

omit [_root_.Group.IsPerfect G] in
include e in
/-- The supplied original group isomorphism itself discharges perfectness of G. -/
theorem isPerfect_of_elementaryEquiv : _root_.Group.IsPerfect G :=
  _root_.Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

end Quillen.StableSteinberg.Schur

end

section

open groupHomology.IntegralBar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace Quillen.StableSteinberg.Schur
variable (F : Type u) [Field F] {G : Type (max u v)} [_root_.Group G] [_root_.Group.IsPerfect G]
  (e : G ≃* StableGeneralLinear.elementary F)

/-- The actual bar torus of the two original elementary torus elements, in the SAME cover group. -/
def originalTorusAlong (a b : Fˣ) : groupHomology.cycles₂ (coefficients (ULift.{max u v} ℤ) G) :=
  torusCycle (ULift.{max u v} ℤ) G
    (e.symm (StableSteinberg.toElementary F (StableSteinberg.h a)))
    (e.symm (StableSteinberg.toElementary F (StableSteinberg.h02 b)))
    (preimage_commute F e _ _ (elementary_torus_commute F a b))

/-- The original kernel element has the same proved negative native bar marking in this universe. -/
theorem nativeSchurAlongEquiv_torusDefect (a b : Fˣ) :
    nativeSchurAlongEquiv F e (StableSteinberg.torusDefectKernel a b) =
      Multiplicative.ofAdd (-groupHomology.H2π (coefficients (ULift.{max u v} ℤ) G)
        (originalTorusAlong F e a b)) := by
  have he : steinbergCommutatorKernel F (StableSteinberg.h a) (StableSteinberg.h02 b)
      (elementary_torus_commute F a b) = StableSteinberg.torusDefectKernel a b :=
    Subtype.ext (StableSteinberg.commutator_h_h02 a b)
  rw [← he]
  exact nativeSchurAlongEquiv_commutator F e _ _ (elementary_torus_commute F a b)

/-- The actual integral-module Schur equivalence sends each original torus defect to the
negative ORIGINAL integral bar torus-cycle class, with no topological transgression assumed. -/
theorem integerSchurAlongEquiv_torusDefect (a b : Fˣ) :
    integerSchurAlongEquiv F e (StableSteinberg.torusDefectKernel a b) =
      Multiplicative.ofAdd (-integerBarCycleClass G (originalTorusAlong F e a b)) := by
  apply Multiplicative.toAdd.injective
  apply (integerBarH2AddEquiv G).injective
  change integerBarH2AddEquiv G ((integerBarH2AddEquiv G).symm
      (nativeSchurAlongEquiv F e (StableSteinberg.torusDefectKernel a b)).toAdd) =
    integerBarH2AddEquiv G (-integerBarCycleClass G (originalTorusAlong F e a b))
  rw [AddEquiv.apply_symm_apply, map_neg]
  have hc : integerBarH2AddEquiv G (integerBarCycleClass G (originalTorusAlong F e a b)) =
      groupHomology.H2π (coefficients (ULift.{max u v} ℤ) G) (originalTorusAlong F e a b) :=
    integerBarH2Iso_cycleClass G _
  rw [hc]
  exact congrArg Multiplicative.toAdd (nativeSchurAlongEquiv_torusDefect F e a b)

end Quillen.StableSteinberg.Schur

end

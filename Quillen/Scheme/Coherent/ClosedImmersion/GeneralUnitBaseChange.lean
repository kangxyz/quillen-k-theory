import Quillen.Scheme.Coherent.ClosedImmersion.GeneralPullback

/-!
# Unit-compatible closed pullback and open base change

The actual pushforward composition square is transported twice by mates.
The resulting pullback square is an isomorphism by the iterated-mates
identity. Its unit square is therefore canonical, rather than inferred from
an arbitrary isomorphism between the four underlying functors.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme.ClosedImmersion.General
open Scheme.Modules
variable {Z V X : Scheme.{u}} (i : Z ⟶ X) (a : V ⟶ X) [IsOpenImmersion a]

/-- The actual direct-image square for a geometric pullback diagram. -/
def pushforwardSquare :
    pushforward (pullback.fst i a) ⋙ pushforward i ≅
      pushforward (pullback.snd i a) ⋙ pushforward a :=
  pushforwardComp (pullback.fst i a) i ≪≫
    pushforwardCongr (pullback.condition (f := i) (g := a)) ≪≫
      (pushforwardComp (pullback.snd i a) a).symm

/-- Actual open base change is the mate of the actual composition square. -/
theorem openBaseChange_eq_mate :
    (openBaseChange i a).hom =
      (mateEquiv (restrictAdjunction (pullback.fst i a)) (restrictAdjunction a)).symm
        (pushforwardSquare i a).hom := by
  ext M
  simp only [openBaseChange, pushforwardSquare, mateEquiv, Equiv.coe_fn_symm_mk,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.map_comp, Category.id_comp,
    Category.assoc, asIso_hom]
  rfl

/-- The pullback/open-restriction square defined as the mate of genuine
open base change. This definition retains the adjunction unit square. -/
def pullbackBaseChangeMate :
    restrictFunctor a ⋙ Scheme.Modules.pullback (pullback.snd i a) ⟶
      Scheme.Modules.pullback i ⋙ restrictFunctor (pullback.fst i a) :=
  (mateEquiv (pullbackPushforwardAdjunction i)
    (pullbackPushforwardAdjunction (pullback.snd i a))).symm (openBaseChange i a).hom

/-- The second mate is an isomorphism because it is the conjugate of the
original isomorphism between the composite right adjoints. -/
instance pullbackBaseChangeMate_isIso : IsIso (pullbackBaseChangeMate i a) := by
  rw [pullbackBaseChangeMate, openBaseChange_eq_mate]
  rw [iterated_mateEquiv_conjugateEquiv_symm
    (pullbackPushforwardAdjunction i)
    (pullbackPushforwardAdjunction (pullback.snd i a))
    (restrictAdjunction a) (restrictAdjunction (pullback.fst i a))]
  change IsIso ((conjugateEquiv
    ((pullbackPushforwardAdjunction i).comp (restrictAdjunction (pullback.fst i a)))
    ((restrictAdjunction a).comp (pullbackPushforwardAdjunction (pullback.snd i a)))).symm
      (pushforwardSquare i a).hom)
  infer_instance

/-- The exact unit compatibility furnished by the mates correspondence. -/
theorem unit_openBaseChange (M : X.Modules) :
    (restrictFunctor a).map ((pullbackPushforwardAdjunction i).unit.app M) ≫
      (openBaseChange i a).hom.app ((Scheme.Modules.pullback i).obj M) =
    (pullbackPushforwardAdjunction (pullback.snd i a)).unit.app
      ((restrictFunctor a).obj M) ≫
        (pushforward (pullback.snd i a)).map ((pullbackBaseChangeMate i a).app M) :=
  unit_mateEquiv_symm (pullbackPushforwardAdjunction i)
    (pullbackPushforwardAdjunction (pullback.snd i a)) (openBaseChange i a).hom M

/-- The local codomain identification of the actual global unit. -/
def unitTargetOpenBaseChange (M : X.Modules) :
    (restrictFunctor a).obj ((pushforward i).obj ((Scheme.Modules.pullback i).obj M)) ≅
      (pushforward (pullback.snd i a)).obj
        ((Scheme.Modules.pullback (pullback.snd i a)).obj ((restrictFunctor a).obj M)) :=
  (openBaseChange i a).app ((Scheme.Modules.pullback i).obj M) ≪≫
    (pushforward (pullback.snd i a)).mapIso ((asIso (pullbackBaseChangeMate i a)).app M).symm

/-- With this canonical codomain comparison, the restricted unit is
literally the actual local unit. -/
theorem unit_comp_unitTargetOpenBaseChange (M : X.Modules) :
    (restrictFunctor a).map ((pullbackPushforwardAdjunction i).unit.app M) ≫
      (unitTargetOpenBaseChange i a M).hom =
        (pullbackPushforwardAdjunction (pullback.snd i a)).unit.app
          ((restrictFunctor a).obj M) := by
  dsimp only [unitTargetOpenBaseChange, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, asIso_inv]
  simp only [NatIso.isIso_inv_app]
  change (restrictFunctor a).map ((pullbackPushforwardAdjunction i).unit.app M) ≫
    (openBaseChange i a).hom.app ((Scheme.Modules.pullback i).obj M) ≫
    (pushforward (pullback.snd i a)).map (inv ((pullbackBaseChangeMate i a).app M)) = _
  rw [← Category.assoc, unit_openBaseChange, Category.assoc, ← Functor.map_comp]
  simp only [IsIso.hom_inv_id]
  rw [CategoryTheory.Functor.map_id]
  exact CategoryTheory.Category.comp_id _

section Coherent
variable [IsLocallyNoetherian Z] [IsLocallyNoetherian X] [IsLocallyNoetherian V]
  [IsClosedImmersion i]

/-- The unit codomain comparison on the actual coherent categories. -/
def coherentUnitTargetOpenBaseChange (M : Coherent X) :
    (coherentRestriction a).obj ((coherentPushforward i).obj ((coherentPullback i).obj M)) ≅
      (coherentPushforward (pullback.snd i a)).obj
        ((coherentPullback (pullback.snd i a)).obj ((coherentRestriction a).obj M)) :=
  (coherent V).fullyFaithfulι.preimageIso (unitTargetOpenBaseChange i a M.obj)

/-- The comparison retains exactly the actual coherent-adjunction unit. -/
theorem coherentUnit_comp_target (M : Coherent X) :
    (coherentRestriction a).map ((coherentAdjunction i).unit.app M) ≫
      (coherentUnitTargetOpenBaseChange i a M).hom =
        (coherentAdjunction (pullback.snd i a)).unit.app ((coherentRestriction a).obj M) := by
  apply ObjectProperty.hom_ext
  change (restrictFunctor a).map (((coherentAdjunction i).unit.app M).hom) ≫
    (unitTargetOpenBaseChange i a M.obj).hom =
      ((coherentAdjunction (pullback.snd i a)).unit.app ((coherentRestriction a).obj M)).hom
  rw [coherentAdjunction_unit_hom, coherentAdjunction_unit_hom]
  exact unit_comp_unitTargetOpenBaseChange i a M.obj

/-- Actual ideal-kernel formation commutes with open restriction. -/
def kernelUnitOpenBaseChange (M : Coherent X) :
    (coherentRestriction a).obj (kernel ((coherentAdjunction i).unit.app M)) ≅
      kernel ((coherentAdjunction (pullback.snd i a)).unit.app
        ((coherentRestriction a).obj M)) :=
  PreservesKernel.iso (coherentRestriction a) _ ≪≫
    kernel.mapIso _ _ (Iso.refl _) (coherentUnitTargetOpenBaseChange i a M)
      (by simpa only [Iso.refl_hom, Category.id_comp] using coherentUnit_comp_target i a M)

end Coherent

end Quillen.CoherentScheme.ClosedImmersion.General

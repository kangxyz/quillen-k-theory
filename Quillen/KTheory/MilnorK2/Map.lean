/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.MilnorK2.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Field maps on the Milnor tensor quotient

Field homomorphisms induce integer-linear and additive maps on the existing
Milnor quotient. These maps have their literal symbol values and preserve
identity and composition.

Migrated from `R5Lab/KTheory/MilnorK2/Map.lean` at R5 commit
`d79a2e5af436f59fdfebdd8770cd27c20f850e27`, source SHA-256
`f10c7f41c9286b07f1ae6e8c5742940dcf559fe0338735dba990312d84421a2c`.
The tensor, Steinberg span, quotient, symbol, and field-map definitions retain
their original meaning. The marked Matsumoto comparison remains separate.
`unitsLinear` absorbs the original Milnor-specific units wrapper, SHA-256
`4a75c288cf0ae65b9a3e4b8552596341e7f0b3f2ae9a146efdf5726897f628ab`.
-/
@[expose] public section

namespace Quillen.MilnorK2

variable (K : Type*) [Field K]

variable {K}

variable {A : Type*} [AddCommGroup A]

variable {L : Type*} [Field L]

/-- The integer-linear map on units induced by a field homomorphism. -/
def unitsLinear (f : K →+* L) : UnitsAdd K →ₗ[ℤ] UnitsAdd L :=
  (Units.map f.toMonoidHom).toAdditive.toIntLinearMap

/-- Field functoriality descends after proving preservation of the Steinberg generators. -/
def map (f : K →+* L) : K2 K →ₗ[ℤ] K2 L :=
  lift ((symbolBilinear L).compl₁₂ (unitsLinear f) (unitsLinear f)) (by
    intro a b hab
    apply steinberg
    change f (a : K) + f (b : K) = 1
    rw [← map_add, hab, map_one])

/-- A field map sends `{a,b}` to the symbol of the image entries. -/
@[simp] theorem map_symbol (f : K →+* L) (a b : Kˣ) :
    map f (symbol a b) = symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) := rfl

/-- The field identity induces the identity on Milnor K₂. -/
@[simp] theorem map_id : map (RingHom.id K) = LinearMap.id := by
  apply linearMap_ext
  intro a b
  simp [map_symbol, Units.map]

variable {M : Type*} [Field M]

/-- Composition of field maps is preserved by Milnor K₂. -/
theorem map_comp (f : K →+* L) (g : L →+* M) :
    map (g.comp f) = (map g).comp (map f) := by
  apply linearMap_ext
  intro a b
  rfl

/-- The additive view of the existing field-induced integer-linear map. -/
def mapAdd (f : K →+* L) : K2 K →+ K2 L := (map f).toAddMonoidHom

/-- The additive field map takes symbols to symbols of the field images. -/
@[simp] theorem mapAdd_symbol (f : K →+* L) (a b : Kˣ) :
    mapAdd f (symbol a b) =
      symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) :=
  map_symbol f a b

/-- The additive field map preserves the identity field homomorphism. -/
@[simp] theorem mapAdd_id : mapAdd (RingHom.id K) = AddMonoidHom.id (K2 K) :=
  congrArg (fun h : K2 K →ₗ[ℤ] K2 K => h.toAddMonoidHom) map_id

/-- The additive field map preserves composition of field homomorphisms. -/
theorem mapAdd_comp (f : K →+* L) (g : L →+* M) :
    mapAdd (g.comp f) = (mapAdd g).comp (mapAdd f) :=
  congrArg (fun h : K2 K →ₗ[ℤ] K2 M => h.toAddMonoidHom) (map_comp f g)

end Quillen.MilnorK2

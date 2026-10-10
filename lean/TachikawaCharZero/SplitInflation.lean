import TachikawaCharZero.TensorProfile
import TachikawaCharZero.TauPowers
import TachikawaCharZero.ExtTransport
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! Split inflation provides actual Yoneda classes without choosing Künneth
coordinates. The two tensor factors retract along the one-dimensional
character. Cross-factor interchange and negative Tate comparison remain
separate obligations. -/
namespace TachikawaCharZero.SplitInflation
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra

section ExactRetract
variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  [HasExt C] [HasExt D]
  (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (e : F ⋙ G ≅ 𝟭 C)

theorem restore_ext {X Y : C} {n : ℕ} (x : Ext X Y n) :
    (Ext.mk₀ (e.inv.app X)).comp
      (((x.mapExactFunctor F).mapExactFunctor G).comp
        (Ext.mk₀ (e.hom.app Y)) (add_zero n)) (zero_add n) = x := by
  rw [← Ext.comp_mapExactFunctor]
  rw [Ext.mapExactFunctor_comp_mk₀_natTransApp x e.hom]
  simp only [Ext.id_mapExactFunctor, Ext.mk₀_comp_mk₀_assoc,
    Iso.inv_hom_id_app, Ext.mk₀_id_comp]

include G e in
theorem map_ext_injective (X Y : C) (n : ℕ) :
    Function.Injective (Ext.mapExactFunctor F (X := X) (Y := Y) (n := n)) := by
  intro x y h
  rw [← restore_ext F G e x, ← restore_ext F G e y, h]
end ExactRetract

open Induced TensorProfile OAI.Tachikawa

def projectionLeft : E →ₐ[ℚ] T :=
  (Algebra.TensorProduct.rid ℚ ℚ T).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id ℚ T) characterT)

def projectionRight : E →ₐ[ℚ] T :=
  (Algebra.TensorProduct.lid ℚ T).toAlgHom.comp
    (Algebra.TensorProduct.map characterT (AlgHom.id ℚ T))

def inclusionLeft : T →ₐ[ℚ] E := Algebra.TensorProduct.includeLeft
def inclusionRight : T →ₐ[ℚ] E := Algebra.TensorProduct.includeRight

theorem projectionLeft_tmul (a b : T) :
    projectionLeft (a ⊗ₜ[ℚ] b) = characterT b • a := by
  simp [projectionLeft]

theorem projectionRight_tmul (a b : T) :
    projectionRight (a ⊗ₜ[ℚ] b) = characterT a • b := by
  simp [projectionRight]

theorem projectionLeft_section : projectionLeft.comp inclusionLeft = AlgHom.id ℚ T := by
  apply AlgHom.ext
  intro a
  change projectionLeft (a ⊗ₜ[ℚ] 1) = a
  simp [projectionLeft_tmul]

theorem projectionRight_section : projectionRight.comp inclusionRight = AlgHom.id ℚ T := by
  apply AlgHom.ext
  intro a
  change projectionRight (1 ⊗ₜ[ℚ] a) = a
  simp [projectionRight_tmul]

abbrev inflateLeft := AlgebraInduction.res projectionLeft
abbrev inflateRight := AlgebraInduction.res projectionRight
abbrev restrictLeft := AlgebraInduction.res inclusionLeft
abbrev restrictRight := AlgebraInduction.res inclusionRight

def retractLeft : inflateLeft ⋙ restrictLeft ≅ 𝟭 (ModuleCat T) :=
  (ModuleCat.restrictScalarsComp' inclusionLeft.toRingHom projectionLeft.toRingHom
    (RingHom.id T) (congrArg AlgHom.toRingHom projectionLeft_section).symm).symm ≪≫
      ModuleCat.restrictScalarsId T

def retractRight : inflateRight ⋙ restrictRight ≅ 𝟭 (ModuleCat T) :=
  (ModuleCat.restrictScalarsComp' inclusionRight.toRingHom projectionRight.toRingHom
    (RingHom.id T) (congrArg AlgHom.toRingHom projectionRight_section).symm).symm ≪≫
      ModuleCat.restrictScalarsId T

theorem inflateLeft_ext_injective (M N : ModuleCat T) (n : ℕ) :
    Function.Injective (Ext.mapExactFunctor inflateLeft (X := M) (Y := N) (n := n)) :=
  map_ext_injective inflateLeft restrictLeft retractLeft M N n

theorem inflateRight_ext_injective (M N : ModuleCat T) (n : ℕ) :
    Function.Injective (Ext.mapExactFunctor inflateRight (X := M) (Y := N) (n := n)) :=
  map_ext_injective inflateRight restrictRight retractRight M N n

def tensorCharacter : E →ₐ[ℚ] ℚ :=
  (Algebra.TensorProduct.lid ℚ ℚ).toAlgHom.comp
    (Algebra.TensorProduct.map characterT characterT)

theorem tensorCharacter_tmul (a b : T) :
    tensorCharacter (a ⊗ₜ[ℚ] b) = characterT a * characterT b := by
  simp [tensorCharacter, smul_eq_mul]

theorem character_projectionLeft : characterT.comp projectionLeft = tensorCharacter := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro a b
  change characterT (projectionLeft (a ⊗ₜ[ℚ] b)) = tensorCharacter (a ⊗ₜ[ℚ] b)
  simp [projectionLeft_tmul, tensorCharacter_tmul, smul_eq_mul, mul_comm]

theorem character_projectionRight : characterT.comp projectionRight = tensorCharacter := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro a b
  change characterT (projectionRight (a ⊗ₜ[ℚ] b)) = tensorCharacter (a ⊗ₜ[ℚ] b)
  simp [projectionRight_tmul, tensorCharacter_tmul, smul_eq_mul]

def underlying : X₂ ≃ₗ[ℚ] (sCanon ⊗[ℚ] sCanon) :=
  OuterTensor.underlyingEquiv sCanon sCanon

def pureTensor (x y : sCanon) : X₂ := underlying.symm (x ⊗ₜ[ℚ] y)

theorem groundEquiv_tmul (x y : sCanon) :
    groundEquiv (pureTensor x y) = (show ℚ from x) * (show ℚ from y) := by
  change (TensorProduct.lid ℚ ℚ)
    (TensorProduct.map simpleGroundEquiv.toLinearMap simpleGroundEquiv.toLinearMap
      (x ⊗ₜ[ℚ] y)) = _
  rw [TensorProduct.map_tmul, TensorProduct.lid_tmul]
  rfl

theorem pureTensor_action (a b : T) (x y : sCanon) :
    (a ⊗ₜ[ℚ] b) • pureTensor x y = pureTensor (a • x) (b • y) :=
  OuterTensor.tmul_smul_tmul ℚ T T sCanon sCanon a b x y

theorem groundEquiv_action (r : E) (z : X₂) :
    groundEquiv (r • z) = tensorCharacter r * groundEquiv z := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => simp [add_smul, hr, hs, add_mul]
  | tmul a b =>
    obtain ⟨w, rfl⟩ := underlying.symm.surjective z
    induction w using TensorProduct.inductionOn with
    | add x y hx hy =>
      have hadd : (a ⊗ₜ[ℚ] b) • underlying.symm (x+y) =
          (a ⊗ₜ[ℚ] b) • underlying.symm x +
            (a ⊗ₜ[ℚ] b) • underlying.symm y :=
        (OuterTensor.action ℚ T T sCanon sCanon (a ⊗ₜ[ℚ] b)).map_add x y
      rw [hadd, map_add, map_add, map_add, mul_add, hx, hy]
    | tmul x y =>
      change groundEquiv ((a ⊗ₜ[ℚ] b) • pureTensor x y) =
        tensorCharacter (a ⊗ₜ[ℚ] b) * groundEquiv (pureTensor x y)
      rw [pureTensor_action, groundEquiv_tmul, groundEquiv_tmul, tensorCharacter_tmul]
      change (characterT a * (show ℚ from x)) * (characterT b * (show ℚ from y)) = _
      ring

def inflatedIso (π : E →ₐ[ℚ] T) (hπ : characterT.comp π = tensorCharacter) :
    (AlgebraInduction.res π).obj X ≅ X₂ :=
  (show (AlgebraInduction.res π).obj X ≃ₗ[E] X₂ from
    { toFun := fun z => groundEquiv.symm (show ℚ from z)
      invFun := fun z => (show S from groundEquiv z)
      left_inv z := groundEquiv.apply_symm_apply z
      right_inv z := groundEquiv.symm_apply_apply z
      map_add' := fun x y => groundEquiv.symm.map_add x y
      map_smul' := by
        intro r z
        apply groundEquiv.injective
        rw [groundEquiv.apply_symm_apply, groundEquiv_action, groundEquiv.apply_symm_apply]
        change characterT (π r) * (show ℚ from z) = tensorCharacter r * (show ℚ from z)
        rw [← hπ]
        rfl }).toModuleIso

def inflatedLeftIso : inflateLeft.obj X ≅ X₂ :=
  inflatedIso projectionLeft character_projectionLeft
def inflatedRightIso : inflateRight.obj X ≅ X₂ :=
  inflatedIso projectionRight character_projectionRight

def externalMap (π : E →ₐ[ℚ] T) (hπ : characterT.comp π = tensorCharacter) (n : ℕ) :
    Ext X X n →ₗ[ℚ] Ext X₂ X₂ n :=
  (ExtTransport.conjugateLinearMap ℚ (inflatedIso π hπ) n).comp
    ((AlgebraInduction.res π).mapExtLinearMap ℚ X X n)

theorem externalMap_unit (π : E →ₐ[ℚ] T) (hπ : characterT.comp π = tensorCharacter) :
    externalMap π hπ 0 (Ext.mk₀ (𝟙 X)) = Ext.mk₀ (𝟙 X₂) := by
  change ExtTransport.conjugate _ ((Ext.mk₀ (𝟙 X)).mapExactFunctor _) = _
  rw [Ext.mapExactFunctor_mk₀, CategoryTheory.Functor.map_id, ExtTransport.conjugate_unit]

theorem externalMap_comp (π : E →ₐ[ℚ] T) (hπ : characterT.comp π = tensorCharacter)
    {a b c : ℕ} (x : Ext X X a) (y : Ext X X b) (h : a+b=c) :
    externalMap π hπ c (x.comp y h) =
      (externalMap π hπ a x).comp (externalMap π hπ b y) h := by
  change ExtTransport.conjugate _ ((x.comp y h).mapExactFunctor _) = _
  rw [Ext.mapExactFunctor_comp, ExtTransport.conjugate_comp]
  rfl

abbrev externalLeft (n : ℕ) := externalMap projectionLeft character_projectionLeft n
abbrev externalRight (n : ℕ) := externalMap projectionRight character_projectionRight n

theorem externalLeft_injective (n : ℕ) : Function.Injective (externalLeft n) :=
  (ExtTransport.conjugate_injective inflatedLeftIso n).comp (inflateLeft_ext_injective X X n)

theorem externalRight_injective (n : ℕ) : Function.Injective (externalRight n) :=
  (ExtTransport.conjugate_injective inflatedRightIso n).comp (inflateRight_ext_injective X X n)

def leftPower (m : ℕ) : Ext X₂ X₂ (3*m) := externalLeft (3*m) (tauPower m)
def rightPower (m : ℕ) : Ext X₂ X₂ (3*m) := externalRight (3*m) (tauPower m)

theorem leftPower_zero : leftPower 0 = Ext.mk₀ (𝟙 X₂) := by
  rw [leftPower, tauPower_zero]
  exact externalMap_unit _ _

theorem rightPower_zero : rightPower 0 = Ext.mk₀ (𝟙 X₂) := by
  rw [rightPower, tauPower_zero]
  exact externalMap_unit _ _

theorem external_zero_equal (x : Ext X X 0) : externalLeft 0 x = externalRight 0 x := by
  rw [eq_smul_tauPower 0 x, map_smul, map_smul]
  change (Induced.extMultiple 0 x) • leftPower 0 = (Induced.extMultiple 0 x) • rightPower 0
  rw [leftPower_zero, rightPower_zero]

theorem leftPower_comp (m n : ℕ) :
    (leftPower m).comp (leftPower n) (by omega) = leftPower (m+n) := by
  rw [leftPower, leftPower, ← externalMap_comp, tauPower_comp]
  rfl

theorem rightPower_comp (m n : ℕ) :
    (rightPower m).comp (rightPower n) (by omega) = rightPower (m+n) := by
  rw [rightPower, rightPower, ← externalMap_comp, tauPower_comp]
  rfl

theorem leftPower_ne_zero (m : ℕ) : leftPower m ≠ 0 := by
  intro h
  apply tauPower_ne_zero m
  apply externalLeft_injective (3*m)
  simpa only [leftPower, map_zero] using h

theorem rightPower_ne_zero (m : ℕ) : rightPower m ≠ 0 := by
  intro h
  apply tauPower_ne_zero m
  apply externalRight_injective (3*m)
  simpa only [rightPower, map_zero] using h

def alpha : Ext X₂ X₂ 3 := leftPower 1
def beta : Ext X₂ X₂ 3 := rightPower 1

theorem alpha_eq_inflated_tau : alpha = externalLeft 3 tau := by
  rw [alpha, leftPower, tauPower_one]

theorem beta_eq_inflated_tau : beta = externalRight 3 tau := by
  rw [beta, rightPower, tauPower_one]

theorem alpha_ne_zero : alpha ≠ 0 := leftPower_ne_zero 1
theorem beta_ne_zero : beta ≠ 0 := rightPower_ne_zero 1

theorem alpha_square_ne_zero : alpha.comp alpha (by omega) ≠ (0 : Ext X₂ X₂ 6) := by
  change (leftPower 1).comp (leftPower 1) _ ≠ _
  rw [leftPower_comp]
  exact leftPower_ne_zero 2

theorem beta_square_ne_zero : beta.comp beta (by omega) ≠ (0 : Ext X₂ X₂ 6) := by
  change (rightPower 1).comp (rightPower 1) _ ≠ _
  rw [rightPower_comp]
  exact rightPower_ne_zero 2

end
end TachikawaCharZero.SplitInflation

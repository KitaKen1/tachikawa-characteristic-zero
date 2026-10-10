import TachikawaCharZero.TwistedBimoduleObstruction
import OAI.RingTheory.Tachikawa.GenericCoinduction

/-! Actual outer Ext orthogonalities for the rational twisted source.
We identify the previously constructed End_Q(B) bimodule with the
coinduced right regular module and with DB tensor B-opposite. Coinduction
uses the actual right-projectivity of B_theta; the dual target is left
injective. The bounded derived-to-ordinary descent remains separate.
The generic adjunction arguments are reused from OpenAI Math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0). -/
namespace TachikawaCharZero.TwistedOrthogonality
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra
open TwistedFactorization TwistedBimoduleObstruction
attribute [local instance] Abelian.hasFiniteBiproducts

abbrev N := Enveloping.rightRegularObj (S := B₀)
abbrev coindRegular := Enveloping.coindObj (k := ℚ) (R := B₀) N

def rightOutput : B₀ ≃ₗ[ℚ] N :=
  (MulOpposite.opLinearEquiv ℚ).trans
    (moduleCatUnderlyingEquiv (k := ℚ) (R := B₀ᵐᵒᵖ) B₀ᵐᵒᵖ).symm

def outerCoindUnderlying : W ≃ₗ[ℚ] coindRegular :=
  (bimoduleUnderlying (k := ℚ) (R := B₀) (S := B₀) (M := OuterEnd ℚ B₀)).trans
    (rightOutput.congrRight.trans (Enveloping.coindUnderlying N).symm)

def outerCoindEquiv : LinearEquiv (R := BE) (S := BE) (RingHom.id BE) W coindRegular where
  __ := outerCoindUnderlying.toAddEquiv
  map_smul' a F := by
    change outerCoindUnderlying
        ((Enveloping.action (k := ℚ) (R := B₀) (S := B₀) (OuterEnd ℚ B₀) a) F)=
      (Enveloping.action (k := ℚ) (R := B₀) (S := B₀)
        (Enveloping.Coind (k := ℚ) (R := B₀) N) a) (outerCoindUnderlying F)
    induction a using TensorProduct.inductionOn with
    | add a b ha hb =>
      erw [map_add,LinearMap.add_apply,map_add,ha,hb,map_add,LinearMap.add_apply]
    | tmul r s =>
      apply LinearMap.ext
      intro x
      change MulOpposite.op ((show B₀ →ₗ[ℚ] B₀ from F) (x*r)*s.unop)=
        s*MulOpposite.op ((show B₀ →ₗ[ℚ] B₀ from F) (x*r))
      rfl

def outerCoindIso : W ≅ coindRegular :=
  LinearEquiv.toModuleIso (X₁ := W) (X₂ := coindRegular)
    (m₁ := W.isModule) (m₂ := coindRegular.isModule) outerCoindEquiv

def ordinaryOuterIso : Enveloping.ordinaryOuterObj (k := ℚ) (R := B₀) ≅ W :=
  (Enveloping.dualOuterEquiv N).toModuleIso ≪≫ outerCoindIso.symm

theorem twisted_outer_ext_zero (n : ℕ) :
    Subsingleton (CategoryTheory.Abelian.Ext U W (n+1)) := by
  let : IsScalarTower ℚ BE U := ModuleCat.isScalarTower_of_algebra_moduleCat (k := ℚ) U
  let : Module.Finite BE U := Module.Finite.of_restrictScalars_finite ℚ BE U
  let M : FiniteModule ℚ BE := ⟨U,inferInstance⟩
  let : Module.Projective B₀ᵐᵒᵖ (Enveloping.Obj M.obj) :=
    inferInstanceAs (Module.Projective B₀ᵐᵒᵖ (Enveloping.Obj U))
  let : Subsingleton (CategoryTheory.Abelian.Ext U coindRegular (n+1)) :=
    Enveloping.coind_ext_zero M N n
  exact (extIso (k := ℚ) (Iso.refl U) outerCoindIso (n+1)).injective.subsingleton

theorem outer_dual_ext_zero (n : ℕ) :
    Subsingleton (CategoryTheory.Abelian.Ext W D (n+1)) := by
  let : Subsingleton (CategoryTheory.Abelian.Ext
      (Enveloping.ordinaryOuterObj (k := ℚ) (R := B₀)) D (n+1)) :=
    Enveloping.outer_dual_ext_zero n
  exact (extIso (k := ℚ) ordinaryOuterIso.symm (Iso.refl D) (n+1)).injective.subsingleton

theorem two_orthogonalities (n : ℕ) :
    Subsingleton (CategoryTheory.Abelian.Ext U W (n+1)) ∧
    Subsingleton (CategoryTheory.Abelian.Ext W D (n+1)) :=
  ⟨twisted_outer_ext_zero n,outer_dual_ext_zero n⟩

theorem inAdd_ordinary_to_outer {V : ModuleCat BE}
    (h : InAdd (Enveloping.ordinaryOuterObj (k := ℚ) (R := B₀)) V) : InAdd W V := by
  obtain ⟨n,⟨r⟩⟩ := h
  exact ⟨n,⟨r.trans (biproduct.mapIso (fun _ : Fin n => ordinaryOuterIso)).retract⟩⟩

theorem eta_not_ordinaryOuter_factor {V : ModuleCat BE}
    (h : InAdd (Enveloping.ordinaryOuterObj (k := ℚ) (R := B₀)) V)
    (a : U ⟶ V) (b : V ⟶ D) : a ≫ b ≠ etaMap :=
  etaMap_not_inAdd_factor (inAdd_ordinary_to_outer h) a b

end
end TachikawaCharZero.TwistedOrthogonality

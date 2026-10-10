import OAI.RingTheory.Tachikawa.BimoduleLinear

/-! Characteristic-independent excerpts from OpenAI Math,
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (φ : R →ₐ[k] S)

abbrev envelopingMap : Alg k R R →ₐ[k] Alg k S S :=
  Algebra.TensorProduct.map φ φ.op

end Tachikawa.Enveloping

namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def resRegularUnderlying (φ : R →ₐ[k] S) :
    (AlgebraInduction.res φ).obj (ModuleCat.of S S) ≃ₗ[k] S where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change φ (algebraMap k R c) * (show S from x) = c • (show S from x)
    rw [AlgHom.commutes,Algebra.smul_def]

abbrev restrictedOuterRegular (φ : R →ₐ[k] S) :=
  ((OuterTensor.bifunctor k R Rᵐᵒᵖ).obj
    ((AlgebraInduction.res φ).obj (ModuleCat.of S S))).obj
      ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ))

def restrictedOuterRegularUnderlying (φ : R →ₐ[k] S) :
    OuterTensor.Obj k R Rᵐᵒᵖ
      ((AlgebraInduction.res φ).obj (ModuleCat.of S S))
      ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)) ≃ₗ[k] Alg k S S :=
  TensorProduct.congr (resRegularUnderlying φ) (resRegularUnderlying φ.op)

lemma restrictedOuterRegularUnderlying_tmul (φ : R →ₐ[k] S)
    (x : (AlgebraInduction.res φ).obj (ModuleCat.of S S))
    (y : (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)) :
    restrictedOuterRegularUnderlying φ (x ⊗ₜ[k] y) =
      (show S from x) ⊗ₜ[k] (show Sᵐᵒᵖ from y) := rfl

lemma restrictedOuterRegular_action (φ : R →ₐ[k] S) (a : Alg k R R)
    (z : ((AlgebraInduction.res φ).obj (ModuleCat.of S S)) ⊗[k]
      ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ))) :
    TensorProduct.congr (resRegularUnderlying φ) (resRegularUnderlying φ.op)
      ((OuterTensor.action k R Rᵐᵒᵖ _ _ a) z) =
    envelopingMap φ a *
      TensorProduct.congr (resRegularUnderlying φ) (resRegularUnderlying φ.op) z := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add,LinearMap.add_apply,map_add,ha,hb,map_add,add_mul]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add,map_add,hx,hy,map_add,mul_add]
    | tmul x y =>
      change (φ a * (show S from x)) ⊗ₜ[k] (φ.op b * (show Sᵐᵒᵖ from y)) =
        (φ a ⊗ₜ[k] φ.op b) * ((show S from x) ⊗ₜ[k] (show Sᵐᵒᵖ from y))
      exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

def restrictedOuterRegularEquiv (φ : R →ₐ[k] S) :
    restrictedOuterRegular φ ≃ₗ[Alg k R R]
      (AlgebraInduction.res (envelopingMap φ)).obj (ModuleCat.of (Alg k S S) (Alg k S S)) where
  __ := (restrictedOuterRegularUnderlying φ).toAddEquiv
  map_smul' a z := restrictedOuterRegular_action φ a z

def restrictedOuterRegularIso (φ : R →ₐ[k] S) :
    restrictedOuterRegular φ ≅
      (AlgebraInduction.res (envelopingMap φ)).obj (ModuleCat.of (Alg k S S) (Alg k S S)) :=
  (restrictedOuterRegularEquiv φ).toModuleIso

end Tachikawa.Enveloping


end
end OAI

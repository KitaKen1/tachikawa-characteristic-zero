import TachikawaCharZero.TensorExt
import TachikawaCharZero.StartingSymmetric

/-! A bounded projective resolution of the actual rational DB, as a left
B=C⊗C module. The tensor/dual comparison and support argument adapt the
characteristic-independent parts of OpenAI Math's FiniteCoinduction.lean
and ReverseResolution.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(Apache-2.0). The length-two C resolution is the checked signed rational
resolution; no characteristic-two construction is imported. -/
namespace TachikawaCharZero.TensorDualResolution
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex OAI.Tachikawa
open scoped TensorProduct ModuleCat.Algebra

section Generic
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

theorem total_isZero_above (P : ChainComplex (ModuleCat R) ℕ)
    (Q : ChainComplex (ModuleCat S) ℕ) (a b : ℕ)
    (hP : ∀ i, a < i → IsZero (P.X i)) (hQ : ∀ j, b < j → IsZero (Q.X j))
    (n : ℕ) (hn : a+b < n) :
    IsZero ((mapBifunctor P Q (OuterTensor.bifunctor k R S) (.down ℕ)).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext
  intro i j hij
  have h : IsZero (((OuterTensor.bifunctor k R S).obj (P.X i)).obj (Q.X j)) := by
    by_cases hi : a < i
    · exact ((OuterTensor.bifunctor k R S).flip.obj (Q.X j)).map_isZero (hP i hi)
    · exact ((OuterTensor.bifunctor k R S).obj (P.X i)).map_isZero
        (hQ j (by have hij' : i+j=n := hij; omega))
  exact h.eq_of_src _ _

end Generic

section Transport
variable {C : Type*} [Category* C] [Abelian C]

def transportResolution {M N : C} (P : ProjectiveResolution M) (e : M ≅ N) :
    ProjectiveResolution N where
  complex := P.complex
  projective n := P.projective n
  π := P.π ≫ (ChainComplex.single₀ C).map e.hom
  quasiIso := inferInstance

end Transport

open Resolution
abbrev B₀ := Starting.B
def DC : ModuleCat A := ModuleCat.of A Dual
def DB : ModuleCat B₀ := ModuleCat.of B₀ (DualBimodule ℚ B₀)

def dualUnderlying : DC ≃ₗ[ℚ] Module.Dual ℚ A where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r φ := by
    change (algebraMap ℚ A r) • (show Dual from φ) = r • (show Dual from φ)
    exact algebraMap_smul A r (show Dual from φ)

def tensorDualUnderlying : OuterTensor.Obj ℚ A A DC DC ≃ₗ[ℚ] DualBimodule ℚ B₀ :=
  (TensorProduct.congr dualUnderlying dualUnderlying).trans
    ((TensorProduct.dualDistribEquiv ℚ A A).trans
      { toFun := id, invFun := id, left_inv := fun _ => rfl,
        right_inv := fun _ => rfl, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl })

theorem tensorDualUnderlying_tmul (φ ψ : DC) (a b : A) :
    tensorDualUnderlying (φ ⊗ₜ[ℚ] ψ) (a ⊗ₜ[ℚ] b)=
      (show Dual from φ) a*(show Dual from ψ) b := by
  exact mul_comm _ _

def tensorDualEquiv : OuterTensor.Obj ℚ A A DC DC ≃ₗ[B₀] DualBimodule ℚ B₀ where
  __ := tensorDualUnderlying.toAddEquiv
  map_smul' a z := by
    change tensorDualUnderlying ((OuterTensor.action ℚ A A DC DC a) z) =
      a • tensorDualUnderlying z
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => erw [map_add,LinearMap.add_apply,map_add,ha,hb,add_smul]
    | tmul a b =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => erw [map_add,map_add,hx,hy,map_add,smul_add]
      | tmul φ ψ =>
        apply TensorProduct.ext'
        intro x y
        change (show Dual from ψ) (y*b)*(show Dual from φ) (x*a) =
          tensorDualUnderlying (φ ⊗ₜ[ℚ] ψ)
          ((x ⊗ₜ[ℚ] y)*(a ⊗ₜ[ℚ] b))
        rw [Algebra.TensorProduct.tmul_mul_tmul,tensorDualUnderlying_tmul,mul_comm]

theorem leftDual_finite (n : ℕ) :
    Module.Finite A (leftDualProjectiveResolution.complex.X n) := by
  let : Module.Finite ℚ Ce := Module.Finite.equiv ceIso
  let : Module.Finite ℚ Cf := Module.Finite.equiv cfIso
  let : Module.Finite A Ce := Module.Finite.of_restrictScalars_finite ℚ A Ce
  let : Module.Finite A Cf := Module.Finite.of_restrictScalars_finite ℚ A Cf
  let : Module.Finite A PUnit := Module.Finite.of_finite (R := A) (M := PUnit)
  change Module.Finite A (leftDualResObj n)
  rcases n with _ | _ | _ | n
  · exact inferInstanceAs (Module.Finite A (Ce × Ce))
  · exact inferInstanceAs (Module.Finite A Ce)
  · exact inferInstanceAs (Module.Finite A Cf)
  · exact inferInstanceAs (Module.Finite A PUnit)

theorem leftDual_above (n : ℕ) (hn : 2 < n) :
    IsZero (leftDualProjectiveResolution.complex.X n) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
  rw [Nat.add_comm 3 n]
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of A PUnit)

def leftResolution : ProjectiveResolution DB :=
  transportResolution
    (TensorExt.resolution ℚ A A leftDualProjectiveResolution leftDualProjectiveResolution
      leftDual_finite leftDual_finite) tensorDualEquiv.toModuleIso

theorem leftResolution_above (n : ℕ) (hn : 4 < n) :
    IsZero (leftResolution.complex.X n) :=
  total_isZero_above _ _ 2 2 leftDual_above leftDual_above n hn

theorem left_projectiveDimension : HasProjectiveDimensionLE DB 4 := by
  apply HasProjectiveDimensionLT.mk
  intro i hi Y α
  obtain ⟨f,hf,rfl⟩ := leftResolution.extMk_surjective α (i+1) rfl
  have h := (leftResolution_above i (by omega)).eq_of_src f 0
  subst f
  exact leftResolution.extMk_zero _ _

end
end TachikawaCharZero.TensorDualResolution

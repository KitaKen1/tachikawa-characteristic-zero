import TachikawaCharZero.StableSeam
import TachikawaCharZero.MonomialBasis
import OAI.RingTheory.Tachikawa.CompleteStable

/-! All-integer Tate self-Hom vector spaces of the actual rational X.
The complete resolution and stable-duality comparisons are genuine module
constructions. No negative generator action or twist weight is inferred
from dimensions. The duality construction adapts the characteristic-free
selfHomDual proof in OpenAI Math HomProfile.lean, fixed at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0). -/
namespace TachikawaCharZero.TateProfile
noncomputable section
open CategoryTheory CategoryTheory.Abelian TensorProfile MonomialBasis OAI.Tachikawa
open StableSeam (finiteX)
open scoped ModuleCat.Algebra

def form : SymmetrizingForm (k := ℚ) (R := E) := Starting.E_form
abbrev P := finiteX.complete form
abbrev Tate (a : ℤ) := VectorSplit.H (completeHom (k := ℚ) P X₂) a

def zeroEquiv : Tate 0 ≃ₗ[ℚ] ℚ :=
  (CompleteHom.equiv P X₂ (finiteX.complete_totallyAcyclic form)
    (finiteX.complete_finite form) (finiteX.complete_projective form) 0).trans
  (((StableEquiv.ofLinearEquiv (k := ℚ) (M := ModuleCat.of E (CokerAt P 0))
    (N := X₂) (finiteX.cokerEquiv form)).pre X₂).trans StableEnd.equiv)

def positiveSucc (n : ℕ) : Tate ((n+1:ℕ):ℤ) ≃ₗ[ℚ] Ext X₂ X₂ (n+1) :=
  (CompleteHom.equiv P X₂ (finiteX.complete_totallyAcyclic form)
    (finiteX.complete_finite form) (finiteX.complete_projective form) _).trans
  ((CompleteStableExt.equiv P (finiteX.complete_totallyAcyclic form)
    (finiteX.complete_finite form) (finiteX.complete_projective form) X₂ n).trans
    (extIso (k := ℚ) (finiteX.cokerEquiv form).toModuleIso (Iso.refl _) (n+1)))

def zeroExt : Ext X₂ X₂ 0 ≃ₗ[ℚ] ℚ :=
  (Ext.linearEquiv₀ (R := ℚ)).trans
    ((ModuleCat.homLinearEquiv (S := ℚ)).trans StableEnd.scalarEquiv.symm)

def nonnegativeExt : (n : ℕ) → Tate (n:ℤ) ≃ₗ[ℚ] Ext X₂ X₂ n
  | 0 => zeroEquiv.trans zeroExt.symm
  | n+1 => positiveSucc n

def multiple (m : ℕ) : Tate ((3*m:ℕ):ℤ) ≃ₗ[ℚ] (Fin (m+1) → ℚ) :=
  (nonnegativeExt (3*m)).trans (monomialBasis m).equivFun

def dual (a : ℤ) : Tate a ≃ₗ[ℚ] Module.Dual ℚ (Tate (-a-1)) := by
  let : Module.Injective E E := form.injective
  let ce := finiteX.cokerEquiv form
  let ta := finiteX.complete_totallyAcyclic form
  let fin := finiteX.complete_finite form
  let proj := finiteX.complete_projective form
  let e₁ := CompleteHom.equiv (k := ℚ) P X₂ ta fin proj a
  let e₂ := (StableEquiv.ofLinearEquiv (k := ℚ)
    (M := ModuleCat.of E (CokerAt P 0)) (N := X₂) ce).symm.post
      (ModuleCat.of E (CokerAt P a))
  have e₃ := cokerStableHomTranslate P ta.1 P ta.1 fin proj fin proj a 0 (-a) (k := ℚ)
  rw [add_neg_cancel,zero_add] at e₃
  let e₄ := (StableEquiv.ofLinearEquiv (k := ℚ)
    (M := ModuleCat.of E (CokerAt P 0)) (N := X₂) ce).pre
      (ModuleCat.of E (CokerAt P (-a)))
  have e₅ := completeCokerDuality form P ta.1 fin proj (-a-1) X₂
  rw [show -a-1+1 = -a by omega] at e₅
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans
    (e₅.trans (CompleteHom.equiv (k := ℚ) P X₂ ta fin proj (-a-1)).dualMap))))

def negative (m : ℕ) : Tate (-((3*m:ℕ):ℤ)-1) ≃ₗ[ℚ]
    Module.Dual ℚ (Fin (m+1) → ℚ) := by
  have e := dual (-((3*m:ℕ):ℤ)-1)
  rw [show -(-((3*m:ℕ):ℤ)-1)-1=((3*m:ℕ):ℤ) by omega] at e
  exact e.trans (multiple m).dualMap.symm

theorem multiple_finrank (m : ℕ) : Module.finrank ℚ (Tate ((3*m:ℕ):ℤ))=m+1 := by
  rw [(multiple m).finrank_eq]
  simp

theorem negative_finrank (m : ℕ) : Module.finrank ℚ (Tate (-((3*m:ℕ):ℤ)-1))=m+1 := by
  rw [(negative m).finrank_eq,Subspace.dual_finrank_eq]
  simp

theorem nonnegative_zero (n : ℕ) (hn : n%3≠0) : Subsingleton (Tate (n:ℤ)) := by
  let := TensorProfile.self_ext_off_multiples n hn
  exact (nonnegativeExt n).injective.subsingleton

theorem zero_of_dual (a : ℤ) (hz : Subsingleton (Tate (-a-1))) : Subsingleton (Tate a) := by
  let := hz
  let : Subsingleton (Module.Dual ℚ (Tate (-a-1))) := by
    constructor
    intro f g
    apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0,map_zero,map_zero]
  exact (dual a).injective.subsingleton

theorem negative_zero (n : ℕ) (hn : n%3≠0) : Subsingleton (Tate (-(n:ℤ)-1)) := by
  apply zero_of_dual
  rw [show -(-(n:ℤ)-1)-1=(n:ℤ) by omega]
  exact nonnegative_zero n hn

theorem unsupported_zero (a : ℤ)
    (hp : ∀ m : ℕ, a≠((3*m:ℕ):ℤ))
    (hn : ∀ m : ℕ, a≠ -((3*m:ℕ):ℤ)-1) : Subsingleton (Tate a) := by
  by_cases ha : 0≤a
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le ha
    apply nonnegative_zero
    intro h
    exact hp (n/3) (by omega)
  · have hneg : 0≤ -a-1 := by omega
    obtain ⟨n,h⟩ := Int.eq_ofNat_of_zero_le hneg
    have he : a= -(n:ℤ)-1 := by omega
    rw [he]
    apply negative_zero
    intro hmod
    exact hn (n/3) (by omega)

end
end TachikawaCharZero.TateProfile

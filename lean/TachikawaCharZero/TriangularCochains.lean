import TachikawaCharZero.SignedConeCochains
import TachikawaCharZero.SignedConeBoundary
import TachikawaCharZero.TriangularWitness

/-! Specialize signed cochain coordinates to the actual rational witness.
The forbidden block vanishes by the triangular module theorem, so no
additional vanishing assumption is placed on these declarations. -/
namespace TachikawaCharZero.TriangularCochains
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits OAI.Tachikawa TriangularWitness
open scoped ModuleCat.Algebra

abbrev v := Triangular.crossMap F lift
abbrev lowComplex := Triangular.D₀Complex F TateProfile.P
abbrev highComplex := Triangular.D₁Complex F TateProfile.P

def decomposition (a : ℤ) : SignedDownHom.Cochain cone cone a ≃ₗ[ℚ]
    (SignedDownHom.Cochain lowComplex lowComplex a ×
     SignedDownHom.Cochain highComplex highComplex a ×
     SignedDownHom.Cochain highComplex lowComplex (a-1)) :=
  SignedConeCochains.decomposition v (fun _ _ f => Triangular.cross₀₁_zero f) a

theorem low_diff {a : ℤ} (f : SignedDownHom.Cochain cone cone a) :
    SignedConeCochains.low v (SignedDownHom.diff (k:=ℚ) f) =
      SignedDownHom.diff (k:=ℚ) (SignedConeCochains.low v f) :=
  SignedConeCochains.low_diff v (fun _ _ f => Triangular.cross₀₁_zero f) f

theorem low_closed {a : ℤ} (f : SignedDownHom.Cochain cone cone a)
    (hf : SignedDownHom.Closed (k:=ℚ) f) :
    SignedDownHom.Closed (k:=ℚ) (SignedConeCochains.low v f) := by
  unfold SignedDownHom.Closed at hf ⊢
  rw [← low_diff,hf]
  funext i j h
  simp only [SignedConeCochains.low,SignedDownHom.zero_apply,comp_zero,zero_comp]

theorem high_diffAt {a : ℤ} (f : SignedDownHom.Cochain cone cone (a-1)) :
    SignedConeCochains.high v (SignedDownHom.diffAt (k:=ℚ) f) =
      -SignedDownHom.diffAt (k:=ℚ) (SignedConeCochains.high v f) :=
  SignedConeDifferential.high_diffAt v (fun _ _ f => Triangular.cross₀₁_zero f) f

theorem cross_diffAt {a : ℤ} (f : SignedDownHom.Cochain cone cone (a-1)) :
    SignedConeCochains.cross v (SignedDownHom.diffAt (k:=ℚ) f) =
      SignedDownHom.diffAt (k:=ℚ) (SignedConeCochains.cross v f)+
        SignedDownHom.post (SignedConeCochains.high v f) v-
          SignedDownHom.sign (k:=ℚ) (a-1) •
            SignedDownHom.pre v (SignedConeCochains.low v f) :=
  SignedConeDifferential.cross_diffAt v (fun _ _ f => Triangular.cross₀₁_zero f) f

theorem closed_blocks {a : ℤ} (f : SignedDownHom.Cochain cone cone a)
    (hf : SignedDownHom.Closed (k:=ℚ) f) :
    SignedDownHom.Closed (k:=ℚ) (SignedConeCochains.low v f) ∧
    SignedDownHom.Closed (k:=ℚ) (SignedConeCochains.high v f) ∧
    SignedConeDifferential.connecting (k:=ℚ) v
      (SignedConeCochains.low v f) (SignedConeCochains.high v f) =
        -SignedDownHom.diffAt (k:=ℚ) (SignedConeCochains.cross v f) :=
  SignedConeBoundary.closed_blocks v (fun _ _ f => Triangular.cross₀₁_zero f) f hf

/-- The actual cone criterion. Its two inputs still require the complete-Hom
comparison; this is not yet the unconditional self-Hom vanishing theorem. -/
theorem boundary_of_connecting (a : ℤ)
    (hI : ∀ (f : SignedDownHom.Cochain lowComplex lowComplex a)
      (g : SignedDownHom.Cochain highComplex highComplex a),
      SignedDownHom.Closed (k:=ℚ) f → SignedDownHom.Closed (k:=ℚ) g →
      SignedDownHom.Boundary (k:=ℚ) (SignedConeDifferential.connecting (k:=ℚ) v f g) →
      SignedDownHom.Boundary (k:=ℚ) f ∧ SignedDownHom.Boundary (k:=ℚ) g)
    (hS : ∀ (c : SignedDownHom.Cochain highComplex lowComplex (a-1)),
      SignedDownHom.Closed (k:=ℚ) c →
      ∃ (f : SignedDownHom.Cochain lowComplex lowComplex (a-1))
        (g : SignedDownHom.Cochain highComplex highComplex (a-1)),
        SignedDownHom.Closed (k:=ℚ) f ∧ SignedDownHom.Closed (k:=ℚ) g ∧
        SignedDownHom.Boundary (k:=ℚ) (c-SignedConeDifferential.connecting (k:=ℚ) v f g))
    (z : SignedDownHom.Cochain cone cone a) (hz : SignedDownHom.Closed (k:=ℚ) z) :
    SignedDownHom.Boundary (k:=ℚ) z :=
  SignedConeBoundary.boundary_of_connecting v
    (fun _ _ f => Triangular.cross₀₁_zero f) a hI hS z hz

end
end TachikawaCharZero.TriangularCochains

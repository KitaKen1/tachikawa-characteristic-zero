import TachikawaCharZero.SignedCochainTransport
import TachikawaCharZero.SignedConeDifferential
import OAI.RingTheory.Tachikawa.GenericTriangular

/-! Actual triangular cochains descend to the original complexes, with
the signed differential and signed boundaries preserved. The component
comparison adapts pinned OpenAI Math DownHom.lean 604--682
(Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).
The connecting-map formula retains the exact order and parity sign. -/
namespace TachikawaCharZero.SignedTriangularComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open CategoryTheory OAI.Tachikawa SignedDownHom SignedCochainTransport
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}

theorem diagonal₀_post {L M N : ModuleCat.{0} R}
    (f : Triangular.D₀Obj F L ⟶ Triangular.D₀Obj F M) (g : M ⟶ N) :
    Triangular.diagonal₀ (f ≫ Triangular.D₀Map F g)=Triangular.diagonal₀ f ≫ g := rfl

theorem diagonal₁_post {L M N : ModuleCat.{0} R}
    (f : Triangular.D₁Obj F L ⟶ Triangular.D₁Obj F M) (g : M ⟶ N) :
    Triangular.diagonal₁ (f ≫ Triangular.D₁Map F g)=Triangular.diagonal₁ f ≫ g := rfl

theorem cross_comp_right {L M N : ModuleCat.{0} R}
    (f : Triangular.D₁Obj F L ⟶ Triangular.D₀Obj F M)
    (g : Triangular.D₀Obj F M ⟶ Triangular.D₀Obj F N) :
    Triangular.cross₁₀ (f ≫ g)=
      Triangular.cross₁₀ f ≫ (Enveloping.tensorFunctor F).map (Triangular.diagonal₀ g) := by
  have hg : Triangular.D₀Map F (Triangular.diagonal₀ g)=g :=
    Triangular.diagonal₀.symm_apply_apply g
  rw [← hg,Triangular.cross₁₀_post]
  rfl

theorem cross_comp_left {L M N : ModuleCat.{0} R}
    (f : Triangular.D₁Obj F L ⟶ Triangular.D₁Obj F M)
    (g : Triangular.D₁Obj F M ⟶ Triangular.D₀Obj F N) :
    Triangular.cross₁₀ (f ≫ g)=Triangular.diagonal₁ f ≫ Triangular.cross₁₀ g := by
  have hf : Triangular.D₁Map F (Triangular.diagonal₁ f)=f :=
    Triangular.diagonal₁.symm_apply_apply f
  rw [← hf,Triangular.cross₁₀_pre]
  rfl

abbrev down₀ (a : ℤ) :
    Cochain (Triangular.D₀Complex F P) (Triangular.D₀Complex F Q) a ≃ₗ[k] Cochain P Q a :=
  cochainEquiv (fun _ _ => Triangular.diagonal₀) a
abbrev down₁ (a : ℤ) :
    Cochain (Triangular.D₁Complex F P) (Triangular.D₁Complex F Q) a ≃ₗ[k] Cochain P Q a :=
  cochainEquiv (fun _ _ => Triangular.diagonal₁) a
abbrev downCross (a : ℤ) :
    Cochain (Triangular.D₁Complex F P) (Triangular.D₀Complex F Q) a ≃ₗ[k]
      Cochain P (Enveloping.tensorComplex F Q) a :=
  cochainEquiv (fun _ _ => Triangular.cross₁₀) a

theorem down₀_closed {a : ℤ}
    (f : Cochain (Triangular.D₀Complex F P) (Triangular.D₀Complex F Q) a) :
    Closed (k:=k) (down₀ F a f) ↔ Closed (k:=k) f :=
  cochainEquiv_closed_iff _ (fun _ _ _ _ => Triangular.diagonal₀_pre F _ _)
    (fun _ _ _ _ => diagonal₀_post F _ _) f
theorem down₁_closed {a : ℤ}
    (f : Cochain (Triangular.D₁Complex F P) (Triangular.D₁Complex F Q) a) :
    Closed (k:=k) (down₁ F a f) ↔ Closed (k:=k) f :=
  cochainEquiv_closed_iff _ (fun _ _ _ _ => Triangular.diagonal₁_pre F _ _)
    (fun _ _ _ _ => diagonal₁_post F _ _) f
theorem downCross_closed {a : ℤ}
    (f : Cochain (Triangular.D₁Complex F P) (Triangular.D₀Complex F Q) a) :
    Closed (k:=k) (downCross F a f) ↔ Closed (k:=k) f :=
  cochainEquiv_closed_iff _ (fun _ _ _ _ => Triangular.cross₁₀_pre F _ _)
    (fun _ _ _ _ => Triangular.cross₁₀_post F _ _) f

theorem down₀_boundary {a : ℤ}
    (f : Cochain (Triangular.D₀Complex F P) (Triangular.D₀Complex F Q) a) :
    Boundary (k:=k) (down₀ F a f) ↔ Boundary (k:=k) f :=
  cochainEquiv_boundary_iff _ (fun _ _ _ _ => Triangular.diagonal₀_pre F _ _)
    (fun _ _ _ _ => diagonal₀_post F _ _) f
theorem down₁_boundary {a : ℤ}
    (f : Cochain (Triangular.D₁Complex F P) (Triangular.D₁Complex F Q) a) :
    Boundary (k:=k) (down₁ F a f) ↔ Boundary (k:=k) f :=
  cochainEquiv_boundary_iff _ (fun _ _ _ _ => Triangular.diagonal₁_pre F _ _)
    (fun _ _ _ _ => diagonal₁_post F _ _) f
theorem downCross_boundary {a : ℤ}
    (f : Cochain (Triangular.D₁Complex F P) (Triangular.D₀Complex F Q) a) :
    Boundary (k:=k) (downCross F a f) ↔ Boundary (k:=k) f :=
  cochainEquiv_boundary_iff _ (fun _ _ _ _ => Triangular.cross₁₀_pre F _ _)
    (fun _ _ _ _ => Triangular.cross₁₀_post F _ _) f

theorem down_connecting (u : P ⟶ Enveloping.tensorComplex F P) {a : ℤ}
    (f : Cochain (Triangular.D₀Complex F P) (Triangular.D₀Complex F P) a)
    (g : Cochain (Triangular.D₁Complex F P) (Triangular.D₁Complex F P) a) :
    downCross F a (SignedConeDifferential.connecting (k:=k) (Triangular.crossMap F u) f g)=
      post (down₁ F a g) u-sign (k:=k) a •
        pre u (mapCochain (Enveloping.tensorFunctor F) (down₀ F a f)) := by
  funext i j h
  change Triangular.cross₁₀
    ((g i j h ≫ (Triangular.crossMap F u).f j)-
      sign (k:=k) a • ((Triangular.crossMap F u).f i ≫ f i j h)) = _
  erw [map_sub,map_smul,cross_comp_left,cross_comp_right]
  simp only [Triangular.crossMap,LinearEquiv.apply_symm_apply] <;> rfl

end
end TachikawaCharZero.SignedTriangularComparison

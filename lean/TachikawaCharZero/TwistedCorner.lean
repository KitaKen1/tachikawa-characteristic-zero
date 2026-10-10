import TachikawaCharZero.Corner
import OAI.RingTheory.Tachikawa.Twisting

/-! Generic scaling comparisons on actual principal corners. Keeping the
ring abstract here avoids expanding a concrete coordinate algebra inside
the kernel when checking restriction-of-scalars module instances. -/
namespace TachikawaCharZero.TwistedCorner
noncomputable section
open CategoryTheory OAI.Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

def comparison (p : R) (hp : σ p=p) :
    (SymmetrizingForm.twistFunctor σ).obj (ModuleCat.of R (Corner.leftCorner p)) ⟶
      ModuleCat.of R (Corner.leftCorner p) :=
  ModuleCat.ofHom
    (X := (SymmetrizingForm.twistFunctor σ).obj (ModuleCat.of R (Corner.leftCorner p)))
    (Y := ModuleCat.of R (Corner.leftCorner p))
    { toFun := fun x => ⟨σ x.val,by
        change σ x.val*p=σ x.val
        have hx := congrArg σ x.property
        rw [map_mul,hp] at hx
        exact hx⟩
      map_add' _ _ := Subtype.ext (map_add _ _ _)
      map_smul' r x := by
        apply Subtype.ext
        change σ (σ.symm r*x.val)=r*σ x.val
        rw [map_mul,AlgEquiv.apply_symm_apply] }

theorem comparison_apply (p : R) (hp : σ p=p)
    (x : (SymmetrizingForm.twistFunctor σ).obj (ModuleCat.of R (Corner.leftCorner p))) :
    (comparison σ p hp x).val=σ x.val := rfl

theorem differential_natural {p r : R} (hp : σ p=p) (hr : σ r=r)
    (b : R) (hb : b*r=b) (hσb : σ b=b) :
    (SymmetrizingForm.twistFunctor σ).map (ModuleCat.ofHom (Corner.mulRight (p:=p) b hb)) ≫
      comparison σ r hr = comparison σ p hp ≫ ModuleCat.ofHom (Corner.mulRight b hb) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change σ (x.val*b)=σ x.val*b
  rw [map_mul,hσb]

end
end TachikawaCharZero.TwistedCorner

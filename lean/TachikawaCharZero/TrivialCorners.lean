import TachikawaCharZero.Dual
import TachikawaCharZero.RightCorners
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! A concrete model of induction on principal projectives.
The corner T p in T=C⋉DC is Cp × D(pC). This avoids constructing a general
balanced tensor product for the two projectives used in the resolution.
The standard dual-exactness argument follows the generic lemma in OpenAI
Math's Tachikawa/Nakayama.lean, fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
The corner decomposition and its differential compatibility are proved here. -/
namespace TachikawaCharZero.Induced
noncomputable section
open Resolution

abbrev T := TrivSqZeroExt A Dual
instance tFiniteQ : Module.Finite ℚ T := inferInstanceAs (Module.Finite ℚ (A×Dual))
abbrev left (p : A) := Corner.leftCorner p
abbrev right (p : A) := Corner.rightCorner p
abbrev corner (p : A) := Corner.leftCorner (TrivSqZeroExt.inl p : T)

instance leftFiniteQ (p : A) : Module.Finite ℚ (left p) :=
  Module.Finite.of_injective ((left p).subtype.restrictScalars ℚ) Subtype.val_injective
instance rightFiniteQ (p : A) : Module.Finite ℚ (right p) :=
  Module.Finite.of_injective ((right p).subtype.restrictScalars ℚ) Subtype.val_injective
instance cornerFiniteQ (p : A) : Module.Finite ℚ (corner p) :=
  Module.Finite.of_injective ((corner p).subtype.restrictScalars ℚ) Subtype.val_injective

def rightProjection {p : A} (hp : p*p=p) : A →ₗ[ℚ] right p where
  toFun a := ⟨p*a, by change p*(p*a)=p*a; rw [← mul_assoc,hp]⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (Algebra.mul_smul_comm _ _ _)

def extendDual {p : A} (hp : p*p=p) (ψ : Module.Dual ℚ (right p)) : Dual :=
  ψ.comp (rightProjection hp)

def first {p : A} (a : corner p) : left p :=
  ⟨(a:T).fst, congrArg TrivSqZeroExt.fst a.property⟩

def second {p : A} (a : corner p) : Module.Dual ℚ (right p) :=
  ((a:T).snd : Module.Dual ℚ A).comp ((right p).subtype.restrictScalars ℚ)

theorem snd_fixed {p : A} (a : corner p) (b : A) : (a:T).snd (p*b)=(a:T).snd b := by
  have h := congrArg (fun x : T => x.snd b) a.property
  change ((a:T).fst • (0:Dual) + MulOpposite.op p • (a:T).snd) b=(a:T).snd b at h
  simpa using h

def pack {p : A} (hp : p*p=p) (a : left p) (ψ : Module.Dual ℚ (right p)) : corner p :=
  ⟨⟨(a:A),extendDual hp ψ⟩, by
    apply TrivSqZeroExt.ext
    · exact a.property
    · apply dual_ext
      intro b
      change ((a:A) • (0:Dual) + MulOpposite.op p • extendDual hp ψ) b = extendDual hp ψ b
      simp only [smul_zero,zero_add]
      change ψ (rightProjection hp (p*b))=ψ (rightProjection hp b)
      congr 1
      apply Subtype.ext
      exact (mul_assoc p p b).symm.trans (congrArg (fun z : A => z*b) hp)⟩

def decomp {p : A} (hp : p*p=p) :
    corner p ≃ₗ[ℚ] (left p × Module.Dual ℚ (right p)) where
  toFun a := (first a,second a)
  invFun a := pack hp a.1 a.2
  left_inv a := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · rfl
    · apply dual_ext
      exact snd_fixed a
  right_inv a := by
    apply Prod.ext
    · rfl
    · apply LinearMap.ext
      intro b
      change a.2 (rightProjection hp (b:A))=a.2 b
      congr 1
      exact Subtype.ext b.property
  map_add' _ _ := by apply Prod.ext <;> rfl
  map_smul' _ _ := by apply Prod.ext <;> rfl

def differential {p r : A} (b : A) (hbr : b*r=b) : corner p →ₗ[T] corner r :=
  Corner.mulRight (TrivSqZeroExt.inl b) (by
    apply TrivSqZeroExt.ext
    · exact hbr
    · simp)

theorem decomp_differential {p r : A} (hp : p*p=p) (hr : r*r=r)
    (b : A) (hpb : p*b=b) (hbr : b*r=b) (a : corner p) :
    decomp hr (differential b hbr a)=
      (Corner.mulRight b hbr (decomp hp a).1,
        ((Corner.mulLeft b hpb).restrictScalars ℚ).dualMap (decomp hp a).2) := by
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro x
    change (((a:T).fst • (0:Dual) + MulOpposite.op b • (a:T).snd) (x:A))=
      (a:T).snd (b*(x:A))
    simp

theorem projective {p : A} (hp : p*p=p) : Module.Projective T (corner p) :=
  Corner.projective (by apply TrivSqZeroExt.ext; exact hp; simp)

theorem exact_dual {U V W : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (f : U →ₗ[ℚ] V) (g : V →ₗ[ℚ] W) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by
  rw [LinearMap.exact_iff,LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker,LinearMap.exact_iff.mp h]

end
end TachikawaCharZero.Induced

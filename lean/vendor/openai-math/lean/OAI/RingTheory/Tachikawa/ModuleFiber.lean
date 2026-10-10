import OAI.RingTheory.Tachikawa.CycleQuasiIso
import OAI.RingTheory.Tachikawa.CompleteResolution

/-! Characteristic-independent excerpts from pinned OpenAI Math (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R : Type} [Ring R]

namespace ModuleFiber
variable {K L : ChainComplex (ModuleCat R) ℤ} (f : K ⟶ L)

def obj (_f : K ⟶ L) (j : ℤ) : ModuleCat R := ModuleCat.of R (L.X (j+1) × K.X j)

def differential (j : ℤ) : obj f (j+1) ⟶ obj f j :=
  ModuleCat.ofHom <|
    (((L.d (j+1+1) (j+1)).hom.comp (LinearMap.fst R _ _) +
        (f.f (j+1)).hom.comp (LinearMap.snd R _ _)).prod
      (-((K.d (j+1) j).hom.comp (LinearMap.snd R _ _))))

lemma differential_apply (j : ℤ) (x : obj f (j+1)) :
    differential f j x = (L.d (j+1+1) (j+1) x.1 + f.f (j+1) x.2,
      -K.d (j+1) j x.2) := rfl

lemma differential_comp (j : ℤ) : differential f (j+1) ≫ differential f j = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change L.d (j+1+1) (j+1) (L.d (j+1+1+1) (j+1+1) x.1 +
        f.f (j+1+1) x.2) + f.f (j+1) (-K.d (j+1+1) (j+1) x.2) = 0
    rw [map_add, map_neg]
    have hz := congrArg (fun a : L.X (j+1+1+1) ⟶ L.X (j+1) => a x.1)
      (L.d_comp_d (j+1+1+1) (j+1+1) (j+1))
    have hc := congrArg (fun a : K.X (j+1+1) ⟶ L.X (j+1) => a x.2)
      (f.comm (j+1+1) (j+1))
    change L.d (j+1+1) (j+1) (L.d (j+1+1+1) (j+1+1) x.1) = 0 at hz
    change L.d (j+1+1) (j+1) (f.f (j+1+1) x.2) =
      f.f (j+1) (K.d (j+1+1) (j+1) x.2) at hc
    rw [hz, zero_add, hc, add_neg_cancel]
  · change -K.d (j+1) j (-K.d (j+1+1) (j+1) x.2) = 0
    rw [map_neg, neg_neg]
    exact congrArg (fun a : K.X (j+1+1) ⟶ K.X j => a x.2)
      (K.d_comp_d (j+1+1) (j+1) j)

def complex : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (obj f) (differential f) (differential_comp f)

@[simp] lemma complex_d (j : ℤ) : (complex f).d (j+1) j = differential f j :=
  ChainComplex.of_d _ _ j

lemma differential_exact [QuasiIso f] (j : ℤ) :
    Function.Exact (differential f (j+1)) (differential f j) := by
  have hqi (n : ℤ) := (quasiIsoAt_iff' f (n+1) n (n-1) (by simp) (by simp)).mp
    (inferInstance : QuasiIsoAt f n)
  have hc (n : ℤ) := shortComplex_cycles_of_quasiIso _ (hqi n)
  intro x
  constructor
  · intro hx
    have hx₁ : L.d (j+1+1) (j+1) x.1 + f.f (j+1) x.2 = 0 := congrArg Prod.fst hx
    have hx₂ : K.d (j+1) j x.2 = 0 := neg_eq_zero.mp (congrArg Prod.snd hx)
    have hx₂' : K.d (j+1) (j+1-1) x.2 = 0 := by
      rw [show j+1-1 = j by omega]
      exact hx₂
    obtain ⟨s,hs⟩ := (hc (j+1)).1 x.2 hx₂' ⟨-x.1, by
      change L.d (j+1+1) (j+1) (-x.1) = f.f (j+1) x.2
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_right hx₁).symm⟩
    change K.X (j+1+1) at s
    change K.d (j+1+1) (j+1) s = x.2 at hs
    have hy : L.d (j+1+1) (j+1+1-1) (x.1 + f.f (j+1+1) s) = 0 := by
      rw [show j+1+1-1 = j+1 by omega, map_add]
      have hh := congrArg (fun a : K.X (j+1+1) ⟶ L.X (j+1) => a s)
        (f.comm (j+1+1) (j+1))
      change L.d (j+1+1) (j+1) (f.f (j+1+1) s) =
        f.f (j+1) (K.d (j+1+1) (j+1) s) at hh
      rw [hh, hs]
      exact hx₁
    obtain ⟨t,ht,u,hu⟩ := (hc (j+1+1)).2 (x.1 + f.f (j+1+1) s) hy
    change K.X (j+1+1) at t
    change L.X (j+1+1+1) at u
    change K.d (j+1+1) (j+1+1-1) t = 0 at ht
    rw [show j+1+1-1 = j+1 by omega] at ht
    change L.d (j+1+1+1) (j+1+1) u =
      f.f (j+1+1) t - (x.1 + f.f (j+1+1) s) at hu
    refine ⟨(-u,-s+t), ?_⟩
    apply Prod.ext
    · change L.d (j+1+1+1) (j+1+1) (-u) + f.f (j+1+1) (-s+t) = x.1
      rw [map_neg, map_add, map_neg, hu]
      abel
    · change -K.d (j+1+1) (j+1) (-s+t) = x.2
      rw [map_add,map_neg,hs,ht,add_zero,neg_neg]
  · rintro ⟨y,rfl⟩
    exact congrArg (fun a : obj f (j+1+1) ⟶ obj f j => a y) (differential_comp f j)

lemma exact [QuasiIso f] : ComplexExact (complex f) := by
  intro j
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j = i+1 := ⟨j-1, by omega⟩
  rw [show i+1-1 = i by omega, complex_d, complex_d]
  exact differential_exact f i

lemma totallyAcyclic [QuasiIso f] [Module.Injective R R] : TotallyAcyclic (complex f) := by
  refine ⟨exact f, ?_⟩
  intro j g hg
  obtain ⟨h,hh⟩ := Module.Injective.extension_property R R
    (CokerAt (complex f) j) ((complex f).X (j-1))
    (CokerAt.ι (complex f) j) (CokerAt.ι_injective _ _ (exact f j))
    (CokerAt.descend _ _ g hg)
  refine ⟨h, ?_⟩
  have hh' := congrArg (fun a => a.comp (CokerAt.π (complex f) j)) hh
  simpa only [LinearMap.comp_assoc, CokerAt.ι_comp_π, CokerAt.descend_comp_π] using hh'

end ModuleFiber

end Tachikawa
end
end OAI

import OAI.RingTheory.Tachikawa.CycleQuasiIso
import OAI.RingTheory.Tachikawa.NakayamaTransfer

/-! Characteristic-independent excerpts from the pinned OpenAI Math
Period.lean and ReverseResolution.lean (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace TrivialInduction

@[simp] lemma map_zero {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N] :
    map (k := k) (0 : M →ₗ[R] N) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · exact LinearMap.congr_fun Nakayama.map_zero x.2

def functor : ModuleCat R ⥤ ModuleCat (TrivialExtension k R) where
  obj M := ModuleCat.of (TrivialExtension k R) (Obj k R M)
  map f := ModuleCat.ofHom (map f.hom)
  map_id _ := ModuleCat.hom_ext map_id
  map_comp f g := ModuleCat.hom_ext (map_comp f.hom g.hom)

instance : (functor (k := k) (R := R)).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · apply LinearMap.ext
      intro a
      change x.2 (a.comp (f.hom+g.hom)) = x.2 (a.comp f.hom) + x.2 (a.comp g.hom)
      rw [LinearMap.comp_add, map_add]

end TrivialInduction

open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace TrivialInduction

lemma quasiIso_map {P Q : ChainComplex (ModuleCat R) ℤ} (f : P ⟶ Q)
    (hf : QuasiIso f)
    (hν : QuasiIso (((Nakayama.functor (k := k)).mapHomologicalComplex _).map f)) :
    QuasiIso (((functor (k := k)).mapHomologicalComplex _).map f) := by
  let := hf
  let := hν
  constructor
  intro j
  rw [quasiIsoAt_iff' _ (j+1) j (j-1) (by simp) (by simp)]
  have hf' := shortComplex_cycles_of_quasiIso _
    ((quasiIsoAt_iff' f (j+1) j (j-1) (by simp) (by simp)).mp inferInstance)
  have hν' := shortComplex_cycles_of_quasiIso _
    ((quasiIsoAt_iff' (((Nakayama.functor (k := k)).mapHomologicalComplex _).map f)
      (j+1) j (j-1) (by simp) (by simp)).mp inferInstance)
  apply shortComplex_quasiIso_of_cycles
  · intro x hx hbd
    obtain ⟨z,hz⟩ := hbd
    obtain ⟨a,ha⟩ := hf'.1 x.1 (congrArg Prod.fst hx) ⟨z.1, congrArg Prod.fst hz⟩
    obtain ⟨b,hb⟩ := hν'.1 x.2 (congrArg Prod.snd hx) ⟨z.2, congrArg Prod.snd hz⟩
    exact ⟨(a,b), Prod.ext ha hb⟩
  · intro y hy
    obtain ⟨a,ha,z,hz⟩ := hf'.2 y.1 (congrArg Prod.fst hy)
    obtain ⟨b,hb,w,hw⟩ := hν'.2 y.2 (congrArg Prod.snd hy)
    exact ⟨(a,b), Prod.ext ha hb, (z,w), Prod.ext hz hw⟩
end TrivialInduction
end Tachikawa
end
end OAI

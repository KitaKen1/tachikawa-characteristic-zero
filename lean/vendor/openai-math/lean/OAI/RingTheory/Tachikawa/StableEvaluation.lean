import OAI.RingTheory.Tachikawa.EvaluationProjectivity
import OAI.RingTheory.Tachikawa.StableLiftDescent
import OAI.RingTheory.Tachikawa.SideProjectivity

/-! Characteristic-independent excerpts at OpenAI Math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa.BalancedTensor
variable {k R S M M' N : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module S M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k S M'] [IsScalarTower k Rᵐᵒᵖ M'] [SMulCommClass S Rᵐᵒᵖ M']
  [AddCommGroup N] [Module k N] [Module R N]

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M'] in
lemma restrictEquiv_mapLeft (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (x : T (k := k) (R := R) (S := S) (M := M) (N := N)) :
    restrictEquiv (mapLeft (k := k) (N := N) f hf x) =
      mapLeft (k := k) (S := k) (N := N) (f.restrictScalars k) hf (restrictEquiv x) := by
  induction x using induction_on with
  | h0 => simp
  | ht m n => rfl
  | ha x y hx hy => simp only [map_add, hx, hy]

lemma mapLeft_injective_of_right_split (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (r : M' →ₗ[Rᵐᵒᵖ] M) (hr : ∀ m, r (f m) = m) :
    Function.Injective (mapLeft (k := k) (N := N) f hf) := by
  let g := mapLeft (k := k) (S := k) (N := N) (r.restrictScalars k) r.map_smul
  have hg : ∀ x : T (k := k) (R := R) (S := k) (M := M) (N := N),
      g (mapLeft (k := k) (S := k) (N := N) (f.restrictScalars k) hf x) = x := by
    intro x
    induction x using induction_on with
    | h0 => simp only [map_zero]
    | ht m n => exact congrArg (fun m => mk (k := k) (R := R) (S := k) m n) (hr m)
    | ha x y hx hy => simp only [map_add, hx, hy]
  intro x y h
  apply (restrictEquiv (k := k) (R := R) (S := S)).injective
  have h' := congrArg (restrictEquiv (k := k) (R := R) (S := S)) h
  rw [restrictEquiv_mapLeft, restrictEquiv_mapLeft] at h'
  exact (hg _).symm.trans ((congrArg g h').trans (hg _))

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R S M P Q N : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup P] [Module k P] [Module S P] [Module Rᵐᵒᵖ P]
  [IsScalarTower k S P] [IsScalarTower k Rᵐᵒᵖ P] [SMulCommClass S Rᵐᵒᵖ P]
  [AddCommGroup Q] [Module k Q] [Module S Q] [Module Rᵐᵒᵖ Q]
  [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  [AddCommGroup N] [Module k N] [Module R N]

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ P]
  [SMulCommClass S Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ P] in
lemma mapLeft_surjective (f : M →ₗ[S] P)
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m) (hs : Function.Surjective f) :
    Function.Surjective (mapLeft (k := k) (N := N) f hf) := by
  intro x
  induction x using induction_on with
  | h0 => exact ⟨0,map_zero _⟩
  | ht m n =>
    obtain ⟨m',rfl⟩ := hs m
    exact ⟨mk m' n,rfl⟩
  | ha x y hx hy =>
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    exact ⟨a+b,map_add _ _ _⟩

lemma mapLeft_exact_of_right_splitting (f : M →ₗ[S] P) (g : P →ₗ[S] Q)
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (hg : ∀ (r : Rᵐᵒᵖ) m, g (r • m) = r • g m)
    (r : P →ₗ[Rᵐᵒᵖ] M) (s : Q →ₗ[Rᵐᵒᵖ] P)
    (hid : ∀ p, f (r p) + s (g p) = p) (hz : ∀ m, g (f m) = 0) :
    Function.Exact (mapLeft (k := k) (N := N) f hf) (mapLeft (k := k) (N := N) g hg) := by
  let F := mapLeft (k := k) (S := k) (N := N) (f.restrictScalars k) hf
  let G := mapLeft (k := k) (S := k) (N := N) (g.restrictScalars k) hg
  let Rr := mapLeft (k := k) (S := k) (N := N) (r.restrictScalars k) r.map_smul
  let Ss := mapLeft (k := k) (S := k) (N := N) (s.restrictScalars k) s.map_smul
  have hid' (x : T (k := k) (R := R) (S := k) (M := P) (N := N)) :
      F (Rr x) + Ss (G x) = x := by
    induction x using induction_on with
    | h0 => simp only [map_zero,add_zero]
    | ht p n =>
      change mk (f (r p)) n + mk (s (g p)) n = mk p n
      rw [← LinearMap.add_apply,← map_add,hid]
    | ha x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm,hx,hy]
  have hz' (x : T (k := k) (R := R) (S := S) (M := M) (N := N)) :
      mapLeft (k := k) (N := N) g hg (mapLeft (k := k) (N := N) f hf x) = 0 := by
    induction x using induction_on with
    | h0 => simp only [map_zero]
    | ht m n => change mk (g (f m)) n = 0; rw [hz,map_zero,LinearMap.zero_apply]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
  intro x
  constructor
  · intro hx
    let x' := restrictEquiv (k := k) (R := R) (S := S) x
    have hG : G x' = 0 := by
      simpa only [restrictEquiv_mapLeft,map_zero] using
        congrArg (restrictEquiv (k := k) (R := R) (S := S)) hx
    refine ⟨(restrictEquiv (k := k) (R := R) (S := S)).symm (Rr x'),?_⟩
    apply (restrictEquiv (k := k) (R := R) (S := S)).injective
    rw [restrictEquiv_mapLeft,LinearEquiv.apply_symm_apply]
    have h := hid' x'
    rw [hG,map_zero,add_zero] at h
    exact h
  · rintro ⟨y,rfl⟩
    exact hz' y
end Tachikawa.BalancedTensor



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R) {M N : ModuleCat.{0} (Alg k S R)}

instance eval_finite [FiniteDimensional k M] [FiniteDimensional k X] :
    Module.Finite S (evalObj X M) :=
  Module.Finite.of_restrictScalars_finite k S (evalType X M)

lemma evalMap_injective [FiniteDimensional k R] [FiniteDimensional k M]
    [Module.Projective Rᵐᵒᵖ (Obj M)] (t : SymmetrizingForm (k := k) (R := R))
    (f : M ⟶ N) (hf : Function.Injective f) : Function.Injective (evalMap X f) := by
  let : Module.Injective Rᵐᵒᵖ Rᵐᵒᵖ := t.op.injective
  let : Module.Finite Rᵐᵒᵖ (Obj M) := Module.Finite.of_restrictScalars_finite k Rᵐᵒᵖ (Obj M)
  let : Module.Injective Rᵐᵒᵖ (Obj M) := injective_of_finite_projective
  obtain ⟨r,hr⟩ := Module.Injective.extension_property Rᵐᵒᵖ (Obj M) (Obj M) (Obj N)
    (rightMap f) hf LinearMap.id
  exact BalancedTensor.mapLeft_injective_of_right_split (leftMap f) (rightMap f).map_smul r
    (fun m => LinearMap.congr_fun hr m)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R) {M P Q : ModuleCat.{0} (Alg k S R)}

lemma evalMap_surjective (g : P ⟶ Q) (hg : Function.Surjective g) :
    Function.Surjective (evalMap X g) :=
  BalancedTensor.mapLeft_surjective (leftMap g) (rightMap g).map_smul hg

lemma evalMap_exact [FiniteDimensional k R] [FiniteDimensional k M]
    [Module.Projective Rᵐᵒᵖ (Obj M)] (t : SymmetrizingForm (k := k) (R := R))
    (f : M ⟶ P) (g : P ⟶ Q) (hi : Function.Injective f)
    (he : Function.Exact f g) (hs : Function.Surjective g) :
    Function.Exact (evalMap X f) (evalMap X g) := by
  let : Module.Injective Rᵐᵒᵖ Rᵐᵒᵖ := t.op.injective
  let : Module.Finite Rᵐᵒᵖ (Obj M) := Module.Finite.of_restrictScalars_finite k Rᵐᵒᵖ (Obj M)
  let : Module.Injective Rᵐᵒᵖ (Obj M) := injective_of_finite_projective
  let H := linearShortExact (rightMap f) (rightMap g) he hi hs
  let : CategoryTheory.Injective (linearShortComplex (rightMap f) (rightMap g) he).X₁ :=
    Module.injective_object_of_injective_module Rᵐᵒᵖ (Obj M)
  let sp := H.splittingOfInjective
  apply BalancedTensor.mapLeft_exact_of_right_splitting (leftMap f) (leftMap g)
    (rightMap f).map_smul (rightMap g).map_smul sp.r.hom sp.s.hom
  · intro p
    exact congrArg (fun z : ModuleCat.of Rᵐᵒᵖ (Obj P) ⟶ ModuleCat.of Rᵐᵒᵖ (Obj P) => z p) sp.id
  · intro m
    exact (he _).mpr ⟨m,rfl⟩
end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))
  (X : ModuleCat.{0} R) [FiniteDimensional k X]
  {M N P Q M' N' : ModuleCat.{0} (Alg k S R)}
  [FiniteDimensional k M] [FiniteDimensional k N]
  [Module.Projective Rᵐᵒᵖ (Obj M)] [Module.Projective Rᵐᵒᵖ (Obj N)]
  [Module.Finite (Alg k S R) P] [Module.Projective (Alg k S R) P]
  [Module.Finite (Alg k S R) Q] [Module.Projective (Alg k S R) Q]

include t u in

lemma eval_square_factors_iff
    (i : M ⟶ P) (pi : P ⟶ M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N ⟶ Q) (delta : Q ⟶ N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (f : M ⟶ N) (h : P ⟶ Q) (g : M' ⟶ N')
    (hu : i ≫ h = f ≫ j) (hl : h ≫ delta = pi ≫ g) :
    (evalMap X f).hom ∈ projectiveFactors (k := k) ↔
      (evalMap X g).hom ∈ projectiveFactors (k := k) := by
  let : Module.Injective S S := u.injective
  let : FiniteDimensional k P := Module.Finite.trans (Alg k S R) P
  let : FiniteDimensional k Q := Module.Finite.trans (Alg k S R) Q
  apply exact_square_factors_iff (P := evalObj X P) (Q := evalObj X Q)
    (evalMap X i).hom (evalMap X pi).hom
    (evalMap_injective X t i hi) (evalMap_exact X t i pi hi hex hpi)
    (evalMap_surjective X pi hpi)
    (evalMap X j).hom (evalMap X delta).hom
    (evalMap_injective X t j hj) (evalMap_exact X t j delta hj hex' hdelta)
    (evalMap_surjective X delta hdelta)
    (evalMap X f).hom (evalMap X h).hom (evalMap X g).hom
  · have hmap := congrArg (evaluation X).map hu
    rw [Functor.map_comp,Functor.map_comp] at hmap
    ext x
    exact congrArg (fun a : (evaluation X).obj M ⟶ (evaluation X).obj Q => a x) hmap
  · have hmap := congrArg (evaluation X).map hl
    rw [Functor.map_comp,Functor.map_comp] at hmap
    ext x
    exact congrArg (fun a : (evaluation X).obj P ⟶ (evaluation X).obj N' => a x) hmap
end Tachikawa.Enveloping



namespace Tachikawa.BimoduleTensorHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (tR : SymmetrizingForm (k := k) (R := R))
  (tS : SymmetrizingForm (k := k) (R := S))
  {M : ModuleCat.{0} (Enveloping.Alg k S R)} {X : ModuleCat.{0} R} {Z : ModuleCat.{0} S}
  [FiniteDimensional k M] [FiniteDimensional k X]

omit tR tS [FiniteDimensional k M] in
lemma uncurry_factors {f : M ⟶ HomBimodule.obj (k := k) X Z}
    (hf : f.hom ∈ projectiveFactors (k := k)) :
    (uncurry f).hom ∈ projectiveFactors (k := k) := by
  obtain ⟨P, hPf, hPp, a, b, hab⟩ := hf
  let := hPf
  let := hPp
  let : FiniteDimensional k P := Module.Finite.trans (Enveloping.Alg k S R) P
  let a₀ : M ⟶ P := ModuleCat.ofHom a
  let b₀ : P ⟶ HomBimodule.obj (k := k) X Z := ModuleCat.ofHom (X := P) (Y := HomBimodule.obj (k := k) X Z) b
  have he : a₀ ≫ b₀ = f := ModuleCat.hom_ext hab
  refine ⟨Enveloping.evalObj X P, inferInstance, inferInstance,
    (Enveloping.evalMap X a₀).hom, (uncurry b₀).hom, ?_⟩
  exact ModuleCat.hom_ext_iff.mp ((uncurry_precompose a₀ b₀).symm.trans (congrArg uncurry he))

omit [FiniteDimensional k X] in
include tR tS in

lemma factors_of_uncurry [Module.Projective Rᵐᵒᵖ (Enveloping.Obj M)]
    {f : M ⟶ HomBimodule.obj (k := k) X Z}
    (hf : (uncurry f).hom ∈ projectiveFactors (k := k)) :
    f.hom ∈ projectiveFactors (k := k) := by
  obtain ⟨P,hPf,hPp,a,b,hab⟩ := hf
  let := hPf
  let := hPp
  let : Module.Injective S S := tS.injective
  let : Module.Injective S P := injective_of_finite_projective
  let J := ModuleCat.of (Enveloping.Alg k S R)
    (Fin (Module.finrank k M) → Enveloping.Alg k S R)
  let i : M ⟶ J := ModuleCat.ofHom ((tS.tensor tR.op).freeEmbedding (M := M))
  have hi : Function.Injective i := (tS.tensor tR.op).freeEmbedding_injective
  have hei := Enveloping.evalMap_injective X tR i hi
  obtain ⟨a',ha'⟩ := Module.Injective.extension_property S P (Enveloping.evalObj X M)
    (Enveloping.evalObj X J) (Enveloping.evalMap X i).hom hei a
  let ag : Enveloping.evalObj X J ⟶ Z := ModuleCat.ofHom (b.comp a')
  let g : J ⟶ HomBimodule.obj (k := k) X Z := curry ag
  have hcomp : i ≫ g = f := by
    apply (equiv (k := k)).injective
    change uncurry (i ≫ g) = uncurry f
    rw [uncurry_precompose]
    change Enveloping.evalMap X i ≫ uncurry (curry ag) = _
    rw [uncurry_curry]
    apply ModuleCat.hom_ext
    change (b.comp a').comp (Enveloping.evalMap X i).hom = (uncurry f).hom
    rw [LinearMap.comp_assoc, ha', hab]
  exact ⟨J, inferInstance, inferInstance, i.hom, g.hom, ModuleCat.hom_ext_iff.mp hcomp⟩

include tR tS in

lemma factors_iff_uncurry [Module.Projective Rᵐᵒᵖ (Enveloping.Obj M)]
    (f : M ⟶ HomBimodule.obj (k := k) X Z) :
    f.hom ∈ projectiveFactors (k := k) ↔ (uncurry f).hom ∈ projectiveFactors (k := k) :=
  ⟨uncurry_factors, factors_of_uncurry tR tS⟩

def linearEquiv : (M →ₗ[Enveloping.Alg k S R] HomBimodule.obj (k := k) X Z) ≃ₗ[k]
    (Enveloping.evalObj X M →ₗ[S] Z) :=
  (ModuleCat.homLinearEquiv (S := k)).symm.trans
    ((equiv (k := k)).trans (ModuleCat.homLinearEquiv (S := k)))

def stableEquiv [Module.Projective Rᵐᵒᵖ (Enveloping.Obj M)] :
    StableHom (k := k) (R := Enveloping.Alg k S R) (M := M)
      (N := HomBimodule.obj (k := k) X Z) ≃ₗ[k]
    StableHom (k := k) (R := S) (M := Enveloping.evalObj X M) (N := Z) :=
  Submodule.Quotient.equiv _ _ (linearEquiv (k := k)) (by
    ext g
    constructor
    · rintro ⟨f,hf,rfl⟩
      exact (factors_iff_uncurry tR tS (ModuleCat.ofHom (X := M) (Y := HomBimodule.obj (k := k) X Z) f)).mp hf
    · intro hg
      obtain ⟨f,rfl⟩ := (linearEquiv (k := k) (M := M) (X := X) (Z := Z)).surjective g
      exact ⟨f,(factors_iff_uncurry tR tS (ModuleCat.ofHom (X := M) (Y := HomBimodule.obj (k := k) X Z) f)).mpr hg,rfl⟩)

end Tachikawa.BimoduleTensorHom



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))
  (X : ModuleCat.{0} R) (Z : ModuleCat.{0} S) [FiniteDimensional k X]

include t u in

theorem evaluation_nonzero_of_syzygy_composition
    (U M T : FiniteModule k (Enveloping.Alg k S R))
    [Module.Projective Rᵐᵒᵖ (Enveloping.Obj U.obj)]
    [Module.Projective Rᵐᵒᵖ (Enveloping.Obj M.obj)]
    (e : T.obj ≃ₗ[Enveloping.Alg k S R] HomBimodule.obj (k := k) X Z)
    (g : U.obj →ₗ[Enveloping.Alg k S R] M.obj)
    (phi : M.obj →ₗ[Enveloping.Alg k S R] T.syzygy.obj)
    (hn : phi.comp g ∉ projectiveFactors (k := k)) :
    (Enveloping.evalMap X (ModuleCat.ofHom (X := U.obj) (Y := M.obj) g)).hom
      ∉ projectiveFactors (k := k) := by
  let tau := Enveloping.envelopingForm u t
  let : Module.Injective (Enveloping.Alg k S R) (Enveloping.Alg k S R) := tau.injective
  let PU := ModuleCat.of (Enveloping.Alg k S R)
    (Fin (Module.finrank k U) → Enveloping.Alg k S R)
  let PM := ModuleCat.of (Enveloping.Alg k S R)
    (Fin (Module.finrank k M) → Enveloping.Alg k S R)
  let PT := ModuleCat.of (Enveloping.Alg k S R) (Fin T.cover.rank → Enveloping.Alg k S R)
  obtain ⟨h,g',hu,hl⟩ := exists_exact_square_down (P := PU) (Q := PM)
    (U.embed tau) (U.cosyzygyProjection tau) (U.embed_injective tau)
    (U.cosyzygyProjection_exact tau) (U.cosyzygyProjection_surjective tau)
    (M.embed tau) (M.cosyzygyProjection tau) (M.cosyzygyProjection_exact tau) g
  obtain ⟨h',psi,hu',hl'⟩ := exists_exact_square_down (P := PM) (Q := PT)
    (M.embed tau) (M.cosyzygyProjection tau) (M.embed_injective tau)
    (M.cosyzygyProjection_exact tau) (M.cosyzygyProjection_surjective tau)
    T.syzygyInclusion T.cover.map T.syzygyInclusion_exact phi
  have hnon : psi.comp g' ∉ projectiveFactors (k := k) := by
    apply mt (exact_square_factors_iff (P := PU) (Q := PT)
      (U.embed tau) (U.cosyzygyProjection tau) (U.embed_injective tau)
      (U.cosyzygyProjection_exact tau) (U.cosyzygyProjection_surjective tau)
      T.syzygyInclusion T.cover.map T.syzygyInclusion_injective
      T.syzygyInclusion_exact T.cover.surjective
      (phi.comp g) (h'.comp h) (psi.comp g') ?_ ?_).mpr hn
    · rw [LinearMap.comp_assoc,hu,← LinearMap.comp_assoc,hu',LinearMap.comp_assoc]
    · rw [← LinearMap.comp_assoc,hl',LinearMap.comp_assoc,hl,← LinearMap.comp_assoc]
  intro hgeval
  have hshift : (Enveloping.evalMap X (ModuleCat.ofHom
      (X := (U.cosyzygy tau).obj) (Y := (M.cosyzygy tau).obj) g')).hom
        ∈ projectiveFactors (k := k) := by
    apply (Enveloping.eval_square_factors_iff t u X
      (ModuleCat.ofHom (X := U.obj) (Y := PU) (U.embed tau))
      (ModuleCat.ofHom (X := PU) (Y := (U.cosyzygy tau).obj) (U.cosyzygyProjection tau))
      (U.embed_injective tau) (U.cosyzygyProjection_exact tau) (U.cosyzygyProjection_surjective tau)
      (ModuleCat.ofHom (X := M.obj) (Y := PM) (M.embed tau))
      (ModuleCat.ofHom (X := PM) (Y := (M.cosyzygy tau).obj) (M.cosyzygyProjection tau))
      (M.embed_injective tau) (M.cosyzygyProjection_exact tau) (M.cosyzygyProjection_surjective tau)
      (ModuleCat.ofHom g) (ModuleCat.ofHom h) (ModuleCat.ofHom g')
      (ModuleCat.hom_ext hu) (ModuleCat.hom_ext hl)).mp hgeval
  let gt : (U.cosyzygy tau).obj ⟶ (M.cosyzygy tau).obj := ModuleCat.ofHom g'
  let psit : (M.cosyzygy tau).obj ⟶ HomBimodule.obj (k := k) X Z :=
    ModuleCat.ofHom (X := (M.cosyzygy tau).obj)
      (Y := HomBimodule.obj (k := k) X Z) (e.toLinearMap.comp psi)
  have hc : (BimoduleTensorHom.uncurry (gt ≫ psit)).hom ∈ projectiveFactors (k := k) := by
    rw [BimoduleTensorHom.uncurry_precompose]
    exact projectiveFactors_postcomp hshift (BimoduleTensorHom.uncurry psit).hom
  let : Module.Projective Rᵐᵒᵖ (Enveloping.Obj (U.cosyzygy tau).obj) :=
    Enveloping.cosyzygy_right_projective u t U
  have hh := BimoduleTensorHom.factors_of_uncurry t u hc
  have hh' := projectiveFactors_postcomp hh e.symm.toLinearMap
  apply hnon
  convert hh' using 1
  ext x
  change psi (g' x) = e.symm (e (psi (g' x)))
  exact (e.symm_apply_apply _).symm
end Tachikawa

end
end OAI

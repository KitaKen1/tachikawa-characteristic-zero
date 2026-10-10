import OAI.RingTheory.Tachikawa.Coresolution

/-! Characteristic-independent excerpt from OpenAI Math DerivedInduction.lean;
fixed commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Exact source range is recorded in vendor/openai-math/manifest.json.
Declarations unchanged; imports and outer wrappers replaced. -/
namespace OAI
noncomputable section

namespace Tachikawa
open CategoryTheory HomologicalComplex

def negUpDown : (ComplexShape.up ℤ).Embedding (.down ℤ) where
  f i := -i
  injective_f := neg_injective
  rel h := by change _+1=_ at h; change _+1=_; omega

instance : negUpDown.IsRelIff where
  rel' := by intro i j h; change (-j)+1=(-i) at h; change i+1=j; omega

def negDownUp : (ComplexShape.down ℤ).Embedding (.up ℤ) where
  f i := -i
  injective_f := neg_injective
  rel h := by change _+1=_ at h; change _+1=_; omega

instance : negDownUp.IsRelIff where
  rel' := by intro i j h; change (-i)+1=(-j) at h; change j+1=i; omega

variable {C : Type*} [Category C] [Preadditive C]

abbrev reflectChain (K : ChainComplex C ℤ) : CochainComplex C ℤ := K.restriction negUpDown
abbrev reflectCochain (K : CochainComplex C ℤ) : ChainComplex C ℤ := K.restriction negDownUp
abbrev reflectChainMap {K L : ChainComplex C ℤ} (f : K ⟶ L) : reflectChain K ⟶ reflectChain L :=
  restrictionMap f negUpDown
abbrev reflectCochainMap {K L : CochainComplex C ℤ} (f : K ⟶ L) : reflectCochain K ⟶ reflectCochain L :=
  restrictionMap f negDownUp

lemma complex_d_transport (K : CochainComplex C ℤ) {i i' j j' : ℤ}
    (hi : i = i') (hj : j = j') :
    eqToHom (congrArg K.X hi) ≫ K.d i' j' = K.d i j ≫ eqToHom (congrArg K.X hj) := by
  subst i'; subst j'; simp

def reflectCochainIso (K : CochainComplex C ℤ) : reflectChain (reflectCochain K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun i => eqToIso (by change K.X (- -i) = K.X i; rw [neg_neg]))
    (by intro i j h; exact complex_d_transport K (neg_neg i) (neg_neg j))

lemma reflectCochainIso_natural {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    reflectChainMap (reflectCochainMap f) ≫ (reflectCochainIso L).hom =
      (reflectCochainIso K).hom ≫ f := by
  ext i
  change f.f (- -i) ≫ eqToHom (show L.X (- -i) = L.X i by simp) =
    eqToHom (show K.X (- -i) = K.X i by simp) ≫ f.f i
  simp

def reflectChainHomotopy {K L : ChainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (reflectChainMap f) (reflectChainMap g) where
  hom i j := h.hom (-i) (-j)
  zero i j hij := h.zero _ _ (by change ¬ (-i)+1=(-j); change ¬ j+1=i at hij; omega)
  comm i := by
    have hh := h.comm (-i)
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (-i) (-i-1) by change (-i-1)+1=(-i); omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (-i+1) (-i) by rfl)] at hh
    erw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i-1) i by change (i-1)+1=i; omega)]
    change f.f (-i) = K.d (-i) (-(i+1)) ≫ h.hom (-(i+1)) (-i) +
      h.hom (-i) (-(i-1)) ≫ L.d (-(i-1)) (-i) + g.f (-i)
    have hi : -(i+1) = -i-1 := by omega
    have hj : -(i-1) = -i+1 := by omega
    rw [hi,hj]
    exact hh

end Tachikawa

end
end OAI

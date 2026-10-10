import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.RingTheory.Artinian.Module

/-! A witness-independent statement of the general Artin-algebra
Auslander--Reiten conjecture. The pointwise signature below is extracted
from FormalConjectures/Paper/AuslanderReiten.lean at
d838afa7a62f66dc034c96fb011c10b9bde3f44c (Apache-2.0).
The upstream conjectural proof is not imported. The universal claim is
specialized to universe zero; a counterexample here suffices to refute
the universal conjecture. No commutativity hypothesis on Lambda is added. -/
namespace TachikawaCharZero.FCStatement
open CategoryTheory
universe u

section ArtinAlgebra

variable (Λ : Type u) [Ring Λ] (M : Type u) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]

/-- The fixed upstream theorem signature, with its premises quantified. -/
def artinCase (A : Type u) [CommRing A] [IsArtinianRing A] [Algebra A Λ]
    [Module.Finite A Λ] : Prop :=
  ∀ (hMΛ : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of Λ M) (ModuleCat.of Λ Λ) i))
    (hMM : ∀ i > 0, Subsingleton (Abelian.Ext (ModuleCat.of Λ M) (ModuleCat.of Λ M) i)),
    Module.Projective Λ M

end ArtinAlgebra

/-- The general Artin-algebra conjecture at universe zero. -/
def ArtinAuslanderReiten : Prop :=
  ∀ (Λ : Type) [Ring Λ] (M : Type) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]
    (A : Type) [CommRing A] [IsArtinianRing A] [Algebra A Λ] [Module.Finite A Λ],
    artinCase Λ M A

end TachikawaCharZero.FCStatement

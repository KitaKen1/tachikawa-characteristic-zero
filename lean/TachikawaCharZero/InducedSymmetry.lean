import TachikawaCharZero.StartingSymmetric
import TachikawaCharZero.PeriodicExt

/-! The corner construction uses the same rational trivial extension as
the previously checked symmetrizing form, with definitionally equal actions. -/
namespace TachikawaCharZero.Induced

theorem T_symmetric : OAI.Tachikawa.SymmetricOver ℚ T := Starting.T_symmetric
theorem T_injective : Module.Injective T T := Starting.T_injective
theorem T_finrank : Module.finrank ℚ T=20 := Starting.T_finrank

end TachikawaCharZero.Induced

import Lean4Lean.Theory.Typing.AnchoredNativePrefixPlan
import Lean4Lean.Theory.Typing.AnchoredNativeSupportedReplay
import Lean4Lean.Theory.Typing.AnchoredNativeConstantTree

/-! The shared equation/native prefix is copied from the actual native
argument tuple. Its fitting entries are restricted from that tuple, rather
than interpreted again under an invented type support. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- A concrete prefix replay has only source syntax/equalities as premises;
its raw and semantic fitting entries are produced by `canonical` from the
original full native tuple. -/
def NativeSupportedReplay.ofNativePrefix
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {domains : List VExpr} {locals : List Nat}
    (values : List VExpr) (available : Valuation) (length : values.length = domains.length)
    (count : Nat) (bound : count ≤ domains.length) :
    NativeSupportedReplay sourceEnv env U registry target domains.reverse locals
      (nativeCaptureSubst values) available (domains.take count).reverse
      (nativePrefixPlan (domains.length - count) (domains.take count).reverse)
      (Subst.lift_l (.skipN .refl (domains.length - count)) (nativeCaptureSubst values))
      (List.range (domains.take count).reverse.length)
      (fun index => available (index + (domains.length - count))) := by
  have source : domains.reverse = (domains.drop count).reverse ++ (domains.take count).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  have laterLength : (domains.drop count).reverse.length = domains.length - count := by simp
  have prefixLength : (domains.take count).reverse.length = count := by simp [Nat.min_eq_left bound]
  have result := NativeSupportedReplay.commonPrefix (sourceEnv := sourceEnv) (env := env)
    (U := U) (registry := registry) (target := target) (argumentLocals := locals)
    (argumentAvailable := available) source (by rw [laterLength])
    (nativePrefixPlan_count (domains.length - count) (domains.take count).reverse)
    (nativePrefixPlan_added (domains.length - count) (domains.take count).reverse (nativeCaptureSubst values))
    (by
      rw [laterLength]
      exact nativePrefixPlan_captures _ _ _ (by rw [prefixLength]; omega))
  simpa only [laterLength] using result

end Lean4Lean.AnchoredSource.Adapted

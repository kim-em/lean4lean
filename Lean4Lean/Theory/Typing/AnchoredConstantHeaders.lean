import Lean4Lean.Theory.Typing.ConstantHeaderProvenance
import Lean4Lean.Theory.Typing.AnchoredBoundedStage

/-! The constant-header component of declaration induction. Entries retain
actual original formation stages. The constructors below populate this component
from the completed theorem of each preceding header, including simultaneous
family and constructor blocks; it is not a supplier of semantic leaf results.
-/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics

/-- Each installed constant retains the completed theorem for the environment
where its type was originally checked, with that theorem's own control filter. -/
def OriginalConstantHeaders (source env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) : Prop :=
  ∀ name value, source.constants name = some value →
    ∃ origin : ConstantHeaderOrigin source name value, ∃ control : Name → Bool,
      ∀ fuel, ∀ {Γ l r A}, origin.source.IsDefEqStrong U Γ l r A →
        Joint control fuel env U registry Γ l r A

namespace OriginalConstantHeaders
variable {source extended env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

theorem empty : OriginalConstantHeaders .empty env U registry := by
  intro name value lookup
  cases lookup

/-- Metadata and equations preserve the exact formation origins. -/
theorem extend (headers : OriginalConstantHeaders source env U registry)
    (below : source ≤ extended) (same : extended.constants = source.constants) :
    OriginalConstantHeaders extended env U registry := by
  intro name value lookup
  rw [same] at lookup
  obtain ⟨origin, control, earlier⟩ := headers name value lookup
  exact ⟨origin.extend below, control, earlier⟩

theorem addConst (headers : OriginalConstantHeaders source env U registry)
    (formed : source.Ordered) (type : value.WF source)
    (installed : source.addConst name value = some extended)
    {control : Name → Bool}
    (earlier : ∀ fuel, ∀ {Γ l r A}, source.IsDefEqStrong U Γ l r A →
      Joint control fuel env U registry Γ l r A) :
    OriginalConstantHeaders extended env U registry := by
  intro selected constant lookup
  have old := lookup
  rw [VEnv.addConst_constants_eq installed] at old
  dsimp only at old
  by_cases same : name = selected
  · subst selected
    simp only [ite_true, Option.some.injEq] at old
    subst constant
    have fresh : source.constants name = none := by
      unfold VEnv.addConst at installed
      split at installed <;> simp_all
    exact ⟨⟨source, formed, type, VEnv.addConst_le installed, fresh, lookup⟩,
      control, earlier⟩
  · rw [if_neg same] at old
    obtain ⟨origin, priorControl, prior⟩ := headers selected constant old
    exact ⟨origin.extend (VEnv.addConst_le installed), priorControl, prior⟩

/-- All types in the block use the original common formation environment.
No fabricated theorem for the incremental installation prefixes is needed. -/
theorem addConstVals (headers : OriginalConstantHeaders source env U registry)
    (formed : source.Ordered) (types : ∀ entry ∈ values, entry.toVConstant.WF source)
    (installed : source.addConstVals values = some extended)
    {control : Name → Bool}
    (earlier : ∀ fuel, ∀ {Γ l r A}, source.IsDefEqStrong U Γ l r A →
      Joint control fuel env U registry Γ l r A) :
    OriginalConstantHeaders extended env U registry := by
  intro name value lookup
  rcases VEnv.addConstVals_lookup_origin installed lookup with old | added
  · obtain ⟨origin, priorControl, prior⟩ := headers name value old
    exact ⟨origin.extend (VEnv.addConstVals_le installed), priorControl, prior⟩
  · obtain ⟨entry, member, rfl, rfl⟩ := added
    exact ⟨ConstantHeaderOrigin.ofBlock formed types installed member, _, earlier⟩

end OriginalConstantHeaders
end Lean4Lean.AnchoredSource.Adapted.Staged

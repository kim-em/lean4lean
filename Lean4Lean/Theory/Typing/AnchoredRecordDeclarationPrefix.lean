import Lean4Lean.Theory.Typing.AnchoredConstructorPacketCoverage
import Lean4Lean.Theory.Typing.AnchoredNativeExtensionalRows

/-! A record observer exposes the exact declaration prefix needed to replay
a dependent field template. Parameter requests come from its actual literal
family code, and preceding field requests come from its retained projections.
All evidence descends from the real private display world. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
open private family_lift from Lean4Lean.Theory.Typing.AnchoredDataLaws
set_option backward.isDefEq.respectTransparency false

theorem RecordWitness.declarationPrefix
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {left right : VExpr} {demand : RecordData (Profile n)}
    {levels : List VLevel} {params indices : List VExpr}
    (witness : RecordWitness env U registry (relations env U registry n) Γ left right
      (mkApps (.const demand.family.name levels) (params ++ indices)) demand)
    (count : Nat)
    (positions : (demand.fields.take count).map Prod.fst = List.range count) :
    Arguments env U (relations env U registry n) Γ
      (demand.family.arguments.take params.length ++ (demand.fields.take count).map Prod.snd)
      (params ++ etaFields demand.family.name count left)
      (params ++ etaFields demand.family.name count right) := by
  have family := witness.typeCode
  simp only [family_lift, List.map_append] at family
  have paramsAtWorld := FamilyRelation.literalArguments henv hscoped
    (witness.insertion.targetWF henv witness.baseWF)
    (family := demand.family.rename witness.map) family
  have paramsAtBase : Arguments env U (relations env U registry n) Γ
      demand.family.arguments (params ++ indices) (params ++ indices) := by
    apply Arguments.mixedBack henv hscoped witness.insertion
    rw [List.map_append]
    exact paramsAtWorld
  have parameters := paramsAtBase.take params.length
  simp only [List.take_left] at parameters
  have fieldsAtBase : Arguments env U (relations env U registry n) Γ
      (demand.fields.map Prod.snd)
      (demand.fields.map (fun entry => .proj demand.family.name entry.1 left))
      (demand.fields.map (fun entry => .proj demand.family.name entry.1 right)) := by
    apply Arguments.mixedBack henv hscoped witness.insertion
    simpa only [List.map_map, Function.comp_def, VExpr.lift'] using witness.fields
  have fields := fieldsAtBase.take count
  simp only [← List.map_take] at fields
  have projected (major : VExpr) :
      (demand.fields.take count).map (fun entry => .proj demand.family.name entry.1 major) =
        etaFields demand.family.name count major := by
    rw [etaFields, ← positions, List.map_map]
    rfl
  rw [projected, projected] at fields
  exact parameters.append fields

end Lean4Lean.AnchoredSemantics.RankedData

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Replay the original declaration field template using only the finite
parameter and preceding-field requests supplied by the actual record. The
result is still a template certificate; source reification must account for
the original parameter and projection expressions explicitly. -/
theorem FamilySeededCodeRows.recordFieldCode
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} (formed : OnCtx target (env.IsType U))
    {expression : VExpr} {domains : List VExpr} {keys : List FamilyKey} {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required [] []
      (nativeCaptureSubst []) (fun _ => []) expression domains keys)
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N)
    {left right : VExpr} {demand : RecordData (Profile N)}
    {levels : List VLevel} {params indices : List VExpr}
    (witness : RankedData.RecordWitness env U registry (relations env U registry N) target left right
      (mkApps (.const demand.family.name levels) (params ++ indices)) demand)
    (count : Nat)
    (positions : (demand.fields.take count).map Prod.fst = List.range count)
    (requests : FamilyKey.uniform N keys bounded =
      demand.family.arguments.take params.length ++ (demand.fields.take count).map Prod.snd)
    {fieldType : VExpr} {level : VLevel} {support : Profile n}
    (original : OriginalTypePayload sourceEnv env U registry domains.reverse fieldType (.sort level))
    (certificate : CodeCert env U registry target rows.terminalLocals
      (nativeCaptureSubst (keys.map (·.key.anchor))) fieldType support required) :
    Nonempty (CodeTransferResult env U registry target rows.terminalLocals
      (nativeCaptureSubst (params ++ RankedData.etaFields demand.family.name count left))
      (nativeCaptureSubst (params ++ RankedData.etaFields demand.family.name count right))
      rows.terminalValuation fieldType fieldType support) := by
  have arguments := witness.declarationPrefix henv hscoped count positions
  rw [← requests] at arguments
  have initial : FamilyPrefixAlignment env U registry [] target []
      (nativeCaptureSubst []) (nativeCaptureSubst []) (nativeCaptureSubst []) (fun _ => []) :=
    ⟨.nil, .nil, .nil, .nil⟩
  have closed : Valuation.AtomClosed (fun _ => []) := by intro _ _ member; cases member
  have result := rows.transferTerminalCode henv hscoped hle closed formed initial
    (FamilyArguments.of_uniform henv formed N bounded arguments)
    (by simpa only [List.append_nil] using original)
    (by simpa only [familySubst_native, List.nil_append] using certificate)
  simpa only [familySubst_native, List.nil_append] using result

end Lean4Lean.AnchoredSource.Adapted

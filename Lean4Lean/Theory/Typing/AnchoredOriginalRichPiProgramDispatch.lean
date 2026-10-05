import Lean4Lean.Theory.Typing.AnchoredOriginalLegacyPiStoredRow
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeRankedRowActions
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiProgramCursor

/-! Execute the native alternative of the actual retained Pi program.
Legacy alternatives select their literal stored body too. Only charged
alternatives retain a pending program; no branch fabricates a new body of
the same recipe. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

inductive RichPiProgramStep (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target source : List VExpr)
    (A B : VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (budget : Nat) {n : Nat} (selectedKey : Key n) (selectedResult : Profile n) : Type where
  | native
      {domainNode : EndpointState sourceEnv U source A (.sort u)}
      {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
      (domain : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint)
      (rows : RichRows sourceEnv env U registry target domainNode bodyNode locals σ relevant ambient table footprint)
      (pending : RankedPendingNativeRow env U registry target table relevant selectedKey selectedResult)
      (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
        pending.oldKey pending.oldResult)
      (sameDomain : HEq row.domain domain)
      (smaller : sizeOf row.body < budget)
      (depth : ∀ policy, max (row.domain.headDepth policy) (row.body.headDepth policy) ≤
        max (domain.headDepth policy) (rows.headDepth policy)) :
      RichPiProgramStep sourceEnv env U registry target source A B locals σ available budget selectedKey selectedResult
  | legacy (selection : LegacyPiSelection env U registry target locals σ A B available budget
      selectedKey selectedResult) :
      RichPiProgramStep sourceEnv env U registry target source A B locals σ available budget selectedKey selectedResult
  | recipe {selectedRows : List (Key n × Profile n)} {selectedSupport : Profile n}
      (code : RichCodeRecipe env U registry target source locals σ (.forallE A B) relevant profile footprint)
      (resources : footprint.Available available) (member : atom ∈ profile.atoms)
      (path : GeneralOutputPath env U registry target atom (n := n + 1)
        (AtomData.pi selectedDomain selectedBody selectedSupport selectedRows))
      (selected : (selectedKey, selectedResult) ∈ selectedRows)
      (bounded : sizeOf code ≤ budget) :
      RichPiProgramStep sourceEnv env U registry target source A B locals σ available budget selectedKey selectedResult

/-- Actual cursor dispatch; only a literal retained native body is executed.
Every other alternative reports its real program, not a semantic supplier. -/
theorem RichPiProgramOrigin.dispatch
    {selectedRows : List (Key n × Profile n)} {selectedSupport : Profile n}
    (origin : RichPiProgramOrigin sourceEnv env U registry target source A B locals σ available budget (n := n + 1)
      (AtomData.pi selectedDomain selectedBody selectedSupport selectedRows))
    (selected : (key, result) ∈ selectedRows) :
    Nonempty (RichPiProgramStep sourceEnv env U registry target source A B locals σ available budget key result) := by
  obtain ⟨rank, atom, leaf, path, bounded⟩ := origin
  cases leaf with
  | native hu hv domain guard rows resources =>
    obtain ⟨pending, row, same, smaller, depth⟩ := rows.pathNativeCursor domain
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member)) path selected
    refine ⟨.native domain rows pending row same ?_ depth⟩
    simp only [RichPiProgramLeaf.programSize] at bounded
    have rowLess : sizeOf rows < sizeOf (RichCert.pi hu hv domain guard rows) := by simp_wf; omega
    omega
  | legacyCode certificate resources member =>
    have limit : sizeOf certificate ≤ budget := by simpa only [RichPiProgramLeaf.programSize] using bounded
    obtain ⟨origin⟩ := certificate.legacyPiPrograms resources budget limit _ member
    obtain ⟨selection⟩ := origin.selectRow path selected
    exact ⟨.legacy selection⟩
  | legacyObs observation resources member =>
    have limit : sizeOf observation ≤ budget := by simpa only [RichPiProgramLeaf.programSize] using bounded
    obtain ⟨origin⟩ := observation.legacyPiPrograms resources budget limit _ member
    obtain ⟨selection⟩ := origin.selectRow path selected
    exact ⟨.legacy selection⟩
  | recipe code resources member => exact ⟨.recipe code resources member path selected (by simpa only [RichPiProgramLeaf.programSize] using bounded)⟩

/-- Enter from the actual rich certificate grammar, so all its wrapper actions
feed the exhaustive native path interpreter above. -/
theorem RichCert.piProgramStep
    {n : Nat} {profile : Profile (n + 1)} {key : Key n} {result : Profile n}
    (henv : env.Ordered)
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (resources : footprint.Available available)
    {selectedRows : List (Key n × Profile n)} {selectedSupport : Profile n}
    (present : AtomData.pi selectedDomain selectedBody selectedSupport selectedRows ∈ profile.atoms)
    (selected : (key, result) ∈ selectedRows) :
    Nonempty (RichPiProgramStep sourceEnv env U registry target source A B locals σ available
      (sizeOf certificate) key result) := by
  obtain ⟨origin⟩ := certificate.piProgramOrigins henv resources (sizeOf certificate)
    (Nat.le_refl _) _ present
  exact origin.dispatch selected

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource

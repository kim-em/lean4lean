import Lean4Lean.Theory.Typing.ProjectionCornerIndexedElim
import Lean4Lean.Theory.Typing.ProjectionCornerCaseElim
import Lean4Lean.Theory.Inductive.CaseRegistration
import Lean4Lean.Theory.Typing.CaseSourceSort

/-! # The projection-walk corner in every well-formed environment with canonical choice

Every registered structure has a registered case eliminator with the structure among its
original families (`VEnv.WF.projections_eliminated`), whose certificate includes the header
agreement of its original families (`VEnv.WF.eliminator_headerAgreement`). Under canonical choice
the binder reached by a projection walk past a field whose projection fails the universe guard is
therefore inhabited, for structures with and without indices
(`VEnv.corner_inhabit_elim`). -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

variable {env : VEnv} {U : Nat}

/-- The header-agreement hypothesis of the indexed corner, from the registration certificate. -/
theorem WF.corner_header {env : VEnv} (henv : env.WF) {key : Name} {schema : CaseSchema}
    (hel : env.eliminators key schema) {S : Name} (hS : S ∈ schema.originalFamilies) :
    ∀ owner : Fin schema.signature.families.size,
      schema.signature.families[owner].name = S →
      ∃ RP RI, schema.signature.params.mapM schema.restoration.expr = some RP ∧
        schema.signature.families[owner].indices.mapM schema.restoration.expr = some RI ∧
        ∃ tc, env.constants S = some tc ∧ env.IsDefEqU schema.signature.uvars [] tc.type
          (VExpr.wrapForalls (RP ++ RI) (.sort schema.signature.families[owner].resultLevel)) := by
  intro owner hname
  obtain ⟨base, source, block, -, hle, hcert, ⟨RP, hRP, hhdr⟩, hconsts⟩ :=
    henv.eliminator_headerAgreement hel
  obtain ⟨RI, hRI, hagree⟩ := hhdr owner
  refine ⟨RP, RI, hRP, hRI, ?_⟩
  obtain ⟨expanded, auxiliaries, hdata, -, -, hnames, -⟩ := hcert
  rw [hnames] at hS
  obtain ⟨type, htype, rfl⟩ := List.mem_map.mp hS
  obtain ⟨envTypes, htypes, hdefeq⟩ := hagree type htype hname.symm
  have hvalues : ∀ value ∈ source.typeConstants,
      env.constants value.name = some value.toVConstant := by
    intro value hvalue
    apply hconsts
    rw [hdata.types]
    exact List.mem_append_left _ hvalue
  have htypesLE : envTypes ≤ env := addConstVals_le_target hle htypes hvalues
  have hlookup : env.constants type.name = some type.toVConstant :=
    hvalues type.toVConstVal (List.mem_map.mpr ⟨type, htype, rfl⟩)
  have huvars : schema.signature.uvars = source.uvars := hdata.model.uvars.trans hdata.uvars
  refine ⟨type.toVConstant, hlookup, ?_⟩
  rw [huvars]
  exact hdefeq.mono htypesLE

/-- **The projection-walk corner is inhabited** in every well-formed environment with canonical
choice: the binder `D` reached by the walk over a registered structure's constructor telescope,
past a field whose projection fails the universe guard, is inhabited in the walk's context. -/
theorem WF.corner_inhabit_choice (henv : env.WF) (hch : env.HasCanonicalChoice)
    {Δ : List VExpr} (hΔ : OnCtx Δ (env.IsType U))
    {S : Name} {info : VProjectionInfo} (hinfo : env.projections S info)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlslen : ls.length = info.uvars)
    {T₀ : VExpr} (hT₀ : VExpr.LEquiv U T₀ (info.ctorType.instL ls))
    {ps idx : List VExpr} (hpl : ps.length = info.nparams)
    {e' : VExpr} (he' : env.HasType U Δ e' (VExpr.mkApps (.const S ls) (ps ++ idx)))
    {j : Nat} {D body' : VExpr}
    (hwalk : VProjectionInfo.instantiateProjectionParameters T₀
      (ps ++ (List.range j).map fun k => .proj S k e') = some (.forallE D body'))
    (hD : env.IsType U Δ D)
    (hguard : ∀ u, env.HasType U Δ D (.sort u) →
      ¬ ((info.resultLevel.inst ls).IsNeverZero ∨ u ≈ .zero)) :
    ∃ d, env.HasType U Δ d D := by
  obtain ⟨key, schema, hel, hS⟩ := henv.projections_eliminated hinfo
  exact corner_inhabit_elim henv hch hΔ hinfo hls hlslen hT₀ hpl he' hwalk hD hguard
    hel hS (henv.corner_header hel hS)

end VEnv
end Lean4Lean

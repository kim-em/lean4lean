import Lean4Lean.Theory.Typing.CaseResult
import Lean4Lean.Theory.Inductive.ProjectionProgramLemmas

/-! Typing of the actual lambda programs used by projection abbreviations. -/

namespace Lean4Lean
namespace VExpr

private theorem liftN_wrapLams_shape (domains : List VExpr) (body : VExpr) (n k : Nat) :
    ∃ domains', domains'.length = domains.length ∧
      (wrapLams domains body).liftN n k =
        wrapLams domains' (body.liftN n (k + domains.length)) := by
  induction domains generalizing k with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons domain domains ih =>
    obtain ⟨domains', hlen, heq⟩ := ih (k + 1)
    refine ⟨domain.liftN n k :: domains', by simp [hlen], ?_⟩
    change VExpr.lam (domain.liftN n k) ((wrapLams domains body).liftN n (k + 1)) = _
    rw [heq]
    simp only [wrapLams, List.foldr_cons, List.length_cons]
    congr 3 <;> omega

private theorem instOuter_liftN_same (body : VExpr) (n : Nat) :
    (body.liftN n n).instOuter (bvarRange n n) = body := by
  rw [instOuter_eq_subst, liftN_subst]
  conv => rhs; rw [← subst_id (e := body)]
  congr 1
  funext i
  simp only [Subst.lift_l, Lift.liftVar_consN_skipN]
  by_cases hi : i < n
  · rw [liftVar_lt hi, Subst.ofList_lt _ (by simpa using hi)]
    simp only [bvarRange_length]
    rw [bvarRange_getElem n n (n - 1 - i) (by omega)]
    change VExpr.bvar (n - 1 - (n - 1 - i)) = VExpr.bvar i
    congr 1
    omega
  · rw [liftVar_le (Nat.le_of_not_gt hi), Subst.ofList_ge _ (by simp)]
    simp [Subst.id]

end VExpr
namespace VEnv
open VExpr InductiveSignature InductiveSignature.CaseSchema
variable {env : VEnv} {U : Nat}

/-- A lifted motive applied to the enclosing telescope variables returns its
original body. Both its beta equality and result typing come from the actual
application's typing. -/
theorem HasType.projectionMotive_result (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {domains : List VExpr} {body term : VExpr}
    (H : env.HasType U Γ term
      (mkApps ((wrapLams domains body).liftN domains.length)
        (bvarRange domains.length domains.length))) :
    env.HasType U Γ term body := by
  obtain ⟨domains', hlen, hshape⟩ := liftN_wrapLams_shape domains body domains.length 0
  obtain ⟨u, hmotive⟩ := H.isType henv.ordered hΓ
  have hwf : VExpr.WF env U Γ (mkApps
      (wrapLams domains' (body.liftN domains.length domains.length))
      (bvarRange domains.length domains.length)) := by
    simpa only [hshape, Nat.zero_add] using (show VExpr.WF env U Γ _ from ⟨_, hmotive⟩)
  have hbeta := hwf.beta_wrapLams henv hΓ (by simp [hlen])
  rw [instOuter_liftN_same] at hbeta
  apply H.defeqU_r henv hΓ
  simpa only [hshape, Nat.zero_add] using hbeta

private theorem vars_bvarRange (count below : Nat) :
    vars count below = bvarRange count (count + below) := by
  apply List.ext_getElem
  · simp [vars, bvarRange]
  · intro i hi hi'
    simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range]
    rw [bvarRange_getElem count (count + below) i (by simpa [vars] using hi)]
    simp only [List.length_range]
    have : i < count := by simpa [vars] using hi
    congr 1
    omega

private theorem vars_with_major (count : Nat) :
    vars count 1 ++ [.bvar 0] = bvarRange (count + 1) (count + 1) := by
  have h : vars count 1 ++ vars 1 0 = vars (count + 1) 0 := by
    rw [Nat.add_comm count 1]
    simp [vars, List.range_add, List.map_append, List.map_map]
  rw [← Nat.add_zero (count + 1), ← vars_bvarRange]
  exact h

private theorem wrapLams_retype (henv : env.WF) :
    ∀ {domains : List VExpr} {Γ : List VExpr} {body resultType : VExpr},
      OnCtx Γ (env.IsType U) → VExpr.WF env U Γ (wrapLams domains body) →
      env.HasType U (domains.reverse ++ Γ) body resultType →
      env.HasType U Γ (wrapLams domains body) (wrapForalls domains resultType) := by
  intro domains
  induction domains with
  | nil => intro Γ body resultType _ _ h; exact h
  | cons domain domains ih =>
    intro Γ body resultType hΓ h hresult
    obtain ⟨⟨_, hd⟩, hb⟩ := h.lam_inv henv.ordered hΓ
    have hΓ' : OnCtx (domain :: Γ) (env.IsType U) := ⟨hΓ, _, hd⟩
    exact .lam hd (ih hΓ' hb (by simpa [List.reverse_cons, List.append_assoc] using hresult))

/-- Every well-typed generated step has its generated dependent function
type. The conclusion does not accept a caller-chosen annotation. -/
theorem HasType.projectionStep_type (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {data : ProjectionData} {levels : List VLevel} {domain : VExpr} {target : VLevel}
    {previous : List ProjectionFunction}
    (hlookup : env.eliminators block schema)
    (hp : data.params.length = schema.signature.params.length)
    (hi : data.indices.length = schema.signature.families[owner].indices.length)
    (hc : (schema.view owner).constructors.size = 1)
    (H : VExpr.WF env U Γ (data.step block owner.val levels domain target previous).value) :
    env.HasType U Γ (data.step block owner.val levels domain target previous).value
      (data.step block owner.val levels domain target previous).type := by
  let ds := data.params ++ data.indices ++ [data.major]
  let fieldType := data.fieldTarget domain previous
  let motive := wrapLams (data.indices ++ [data.major]) fieldType
  let minor := wrapLams data.fields (.bvar (data.fields.length - 1 - previous.length))
  let below := data.indices.length + 1
  let body := mkApps (.elim block owner.val (target :: levels))
    (vars data.params.length below ++ [motive.liftN below, minor.liftN below] ++
      vars data.indices.length 1 ++ [.bvar 0])
  change VExpr.WF env U Γ (wrapLams ds body) at H
  obtain ⟨resultType, ht⟩ := H.wrapLams_type henv hΓ
  obtain ⟨hctx, hbody⟩ := ht.wrapLams_inv henv hΓ
  have hcase := HasType.caseResult_motive henv hctx (owner := owner) (packed := target :: levels) hlookup
    (params := vars data.params.length below) (motive := motive.liftN below)
    (minors := [minor.liftN below]) (indices := vars data.indices.length 1)
    (major := .bvar 0)
    (by simpa [vars] using hp) (by simpa using hc.symm) (by simpa [vars] using hi)
    (by simpa only [body, List.append_assoc, List.singleton_append] using
      (show VExpr.WF env U (ds.reverse ++ Γ) body from ⟨_, hbody⟩))
  rw [vars_with_major] at hcase
  have hresult : env.HasType U (ds.reverse ++ Γ) body fieldType := by
    apply HasType.projectionMotive_result henv hctx (domains := data.indices ++ [data.major])
    simpa only [motive, below, body, List.length_append, List.length_singleton,
      List.append_assoc, List.singleton_append] using hcase
  exact wrapLams_retype henv hΓ H hresult

/-- Every well-typed generated step has its generated dependent function
type. The conclusion does not accept a caller-chosen annotation. -/
theorem HasType.projectionStep_instL_type (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {data : ProjectionData} {levels : List VLevel} {domain : VExpr} {target : VLevel}
    {previous : List ProjectionFunction} {packed : List VLevel}
    (hlookup : env.eliminators block schema)
    (hp : data.params.length = schema.signature.params.length)
    (hi : data.indices.length = schema.signature.families[owner].indices.length)
    (hc : (schema.view owner).constructors.size = 1)
    (H : VExpr.WF env U Γ ((data.step block owner.val levels domain target previous).value.instL packed)) :
    env.HasType U Γ ((data.step block owner.val levels domain target previous).value.instL packed)
      ((data.step block owner.val levels domain target previous).type.instL packed) := by
  let params := data.params.map (VExpr.instL packed)
  let indices := data.indices.map (VExpr.instL packed)
  let major := data.major.instL packed
  let ds := params ++ indices ++ [major]
  let fieldType := (data.fieldTarget domain previous).instL packed
  let motive := wrapLams (indices ++ [major]) fieldType
  let minor := (wrapLams data.fields (.bvar (data.fields.length - 1 - previous.length))).instL packed
  let below := indices.length + 1
  let body := mkApps (.elim block owner.val (target.inst packed :: levels.map (·.inst packed)))
    (vars params.length below ++ [motive.liftN below, minor.liftN below] ++
      vars indices.length 1 ++ [.bvar 0])
  have hvars (n k : Nat) : (vars n k).map (VExpr.instL packed) = vars n k := by
    simp [vars, List.map_map, VExpr.instL]
  have hvalue : (data.step block owner.val levels domain target previous).value.instL packed =
      wrapLams ds body := by
    simp only [ProjectionData.step, instL_wrapLams, instL_mkApps, VExpr.instL,
      List.map_append, List.map_cons, List.map_nil, instL_liftN, hvars]
    simp only [ds, body, params, indices, major, motive, minor, below, fieldType,
      List.length_map, instL_wrapLams, VExpr.instL]
  rw [hvalue] at H
  obtain ⟨resultType, ht⟩ := H.wrapLams_type henv hΓ
  obtain ⟨hctx, hbody⟩ := ht.wrapLams_inv henv hΓ
  have hcase := HasType.caseResult_motive henv hctx (owner := owner) (packed := target.inst packed :: levels.map (·.inst packed)) hlookup
    (params := vars params.length below) (motive := motive.liftN below)
    (minors := [minor.liftN below]) (indices := vars indices.length 1)
    (major := .bvar 0)
    (by simpa [vars, params] using hp) (by simpa using hc.symm) (by simpa [vars, indices] using hi)
    (by simpa only [body, List.append_assoc, List.singleton_append] using
      (show VExpr.WF env U (ds.reverse ++ Γ) body from ⟨_, hbody⟩))
  rw [vars_with_major] at hcase
  have hresult : env.HasType U (ds.reverse ++ Γ) body fieldType := by
    apply HasType.projectionMotive_result henv hctx (domains := indices ++ [major])
    simpa only [motive, below, body, List.length_append, List.length_singleton,
      List.append_assoc, List.singleton_append] using hcase
  rw [hvalue]
  have htype : (data.step block owner.val levels domain target previous).type.instL packed =
      wrapForalls ds fieldType := by
    simp only [ProjectionData.step, instL_wrapForalls, List.map_append,
      List.map_cons, List.map_nil]
    rfl
  rw [htype]
  exact wrapLams_retype henv hΓ H hresult

/-- Universe-specializing a selected generated projection retains its exact
generated annotation whenever the resulting function is well typed. -/
theorem HasType.projectionPrefix_instL_type (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {uvars : Nat}
    {program : ProjectionFunction} {packed : List VLevel}
    (hlookup : env.eliminators block schema)
    (hgen : schema.projectionPrefix block owner uvars levels targets = some programs)
    (hselected : program ∈ programs)
    (H : VExpr.WF env U Γ (program.value.instL packed)) :
    env.HasType U Γ (program.value.instL packed) (program.type.instL packed) := by
  obtain ⟨data, hdata, domain, target, previous, rfl⟩ := projectionPrefix_step hgen hselected
  obtain ⟨hp, hi, hc⟩ := projectionData_counts hdata
  exact HasType.projectionStep_instL_type henv hΓ hlookup hp hi hc H

/-- An actual generated projection occurrence instantiates its own generated
telescope, including all dependent field substitutions retained in the type. -/
theorem HasType.projectionPrefix_instL_application_type (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {uvars : Nat}
    {program : ProjectionFunction} {packed : List VLevel} {args : List VExpr}
    (hlookup : env.eliminators block schema)
    (hgen : schema.projectionPrefix block owner uvars levels targets = some programs)
    (hselected : program ∈ programs)
    (hlen : args.length = schema.signature.params.length +
      schema.signature.families[owner].indices.length + 1)
    (H : VExpr.WF env U Γ (mkApps (program.value.instL packed) args)) :
    env.HasType U Γ (program.value.instL packed) (program.type.instL packed) ∧
    ∃ resultType, InstForallsC env U Γ (program.type.instL packed) args resultType ∧
      env.HasType U Γ (mkApps (program.value.instL packed) args) resultType := by
  have hf := HasType.projectionPrefix_instL_type henv hΓ hlookup hgen hselected
    (H.of_mkApps henv.ordered hΓ)
  refine ⟨hf, ?_⟩
  obtain ⟨data, hdata, domain, target, previous, rfl⟩ := projectionPrefix_step hgen hselected
  obtain ⟨hp, hi, _⟩ := projectionData_counts hdata
  apply HasType.mkApps_telescope henv hΓ hf H
  simp only [ProjectionData.step, instL_wrapForalls]
  have hlen' : args.length =
      ((data.params ++ data.indices ++ [data.major]).map (VExpr.instL packed)).length := by
    simp only [List.length_map, List.length_append, List.length_singleton]
    omega
  rw [hlen']
  exact takeForalls_wrapForalls _ _

end VEnv
end Lean4Lean

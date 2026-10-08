import Lean4Lean.Theory.Typing.SingletonExtraction.Recursor
import Lean4Lean.Theory.Typing.SingletonExtraction.RecursorLevels
import Lean4Lean.Theory.Typing.SingletonExtraction.RecursorScope
import Lean4Lean.Theory.Inductive.RecursorPrefixUnfolding
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.Strong

/-! # The singleton prefix program with `Eq`-cast extraction

The native singleton unfolding opens the unsupplied binders of a recursor
prefix, reconstructs the major from its indices, and replays the installed
equation. Data fields are read from the literal index slots. Proof fields are
extracted from the major by the native recursor itself at the motive universe
`Prop`, with the earlier data fields cast along type equations
(`PropElim.occ`, `SingletonExtraction.lean`). These extraction terms are well
typed whenever the indices are aligned with a constructor instance, without an
eliminator registration; the earlier selectors of `prefixProgram` were not. -/

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr VEnv
variable {env : VEnv} {data : NativeRecursorData} {levels levels' packed : List VLevel}
  {all : List VExpr} {c : VExpr} {fs : List VExpr}

/-- The reconstructed constructor and fields at the opened arguments
(parameters, motives, minors, indices, then the major as `bvar 0`). -/
noncomputable def singletonRecon (env : VEnv) (data : NativeRecursorData) (levels : List VLevel)
    (allArguments : List VExpr) : Option (VExpr × List VExpr) := do
  let S ← data.castSpec env levels
  let E ← data.propElim levels
  let ps := allArguments.take data.numParams
  let idx := (allArguments.drop data.indexOffset).take data.numIndices
  let fields := (PropElim.occ S (data.propParams levels) E ps idx (.bvar 0) S.fields.length).2
  return (VExpr.mkApps E.ctor (ps ++ fields), fields)

theorem singletonRecon_isSome (env : VEnv) (data : NativeRecursorData) (levels : List VLevel)
    (all all' : List VExpr) :
    (data.singletonRecon env levels all).isSome = (data.singletonRecon env levels all').isSome := by
  unfold singletonRecon
  cases data.castSpec env levels <;> cases data.propElim levels <;> rfl

theorem singletonRecon_fields_length (H : data.singletonRecon env levels all = some (c, fs)) :
    ∃ S, data.castSpec env levels = some S ∧ fs.length = S.fields.length := by
  unfold singletonRecon at H
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨S, hS, E, hE, -, rfl⟩ := H
  exact ⟨S, hS, (PropElim.occ_length S _ E _ _ _ _).2⟩

theorem lift'_eq_subst (e : VExpr) (ρ : Lift) : e.lift' ρ = e.subst (.lift_r .id ρ) := by
  rw [← VExpr.lift'_subst, VExpr.subst_id]

theorem propElim_ctor (hE : data.propElim levels = some E) : ∃ c ls, E.ctor = .const c ls := by
  unfold propElim at hE
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at hE
  obtain ⟨k, hk, i, hi, rfl⟩ := hE
  exact ⟨_, _, rfl⟩

theorem castSpec_lengths (hS : data.castSpec env levels = some S) :
    S.indices.length = data.numIndices ∧ (data.propParams levels).length = data.numParams := by
  unfold castSpec castSpecGeneric at hS
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.map_eq_some_iff,
    Option.some.injEq] at hS
  obtain ⟨_, ⟨i, hi, rfl⟩, rfl⟩ := hS
  simp [CastSpec.instL, Instance.singletonCast, Instance.sIndices, propParams, Instance.params,
    numIndices, numParams]

/-- The reconstruction commutes with substitutions of the opened arguments
that fix the major. -/
theorem singletonRecon_subst {σ : VExpr.Subst} (henv : env.WF) (hr : NativeRecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero)
    (hall : all.length = data.majorOffset + 1) (hσ : σ 0 = .bvar 0)
    (H : data.singletonRecon env levels all = some (c, fs)) :
    data.singletonRecon env levels (all.map (·.subst σ)) =
      some (c.subst σ, fs.map (·.subst σ)) := by
  unfold singletonRecon at H ⊢
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨S, hS, E, hE, rfl, rfl⟩ := H
  have hC := propElim_closed henv hr hlarge hzero hS hE
  obtain ⟨hidxl, hpl⟩ := castSpec_lengths hS
  have hps : (all.take data.numParams).length = (data.propParams levels).length := by
    rw [hpl]; simp [majorOffset, indexOffset] at hall ⊢; omega
  have hidx : ((all.drop data.indexOffset).take data.numIndices).length = S.indices.length := by
    rw [hidxl]; simp [majorOffset] at hall ⊢; omega
  have hsub := PropElim.occ_subst' (m := .bvar 0) hC (hps ▸ hC.scope) hidx σ S.fields.length (Nat.le_refl _)
  simp only [hS, hE]
  obtain ⟨cn, cls, hct⟩ := propElim_ctor hE
  simp only [VExpr.subst_bvar, hσ, ← List.map_take, ← List.map_drop] at hsub
  simp only [← List.map_take, ← List.map_drop, bind, Option.bind_some, pure]
  rw [← hsub.2]
  simp only [VExpr.subst_mkApps, hct, VExpr.subst_const, List.map_append]

theorem singletonRecon_inst {a : VExpr} {K : Nat} (henv : env.WF) (hr : NativeRecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero)
    (hall : all.length = data.majorOffset + 1) (hK : 0 < K)
    (H : data.singletonRecon env levels all = some (c, fs)) :
    data.singletonRecon env levels (all.map (·.inst a K)) =
      some (c.inst a K, fs.map (·.inst a K)) := by
  have h := singletonRecon_subst (σ := .liftN (.one a) K) henv hr hlarge hzero hall
    (by cases K with | zero => omega | succ K => rfl) H
  simpa only [← VExpr.instN_eq] using h

theorem singletonRecon_lift' {ρ : Lift} {n : Nat} (henv : env.WF)
    (hr : NativeRecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero)
    (hall : all.length = data.majorOffset + 1) (hn : 0 < n)
    (H : data.singletonRecon env levels all = some (c, fs)) :
    data.singletonRecon env levels (all.map (·.lift' (ρ.consN n))) =
      some (c.lift' (ρ.consN n), fs.map (·.lift' (ρ.consN n))) := by
  have h := singletonRecon_subst (σ := .lift_r .id (ρ.consN n)) henv hr hlarge hzero hall
    (by cases n with | zero => omega | succ n => rfl) H
  simpa only [← lift'_eq_subst] using h

theorem singletonRecon_levels
    (hl : ∀ level ∈ levels, level.WF U) (hl' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (VEnv.EqUpToLevels U) all all')
    (H : data.singletonRecon env levels all = some (c, fs)) :
    ∃ c' fs', data.singletonRecon env levels' all' = some (c', fs') ∧
      VEnv.EqUpToLevels U c c' ∧ List.Forall₂ (VEnv.EqUpToLevels U) fs fs' := by
  unfold singletonRecon at H ⊢
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨S, hS, E, hE, rfl, rfl⟩ := H
  obtain ⟨S', E', hS', hE', hlenF, hocc⟩ := occ_levels hS hE hl hl' he
  obtain ⟨E'', hE'', hrel⟩ := propElim_levels hE hl hl' he
  cases hE'.symm.trans hE''
  have hps := List.forall₂_take ha data.numParams
  have hidx := List.forall₂_take (List.forall₂_drop ha data.indexOffset) data.numIndices
  have h := (hocc hps hidx (.bvar (i := 0)) S.fields.length).2
  simp only [hS', hE', bind, Option.bind_some, hlenF]
  exact ⟨_, _, rfl, hrel.ctor.mkApps_args (List.Forall₂.append' hps h), h⟩

/-- The singleton prefix program: `prefixProgram` with the reconstruction of
`singletonRecon`. -/
noncomputable def singletonProgram (env : VEnv) (data : NativeRecursorData) (_U : Nat)
    (levels : List VLevel) (arguments : List VExpr) : Option PrefixProgram := do
  if levels.length != data.uvars || arguments.length > data.majorOffset then none else
  let type ← data.recursorType
  let type ← supplyType arguments (type.instL levels)
  let remaining := data.majorOffset + 1 - arguments.length
  let (domains, result) ← takeForalls remaining type
  let allArguments := arguments.map (·.liftN remaining) ++ vars remaining 0
  let (constructor, fields) ← data.singletonRecon env levels allArguments
  let captures := allArguments.take data.indexOffset ++ fields
  let equation ← data.singletonEquation
  let equationBody ← CaseSchema.EquationBody.extract equation.lhs equation.rhs equation.type
  if captures.length != equationBody.domains.length then none else
  return ⟨domains, result, constructor, equation, equationBody, captures, levels⟩

theorem singletonProgram_unique {data : NativeRecursorData} {levels : List VLevel}
    (h : data.singletonProgram env U levels arguments = some p)
    (h' : data.singletonProgram env U levels arguments = some p') : p = p' :=
  Option.some.inj (h.symm.trans h')

theorem singletonProgram_spec {data : NativeRecursorData} {levels : List VLevel}
    (h : data.singletonProgram env U levels arguments = some program) :
    arguments.length ≤ data.majorOffset ∧ program.domains ≠ [] ∧
    program.levels = levels ∧ program.levels.length = program.equation.uvars ∧
    data.singletonEquation = some program.equation ∧
    CaseSchema.EquationBody.extract program.equation.lhs program.equation.rhs
      program.equation.type = some program.equationBody ∧
    program.captures.length = program.equationBody.domains.length := by
  unfold singletonProgram at h
  dsimp only at h
  split at h <;> try contradiction
  rename_i hguard
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨type, _, remainingType, _, ⟨domains, result⟩, hdomains,
    ⟨constructor, fields⟩, _, equation, hequation, body, hbody, h⟩ := h
  split at h <;> try contradiction
  rename_i hcaptures
  cases h
  simp at hguard
  have hargs : arguments.length ≤ data.majorOffset := by simpa using hguard.2
  have hlevels : levels.length = data.uvars := by simpa using hguard.1
  have hlen := takeForalls_length hdomains
  refine ⟨hargs, ?_, rfl, hlevels.trans (singletonEquation_uvars hequation).symm,
    hequation, hbody, ?_⟩
  · intro hnil
    change domains = [] at hnil
    simp only [hnil, List.length_nil] at hlen
    omega
  · simpa using hcaptures

end Lean4Lean.InductiveSignature.NativeRecursorData

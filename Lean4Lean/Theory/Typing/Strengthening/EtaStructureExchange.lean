import Lean4Lean.Theory.Typing.Strengthening.EtaExpansion
import Lean4Lean.Theory.Typing.Strengthening.StructureUnfoldingSupply

/-! # Consuming an eta-created structure constructor

A closed structure unfolding computes directly on the original major. Compatible
eta expansion of the supplied recursor arguments and projected fields then
reaches the ordinary iota result. Constructor parameters are ignored by the
checked rule. This is a root exchange, not full compatible postponement.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Pattern right-hand sides preserve compatible eta expansion of captures. -/
theorem TypedEtaExpansion.apply_pat {p : Pattern} (r : p.RHS)
    {levels : List VLevel} {captures captures' : p.Path → VExpr}
    (H : ∀ a, TypedEtaExpansion Γ (captures a) (captures' a)) :
    TypedEtaExpansion Γ (r.apply levels captures) (r.apply levels captures') := by
  induction r with
  | fixed => exact .refl
  | var => exact H _
  | app _ _ ihf iha => exact .app ihf iha

/-- Selecting corresponding spine captures preserves their actual eta paths. -/
theorem TypedEtaExpansion.spineCaptures {c : Name} {n : Nat}
    (H : List.Forall₂ (TypedEtaExpansion Γ) args args')
    (hlen : args.length = n) (hlen' : args'.length = n)
    (p : ((Pattern.const c).varN n).Path) :
    TypedEtaExpansion Γ (ClosedStructure.spineCaptures args hlen p)
      (ClosedStructure.spineCaptures args' hlen' p) :=
  H.getElem_of _ (hlen ▸ (ClosedStructure.spineIndex p).isLt)
    (hlen' ▸ (ClosedStructure.spineIndex p).isLt)

/-- Projection consuming an eta-created constructor with further expansions in
its fields leaves exactly the selected field expansion. No constructor
parameters or universe levels survive in the result. -/
theorem projection_eta_exchange {info : VProjectionInfo}
    (HF : List.Forall₂ (TypedEtaExpansion Γ)
      ((List.range info.numFields).map (fun i => .proj family i major)) fields)
    (hp : params.length = info.nparams)
    (hg : (params ++ fields)[info.nparams + index]? = some field) :
    TypedEtaExpansion Γ (.proj family index major) field := by
  rw [List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left] at hg
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.1 hg
  have hi' : index < ((List.range info.numFields).map
      (fun i => VExpr.proj family i major)).length := by rw [HF.length_eq]; exact hi
  have H := HF.getElem_of index hi' hi
  simpa only [List.getElem_map, List.getElem_range, he] using H

end Lean4Lean.VEnv.Strengthening.PureObservation

namespace Lean4Lean.VEnv.Strengthening.ClosedStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
open PureObservation
variable [Params]

set_option backward.isDefEq.respectTransparency false in
/-- The iota result after eta expansion of a structure major is reached by
computing its closed projection program first, then expanding the supplied
arguments and projected fields. No source typing, canonical Eq, or front is
needed beyond the closed unfolding's existing certificates. -/
theorem iota_eta_exchange
    {r : (pattern data info).RHS × (pattern data info).Check}
    {params : List VExpr}
    {recCaptures : ((Pattern.const data.name).varN data.majorOffset).Path → VExpr}
    {ctorCaptures : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Path → VExpr}
    (hr : RecursorRegistered env data) (hw : ∀ l ∈ levels, l.WF univs)
    (hl : levels.length = data.uvars) (hi : env.projections (family data) info)
    (hn : info.nindices = 0) (hz : Admissible env univs data info levels)
    (hp : Pat _ r) (hc : CheckFromTyping env univs _ r levels)
    (ha : args.length = data.majorOffset)
    (HA : List.Forall₂ (TypedEtaExpansion Γ) args args')
    (HF : List.Forall₂ (TypedEtaExpansion Γ)
      ((List.range info.numFields).map (fun i => .proj (family data) i major)) fields)
    (hrec : ((Pattern.const data.name).varN data.majorOffset).Matches
      (mkApps (.const data.name levels) args') levels recCaptures)
    (hparams : params.length = info.nparams)
    (hctor : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Matches
      (mkApps (.const info.ctorName ctorLevels) (params ++ fields)) ctorLevels ctorCaptures) :
    ∃ out, Compute (definitions D) (.app (mkApps (.const data.name levels) args) major) out ∧
      TypedEtaExpansion Γ out (Pattern.RHS.apply (p := pattern data info)
        levels (Sum.elim recCaptures ctorCaptures) r.1) := by
  have ha' : args'.length = data.majorOffset := HA.length_eq.symm.trans ha
  have hf : fields.length = info.numFields := by simpa using HF.length_eq.symm
  have hrecEq := (Pattern.matches_determ hrec (spineCaptures_match args' ha' levels)).2
  rw [hrecEq]
  let dummyFields := List.replicate info.nparams (VExpr.sort .zero) ++ fields
  have hdlen : dummyFields.length = info.nparams + info.numFields := by simp [dummyFields, hf]
  have hdummy := spineCaptures_match (c := info.ctorName) dummyFields hdlen []
  have he := (pat_iota_params hp hi rfl hctor hdummy hparams (by simp)).1
    levels (spineCaptures args' ha')
  rw [he]
  refine ⟨_, supplied_compute hr hw hl hi hn hz hp hc ha, ?_⟩
  unfold suppliedBody
  apply TypedEtaExpansion.apply_pat
  intro p
  cases p with
  | inl p => exact TypedEtaExpansion.spineCaptures HA ha ha' p
  | inr p =>
    exact TypedEtaExpansion.spineCaptures
      ((List.Forall₂.rfl (fun _ _ => TypedEtaExpansion.refl)).append' HF) (by simp) hdlen p

/-- Actual endpoint typings of structure eta supply the closed admissibility
certificate at the recursor's canonical family instance. Compatible later
expansions of arguments and fields are retained in the final eta phase. -/
theorem typed_iota_eta_exchange
    {r : (pattern data info).RHS × (pattern data info).Check}
    {params params' : List VExpr}
    {recCaptures : ((Pattern.const data.name).varN data.majorOffset).Path → VExpr}
    {ctorCaptures : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Path → VExpr}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : RecursorRegistered env data) (hw : ∀ l ∈ levels, l.WF univs)
    (hl : levels.length = data.uvars) (hi : env.projections (family data) info)
    (hn : info.nindices = 0) (hparams : params.length = info.nparams)
    (hm : env.HasType univs Γ major
      (mkApps (.const (family data) (familyLevels data levels)) params))
    (he : env.HasType univs Γ
      (structExpand (family data) info (familyLevels data levels) params major)
      (mkApps (.const (family data) (familyLevels data levels)) params))
    (hp : Pat _ r) (hc : CheckFromTyping env univs _ r levels)
    (ha : args.length = data.majorOffset)
    (HA : List.Forall₂ (TypedEtaExpansion Γ) args args')
    (HF : List.Forall₂ (TypedEtaExpansion Γ)
      ((List.range info.numFields).map (fun i => .proj (family data) i major)) fields)
    (hrec : ((Pattern.const data.name).varN data.majorOffset).Matches
      (mkApps (.const data.name levels) args') levels recCaptures)
    (hparams' : params'.length = info.nparams)
    (hctor : ((Pattern.const info.ctorName).varN (info.nparams + info.numFields)).Matches
      (mkApps (.const info.ctorName ctorLevels) (params' ++ fields)) ctorLevels ctorCaptures) :
    ∃ out, Compute (definitions D) (.app (mkApps (.const data.name levels) args) major) out ∧
      TypedEtaExpansion Γ out (Pattern.RHS.apply (p := pattern data info)
        levels (Sum.elim recCaptures ctorCaptures) r.1) :=
  iota_eta_exchange hr hw hl hi hn
    ((StructureReplay.expansion_typed_iff henv hΓ hi hparams hn hm).1 he)
    hp hc ha HA HF hrec hparams' hctor

end Lean4Lean.VEnv.Strengthening.ClosedStructure

import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.AuxiliaryConstructors
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.ProjNames

/-! Beta reduction and the context-carrying renaming of projection rules.

The lowered constructor type of a source structure restores syntactically to the source
constructor type. The renaming replacement `replaceRen ρ σ` of the lowered constructor type beta
reduces to its restoration (`Restoration.expr_betaRed`): each inserted restoration lambda
`λ params, target levels args` meets a complete parameter spine. Field types commute with the
replacement (`VProjectionInfo.fieldType_replaceRen_renamed`), and field types computed from a beta
reduct of the constructor type are beta reducts of the field types
(`VProjectionInfo.fieldType_betaRed`), as instantiating parameters and preceding fields is
substitution. `ProjectionRulesRenamedOnCtx` receives the well-formedness of the image context in
every projection rule, so beta subject reduction (`VExpr.BetaRed.simAt`) applies and the renaming
of the projection rules of a source structure needs no hypothesis
(`ProjectionRulesRenamedOnCtx.of_ctorType_betaRed`). Auxiliary structure-like families are
handled in `Nested/Restoration/AuxiliaryProjections.lean`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VExpr

/-- Beta reduction: the reflexive-transitive compatible closure of the
contraction of a beta redex. -/
inductive BetaRed : VExpr → VExpr → Prop
  | refl : BetaRed e e
  | trans : BetaRed e₁ e₂ → BetaRed e₂ e₃ → BetaRed e₁ e₃
  | app : BetaRed f f' → BetaRed a a' → BetaRed (.app f a) (.app f' a')
  | lam : BetaRed d d' → BetaRed b b' → BetaRed (.lam d b) (.lam d' b')
  | forallE : BetaRed d d' → BetaRed b b' → BetaRed (.forallE d b) (.forallE d' b')
  | proj : BetaRed m m' → BetaRed (.proj n i m) (.proj n i m')
  | beta : BetaRed (.app (.lam A b) a) (b.inst a)

namespace BetaRed

theorem instN (H : BetaRed e e') (v : VExpr) (k : Nat) :
    BetaRed (e.inst v k) (e'.inst v k) := by
  induction H generalizing k with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans (ih1 k) (ih2 k)
  | app _ _ ih1 ih2 => exact .app (ih1 k) (ih2 k)
  | lam _ _ ih1 ih2 => exact .lam (ih1 k) (ih2 (k + 1))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 k) (ih2 (k + 1))
  | proj _ ih => exact .proj (ih k)
  | @beta A b a => rw [inst0_inst_hi]; exact .beta

theorem instL (H : BetaRed e e') (ls : List VLevel) : BetaRed (e.instL ls) (e'.instL ls) := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih
  | beta => rw [instL_instN]; exact .beta

theorem mkApps (hf : BetaRed f f') (has : List.Forall₂ BetaRed as as') :
    BetaRed (VExpr.mkApps f as) (VExpr.mkApps f' as') := by
  induction has generalizing f f' with
  | nil => exact hf
  | cons ha _ ih => exact ih (.app hf ha)

theorem forall₂_refl : ∀ (as : List VExpr), List.Forall₂ BetaRed as as
  | [] => .nil
  | _ :: as => .cons .refl (forall₂_refl as)

theorem forallE_inv (H : BetaRed (.forallE d b) y) :
    ∃ d' b', y = .forallE d' b' ∧ BetaRed d d' ∧ BetaRed b b' := by
  generalize hx : VExpr.forallE d b = x at H
  induction H generalizing d b with
  | refl => subst hx; exact ⟨_, _, rfl, .refl, .refl⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨d1, b1, rfl, h1, h2⟩ := ih1 hx
    obtain ⟨d2, b2, rfl, h3, h4⟩ := ih2 rfl
    exact ⟨_, _, rfl, h1.trans h3, h2.trans h4⟩
  | forallE h1 h2 => cases hx; exact ⟨_, _, rfl, h1, h2⟩
  | app | lam | proj | beta => cases hx

/-- Full beta reduction of a lambda telescope applied to at least as many
arguments as it has binders. -/
theorem mkApps_wrapLams :
    ∀ (doms : List VExpr) (body : VExpr) (args : List VExpr), doms.length ≤ args.length →
      BetaRed (VExpr.mkApps (VExpr.wrapLams doms body) args)
        (VExpr.mkApps (body.instOuter (args.take doms.length)) (args.drop doms.length))
  | [], body, args, _ => by simpa [VExpr.wrapLams] using BetaRed.refl
  | _ :: _, _, [], h => by simp at h
  | d :: ds, body, a :: rest, h => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    have h1 : BetaRed (VExpr.mkApps (VExpr.wrapLams (d :: ds) body) (a :: rest))
        (VExpr.mkApps ((VExpr.wrapLams ds body).inst a) rest) :=
      BetaRed.mkApps (f := .app (.lam d (VExpr.wrapLams ds body)) a) (as := rest)
        .beta (forall₂_refl rest)
    rw [VExpr.wrapLams_inst, Nat.zero_add] at h1
    have h2 := mkApps_wrapLams (VExpr.instDomains ds a 0) (body.inst a ds.length) rest
      (by simpa using h)
    simp only [VExpr.instDomains_length] at h2
    have hlen : (rest.take ds.length).length = ds.length := by simp; omega
    simpa [List.take_succ_cons, VExpr.instOuter_cons, hlen] using h1.trans h2

end BetaRed
end VExpr

namespace VEnv

end VEnv

/-- In a well-formed context, beta reduction is a definitional equality at
every type of the reduced term. -/
theorem VExpr.BetaRed.simAt {env : VEnv} {U : Nat} (henv : env.Ordered)
    (hβ : env.BetaSubjectReduction U) {x x' : VExpr} (H : VExpr.BetaRed x x') :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) → env.SimAt U Γ x x' := by
  induction H with
  | refl => intro _ _; exact VEnv.SimAt.refl
  | trans _ _ ih1 ih2 => intro _ hΓ; exact (ih1 hΓ).trans (ih2 hΓ)
  | app _ _ ih1 ih2 => intro _ hΓ; exact VEnv.SimAt.app henv hΓ (ih1 hΓ) (ih2 hΓ)
  | lam _ _ ih1 ih2 =>
    intro _ hΓ; exact VEnv.SimAt.lam henv hΓ (ih1 hΓ) fun hΓ' => ih2 hΓ'
  | forallE _ _ ih1 ih2 =>
    intro _ hΓ; exact VEnv.SimAt.forallE henv hΓ (ih1 hΓ) fun hΓ' => ih2 hΓ'
  | proj _ ih => intro _ hΓ; exact VEnv.SimAt.proj henv hΓ (ih hΓ)
  | beta => intro Γ hΓ; exact hβ Γ _ _ _ hΓ

namespace VProjectionInfo

theorem instantiateProjectionParameters_betaRed :
    ∀ (params : List VExpr) {A B X : VExpr}, VExpr.BetaRed A B →
      instantiateProjectionParameters A params = some X →
      ∃ Y, instantiateProjectionParameters B params = some Y ∧ VExpr.BetaRed X Y
  | [], A, B, X, h, hX => by
    simp only [instantiateProjectionParameters, Option.some.injEq] at hX ⊢
    subst hX
    exact ⟨_, rfl, h⟩
  | p :: ps, A, B, X, h, hX => by
    cases A with
    | forallE d b =>
      obtain ⟨d', b', rfl, -, hb⟩ := h.forallE_inv
      simp only [instantiateProjectionParameters] at hX ⊢
      exact instantiateProjectionParameters_betaRed ps (hb.instN p 0) hX
    | _ => simp [instantiateProjectionParameters] at hX

theorem instantiateProjectionFields_betaRed {typeName : Name} {major : VExpr} {wanted : Nat} :
    ∀ (fuel : Nat) {current : Nat} {A B X : VExpr}, VExpr.BetaRed A B →
      instantiateProjectionFields typeName major wanted current fuel A = some X →
      ∃ Y, instantiateProjectionFields typeName major wanted current fuel B = some Y ∧
        VExpr.BetaRed X Y
  | 0, _, _, _, _, _, hX => by simp [instantiateProjectionFields] at hX
  | fuel + 1, current, A, B, X, h, hX => by
    cases A with
    | forallE d b =>
      obtain ⟨d', b', rfl, hd, hb⟩ := h.forallE_inv
      simp only [instantiateProjectionFields] at hX ⊢
      by_cases hw : wanted = current
      · rw [if_pos hw] at hX ⊢
        cases hX
        exact ⟨_, rfl, hd⟩
      · rw [if_neg hw] at hX ⊢
        exact instantiateProjectionFields_betaRed fuel (hb.instN _ 0) hX
    | _ => simp [instantiateProjectionFields] at hX

/-- Field types computed from a beta-reduced constructor type are beta
reducts of the field types of the unreduced constructor type. -/
theorem fieldType_betaRed {info : VProjectionInfo} {ctorType' : VExpr}
    {typeName : Name} {levels : List VLevel} {params : List VExpr} {index : Nat}
    {major X : VExpr} (h : VExpr.BetaRed info.ctorType ctorType')
    (H : info.fieldType typeName levels params index major = some X) :
    ∃ Y, { info with ctorType := ctorType' }.fieldType typeName levels params index major =
      some Y ∧ VExpr.BetaRed X Y := by
  unfold fieldType at H ⊢
  split at H
  · cases H
  · next hvalid =>
    rw [if_neg hvalid]
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at H ⊢
    obtain ⟨tail, htail, hX⟩ := H
    obtain ⟨tail', htail', hrel⟩ := instantiateProjectionParameters_betaRed params (h.instL levels) htail
    obtain ⟨Y, hY, hXY⟩ := instantiateProjectionFields_betaRed _ hrel hX
    exact ⟨Y, ⟨tail', htail', hY⟩, hXY⟩

theorem instantiateProjectionFields_replaceRen_renamed {ρ : Name → Option VExpr} {σ : Name → Name}
    (hρ : VExpr.ReplacementsClosed ρ) (type : VExpr) :
    instantiateProjectionFields (σ typeName) (major.replaceRen ρ σ) wanted current fuel
        (type.replaceRen ρ σ) =
      (instantiateProjectionFields typeName major wanted current fuel type).map
        (·.replaceRen ρ σ) := by
  induction fuel generalizing type current with
  | zero => simp [instantiateProjectionFields]
  | succ fuel ih =>
    cases type <;> simp [instantiateProjectionFields, VExpr.replaceRen]
    case const c ls =>
      cases h : ρ c with
      | none => simp [instantiateProjectionFields]
      | some t =>
        exact instantiateProjectionFields_of_ne_forallE (VExpr.instL_ne_forallE (hρ c t h).2 ls)
    case forallE domain body =>
      split
      · simp
      · change instantiateProjectionFields (σ typeName) (major.replaceRen ρ σ) wanted
            (current + 1) fuel
            ((body.replaceRen ρ σ).inst
              (.proj (σ typeName) current (major.replaceRen ρ σ))) = _
        have : VExpr.proj (σ typeName) current (major.replaceRen ρ σ) =
            (VExpr.proj typeName current major).replaceRen ρ σ := by
          simp [VExpr.replaceRen]
        rw [this, ← VExpr.replaceRen_inst hρ]
        exact ih (current := current + 1) (body.inst (.proj typeName current major))

/-- Field types commute with a renaming replacement of the constructor type,
the parameters, the major premise and the projection type name. -/
theorem fieldType_replaceRen_renamed {ρ : Name → Option VExpr} {σ : Name → Name}
    {typeName : Name} {levels : List VLevel} {params : List VExpr} {index : Nat}
    {major : VExpr} (hρ : VExpr.ReplacementsClosed ρ) (info : VProjectionInfo) :
    { info with ctorType := info.ctorType.replaceRen ρ σ }.fieldType (σ typeName) levels
        (params.map (VExpr.replaceRen ρ σ)) index (major.replaceRen ρ σ) =
      (info.fieldType typeName levels params index major).map (VExpr.replaceRen ρ σ) := by
  simp only [fieldType, List.length_map]
  split
  · rfl
  · rw [← VExpr.replaceRen_instL, instantiateProjectionParameters_replaceRen hρ]
    cases instantiateProjectionParameters (info.ctorType.instL levels) params <;>
      simp [instantiateProjectionFields_replaceRen_renamed hρ]

end VProjectionInfo

namespace InductiveSignature

/-- Restoration is a beta reduct of the renaming replacement, for terms whose
projection names are fixed (the syntactic form of
`RenamingRestorationSubstitution.go_simAt`). -/
theorem Restoration.go_betaRed {r : Restoration} {ρ : Name → Option VExpr}
    {σ : Name → Name}
    (shape : ∀ c t, ρ c = some t → ∃ h doms,
      r.heads.find? (fun h => h.auxiliary == c) = some h ∧ doms.length = h.nparams ∧
      t = VExpr.wrapLams doms (VExpr.mkApps (.const h.target h.levels) h.arguments))
    (headsReplaced : ∀ c h, r.heads.find? (fun h => h.auxiliary == c) = some h → ρ c ≠ none)
    (renamed : ∀ c, r.heads.find? (fun h => h.auxiliary == c) = none →
      σ c = r.recursorName c) :
    ∀ (e : VExpr) {as as' : List VExpr} {out : VExpr},
      e.ProjNamesFixed σ → List.Forall₂ VExpr.BetaRed as as' →
      Restoration.expr.go r e as' = some out →
      VExpr.BetaRed (VExpr.mkApps (e.replaceRen ρ σ) as) out := by
  intro e
  induction e with
  | bvar i =>
    intro as as' out _ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact VExpr.BetaRed.mkApps .refl has
  | sort u =>
    intro as as' out _ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact VExpr.BetaRed.mkApps .refl has
  | elim block owner ls =>
    intro as as' out _ has h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    exact VExpr.BetaRed.mkApps .refl has
  | app fn arg ihfn iharg =>
    intro as as' out hfix has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨arg', harg, hfn⟩ := h
    have h1 := iharg (as := []) (as' := []) hfix.2 .nil harg
    exact ihfn (as := arg.replaceRen ρ σ :: as) hfix.1 (.cons h1 has) hfn
  | lam d b ihd ihb =>
    intro as as' out hfix has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact VExpr.BetaRed.mkApps (.lam (ihd (as := []) hfix.1 .nil hd)
      (ihb (as := []) hfix.2 .nil hb)) has
  | forallE d b ihd ihb =>
    intro as as' out hfix has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨d', hd, b', hb, rfl⟩ := h
    exact VExpr.BetaRed.mkApps (.forallE (ihd (as := []) hfix.1 .nil hd)
      (ihb (as := []) hfix.2 .nil hb)) has
  | proj n i m ih =>
    intro as as' out hfix has h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨m', hm, rfl⟩ := h
    simp only [VExpr.replaceRen, hfix.1]
    exact VExpr.BetaRed.mkApps (.proj (ih (as := []) hfix.2 .nil hm)) has
  | const c ls =>
    intro as as' out _ has h
    simp only [Restoration.expr.go] at h
    split at h
    · next hd hfind =>
      cases hρ : ρ c with
      | none => exact absurd hρ (headsReplaced c hd hfind)
      | some t =>
        rw [VExpr.replaceRen_const_some hρ]
        obtain ⟨hd', doms, hfind', hdoms, rfl⟩ := shape c t hρ
        rw [hfind] at hfind'
        cases hfind'
        have hsim := VExpr.BetaRed.mkApps (f := (VExpr.wrapLams doms
          (VExpr.mkApps (.const hd.target hd.levels) hd.arguments)).instL ls) .refl has
        refine hsim.trans ?_
        unfold HeadSpecialization.apply at h
        split at h
        · cases h
        · next hlen =>
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
            Nat.not_lt] at hlen
          simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          rw [VExpr.instL_wrapLams]
          have := VExpr.BetaRed.mkApps_wrapLams (doms.map (VExpr.instL ls))
            ((VExpr.mkApps (.const hd.target hd.levels) hd.arguments).instL ls) as'
            (by simp [hdoms]; omega)
          simp only [List.length_map, hdoms] at this
          refine this.trans ?_
          simp only [VExpr.instL_mkApps, VExpr.instL, VExpr.instOuter_mkApps,
            VExpr.instOuter_const, ← VExpr.mkApps_append, List.map_map,
            Function.comp_def, Lean4Lean.VEnv.instantiateParams_eq_instOuter]
          exact .refl
    · next hfind =>
      have hρ : ρ c = none := by
        cases hρ : ρ c with
        | none => rfl
        | some t =>
          obtain ⟨_, _, hfind', _⟩ := shape c t hρ
          rw [hfind] at hfind'
          cases hfind'
      simp only [Option.some.injEq] at h
      subst h
      rw [VExpr.replaceRen_const_none hρ, renamed c hfind]
      exact VExpr.BetaRed.mkApps .refl has

theorem Restoration.expr_betaRed {r : Restoration} {ρ : Name → Option VExpr}
    {σ : Name → Name}
    (shape : ∀ c t, ρ c = some t → ∃ h doms,
      r.heads.find? (fun h => h.auxiliary == c) = some h ∧ doms.length = h.nparams ∧
      t = VExpr.wrapLams doms (VExpr.mkApps (.const h.target h.levels) h.arguments))
    (headsReplaced : ∀ c h, r.heads.find? (fun h => h.auxiliary == c) = some h → ρ c ≠ none)
    (renamed : ∀ c, r.heads.find? (fun h => h.auxiliary == c) = none →
      σ c = r.recursorName c)
    {e e' : VExpr} (hfix : e.ProjNamesFixed σ) (h : r.expr e = some e') :
    VExpr.BetaRed (e.replaceRen ρ σ) e' :=
  Restoration.go_betaRed shape headsReplaced renamed e (as := []) hfix .nil h

end InductiveSignature

/-! ### Context-carrying renaming of projection rules -/

namespace VEnv

/-- A projection whose type and constructor names are fixed by the
replacement, registered in `envS` with a constructor type that is a beta
reduct of the renamed constructor type (of the same syntactic arity),
has its projection rules renamed in well-formed contexts, by beta subject
reduction of `envS`. -/
theorem ProjectionRulesRenamedOnCtx.of_ctorType_betaRed {envS : VEnv}
    {ρ : Name → Option VExpr} {σ : Name → Name} {typeName : Name}
    {info : VProjectionInfo} {ctorType' : VExpr}
    (henv : envS.Ordered) (hβ : ∀ U, envS.BetaSubjectReduction U)
    (hρ : VExpr.ReplacementsClosed ρ)
    (hS : envS.projections typeName { info with ctorType := ctorType' })
    (htn : ρ typeName = none) (hσtn : σ typeName = typeName)
    (hctorName : ρ info.ctorName = none) (hσctor : σ info.ctorName = info.ctorName)
    (hclosed : ctorType'.Closed) (harity : ctorType'.forallArity = info.ctorType.forallArity)
    (hBR : VExpr.BetaRed (info.ctorType.replaceRen ρ σ) ctorType') :
    ProjectionRulesRenamedOnCtx envS ρ σ typeName info where
  projDF := by
    intro U Γ levels params index sourceMajor fieldType fieldLevel major indexArgs major'
      hΓ hlevels huvars hparams hindices hfield _ hguard ihField ihLeft ihRight
    have h1 := VProjectionInfo.fieldType_replaceRen_renamed (typeName := typeName) (levels := levels)
      (params := params) (index := index) (major := sourceMajor) (σ := σ) hρ info
    rw [hfield, hσtn] at h1
    obtain ⟨fieldType', hfield', hXY⟩ :=
      VProjectionInfo.fieldType_betaRed (ctorType' := ctorType') hBR h1
    have hfield'' : ({ info with ctorType := ctorType' } : VProjectionInfo).fieldType typeName
        levels (params.map (VExpr.replaceRen ρ σ)) index (sourceMajor.replaceRen ρ σ) =
        some fieldType' := hfield'
    have hdefF := (hXY.simAt henv (hβ U) hΓ _ ihField).symm
    simp only [VExpr.replaceRen_mkApps, List.map_append,
      VExpr.replaceRen_const_none htn, hσtn] at ihLeft ihRight
    simp only [VExpr.replaceRen, hσtn]
    exact .defeqDF hdefF (.projDF hS hlevels huvars (by simpa using hparams)
      (by simpa using hindices) hfield'' hdefF.hasType.1 ihLeft ihRight hclosed hguard)
  projIota := by
    intro U Γ index levels args field fieldType _ ih1 h3 ih2
    simp only [VExpr.replaceRen, VExpr.replaceRen_mkApps, hctorName,
      hσctor, hσtn] at ih1 ⊢
    exact .projIota (info := { info with ctorType := ctorType' }) hS ih1 (by simp [h3]) ih2
  structEta := by
    intro U Γ levels params e _ h2 h3 ih1 ih2
    have hnf : ({ info with ctorType := ctorType' } : VProjectionInfo).numFields =
        info.numFields := by
      simp only [VProjectionInfo.numFields, harity]
    simp only [VExpr.replaceRen, VExpr.replaceRen_mkApps, List.map_append,
      List.map_map, Function.comp_def, hctorName, htn, hσctor, hσtn] at ih1 ih2 ⊢
    rw [← hnf] at ih2 ⊢
    exact .structEta hS (by simpa using h2) h3 ih1 ih2
  unitLike := by
    intro U Γ levels params e e' _ h2 h3 h4 ih1 ih2
    have hnf : ({ info with ctorType := ctorType' } : VProjectionInfo).numFields =
        info.numFields := by
      simp only [VProjectionInfo.numFields, harity]
    simp only [VExpr.replaceRen_mkApps, VExpr.replaceRen_const_none htn, hσtn] at ih1 ih2 ⊢
    exact .unitLike hS (by simpa using h2) h3 (hnf.trans h4) ih1 ih2

end VEnv

end Lean4Lean

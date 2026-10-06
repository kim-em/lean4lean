import Lean4Lean.Verify.Inductive.Nested.RestoredEquationContainers
import Lean4Lean.Verify.Inductive.Nested.RestoredEquationProjNames

/-! The hypothesis `NestedProjectionTransportGap`
(`Nested/RestoredEquationContainers.lean`) of the restored-equation route.

**Primary field types (`primaryFields`).** The lowered constructor type of an
original structure restores syntactically to the source constructor type. The
renaming replacement `replaceRen ρ σ` of the lowered constructor type beta
reduces to its restoration (`Restoration.expr_betaRed`, the syntactic form of
`RenamingRestorationSubstitution.go_simAt`): each inserted restoration lambda
`λ params, target levels args` meets a complete parameter spine. Field types
commute with the replacement (`VProjectionInfo.fieldType_replaceRen'`), and
field types computed from a beta reduct of the constructor type are beta
reducts of the field types (`VProjectionInfo.fieldType_betaRed`), as
instantiating parameters and preceding fields is substitution. So the source
field type is a beta reduct of the transported lowered field type. The
projection rule `projDF` carries no well-formedness of its context, so the
final step, beta conversion of a typed term, is taken in an arbitrary context:
`VEnv.BetaConversionAnyContext`. In well-formed contexts this is beta subject
reduction (`VExpr.BetaRed.simAt`); the arbitrary-context form is a named
hypothesis here.

**Auxiliary projections (`auxiliary`).** For a projection of an auxiliary
structure-like family `A`, renamed to its container `J`, the transported major
premise of `projDF` has the type `(λ params, J levels args) params' indices'`,
a beta redex, while `projDF` of the final environment needs the major at the
syntactic application `J levels' (args[params'] ++ indices')`. In an
ill-formed lowered context this transport fails: take a block with a
parameter `α` and an auxiliary family `A α := Prod Nat (Foo α)`, and the
lowered context `[A (bvar 5)]` (unchecked, with an out-of-scope parameter).
The lowered environment derives `proj A 0 (bvar 0) : Nat` (`projDF`: the
major is typed by `bvar`, the field type `Nat` does not mention the
parameter). Its image `proj J 0 (bvar 0)` in the context
`[(λ α, Prod Nat (Foo α)) (bvar 5)]` has no typing in the final environment:
the only rule typing a projection whose major is a variable is `projDF`, which
needs the variable at a syntactic `Prod` application, reachable from the
context entry only through a definitional equality whose left side (the
context entry, mentioning an out-of-scope variable) has no typing. So the
`auxiliary` field is not a consequence of the run in the presence of block
parameters and auxiliary structure-like families; it is kept as the named
hypothesis `NestedAuxiliaryProjectionTransport`. The context-carrying
transport `RenamingReplacementOnCtx.isDefEq` (below) receives the
well-formedness of the image context in every projection rule
(`ProjectionTransportOnCtx`); there beta subject reduction applies, and the
primary transport needs no hypothesis at all
(`ProjectionTransportOnCtx.of_ctorType_betaRed`).
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

/-- Beta reduction preserves typing and is a definitional equality in *every*
context, well-formed or not. In well-formed contexts this follows from beta
subject reduction (`VExpr.BetaRed.simAt`); the projection rule `projDF`
carries no well-formedness of its context, so its transport along a
replacement that inserts beta redexes needs the context-free form. -/
def BetaConversionAnyContext (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {x x' T : VExpr}, VExpr.BetaRed x x' →
    env.HasType U Γ x T → env.IsDefEq U Γ x x' T

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
reducts of the original field types. -/
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

theorem instantiateProjectionFields_replaceRen' {ρ : Name → Option VExpr} {σ : Name → Name}
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
theorem fieldType_replaceRen' {ρ : Name → Option VExpr} {σ : Name → Name}
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
      simp [instantiateProjectionFields_replaceRen' hρ]

end VProjectionInfo

namespace InductiveSignature

private theorem instantiateParams_eq_instOuter_betaRed (body : VExpr) (args : List VExpr) :
    instantiateParams body args = body.instOuter args := by
  rw [VExpr.instOuter_eq_subst]
  rfl

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
            Function.comp_def, instantiateParams_eq_instOuter_betaRed]
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

/-! ### Context-carrying transport -/

namespace VEnv

/-- The four projection rules of `envL` at the projection `(typeName, info)`,
transported along `replaceRen ρ σ` to `envS`, in well-formed image contexts
(`ProjectionTransport` without the well-formedness of the context). -/
structure ProjectionTransportOnCtx (envS : VEnv) (ρ : Name → Option VExpr) (σ : Name → Name)
    (typeName : Name) (info : VProjectionInfo) : Prop where
  projDF : ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel} {params : List VExpr}
      {index : Nat} {sourceMajor fieldType : VExpr} {fieldLevel : VLevel}
      {major : VExpr} {indexArgs : List VExpr} {major' : VExpr},
    OnCtx Γ (envS.IsType U) →
    (∀ l ∈ levels, l.WF U) → levels.length = info.uvars →
    params.length = info.nparams → indexArgs.length = info.nindices →
    info.fieldType typeName levels params index sourceMajor = some fieldType →
    info.ctorType.Closed →
    ((info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) →
    envS.HasType U Γ (fieldType.replaceRen ρ σ) (.sort fieldLevel) →
    envS.IsDefEq U Γ (sourceMajor.replaceRen ρ σ) (major.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) (params ++ indexArgs)).replaceRen ρ σ) →
    envS.IsDefEq U Γ (sourceMajor.replaceRen ρ σ) (major'.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) (params ++ indexArgs)).replaceRen ρ σ) →
    envS.IsDefEq U Γ ((VExpr.proj typeName index major).replaceRen ρ σ)
      ((VExpr.proj typeName index major').replaceRen ρ σ) (fieldType.replaceRen ρ σ)
  projIota : ∀ {U : Nat} {Γ : List VExpr} {index : Nat} {levels : List VLevel}
      {args : List VExpr} {field fieldType : VExpr},
    OnCtx Γ (envS.IsType U) →
    envS.HasType U Γ
      ((VExpr.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args)).replaceRen
        ρ σ) (fieldType.replaceRen ρ σ) →
    args[info.nparams + index]? = some field →
    envS.HasType U Γ (field.replaceRen ρ σ) (fieldType.replaceRen ρ σ) →
    envS.IsDefEq U Γ
      ((VExpr.proj typeName index (VExpr.mkApps (.const info.ctorName levels) args)).replaceRen
        ρ σ) (field.replaceRen ρ σ) (fieldType.replaceRen ρ σ)
  structEta : ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel} {params : List VExpr}
      {e : VExpr},
    OnCtx Γ (envS.IsType U) →
    params.length = info.nparams → info.nindices = 0 →
    envS.HasType U Γ (e.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ) →
    envS.HasType U Γ
      ((VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index =>
          .proj typeName index e)).replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ) →
    envS.IsDefEq U Γ
      ((VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index =>
          .proj typeName index e)).replaceRen ρ σ)
      (e.replaceRen ρ σ) ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ)
  unitLike : ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel} {params : List VExpr}
      {e e' : VExpr},
    OnCtx Γ (envS.IsType U) →
    params.length = info.nparams → info.nindices = 0 → info.numFields = 0 →
    envS.HasType U Γ (e.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ) →
    envS.HasType U Γ (e'.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ) →
    envS.IsDefEq U Γ (e.replaceRen ρ σ) (e'.replaceRen ρ σ)
      ((VExpr.mkApps (.const typeName levels) params).replaceRen ρ σ)

theorem ProjectionTransport.onCtx {envS : VEnv} {ρ : Name → Option VExpr} {σ : Name → Name}
    {typeName : Name} {info : VProjectionInfo}
    (H : ProjectionTransport envS ρ σ typeName info) :
    ProjectionTransportOnCtx envS ρ σ typeName info where
  projDF _ := H.projDF
  projIota _ := H.projIota
  structEta _ := H.structEta
  unitLike _ := H.unitLike

/-- `RenamingReplacement` with projection rules transported only in
well-formed image contexts, for a lowered environment with well-formed
constant types (so that well-formedness of contexts propagates through the
binders of a derivation). -/
structure RenamingReplacementOnCtx (envS envL : VEnv) (ρ : Name → Option VExpr)
    (σ : Name → Name) : Prop where
  closed : VExpr.ReplacementsClosed ρ
  ordered : envS.Ordered
  orderedL : envL.Ordered
  replaced : ∀ c ci t, envL.constants c = some ci → ρ c = some t →
    envS.HasType ci.uvars [] t (ci.type.replaceRen ρ σ)
  kept : ∀ c ci, envL.constants c = some ci → ρ c = none →
    ∃ ci', envS.constants (σ c) = some ci' ∧ ci'.uvars = ci.uvars ∧
      ∃ u, envS.IsDefEq ci.uvars [] ci'.type (ci.type.replaceRen ρ σ) (.sort u)
  defeqs : ∀ df, envL.defeqs df → ∃ df', envS.defeqs df' ∧ df'.uvars = df.uvars ∧
    df'.lhs = df.lhs.replaceRen ρ σ ∧ df'.rhs = df.rhs.replaceRen ρ σ ∧
    df'.type = df.type.replaceRen ρ σ
  eliminators : ∀ block schema, envL.eliminators block schema →
    envS.eliminators block schema ∧
    (∀ owner type, schema.genericType owner = some type → type.replaceRen ρ σ = type) ∧
    (∀ owner rules, schema.genericEquations block owner = some rules → ∀ df ∈ rules,
      df.lhs.replaceRen ρ σ = df.lhs ∧ df.rhs.replaceRen ρ σ = df.rhs ∧
      df.type.replaceRen ρ σ = df.type)
  projections : ∀ typeName info, envL.projections typeName info →
    ProjectionTransportOnCtx envS ρ σ typeName info

theorem RenamingReplacement.toOnCtx {envS envL : VEnv} {ρ : Name → Option VExpr}
    {σ : Name → Name} (S : RenamingReplacement envS envL ρ σ) (hL : envL.Ordered) :
    RenamingReplacementOnCtx envS envL ρ σ where
  closed := S.closed
  ordered := S.ordered
  orderedL := hL
  replaced := S.replaced
  kept := S.kept
  defeqs := S.defeqs
  eliminators := S.eliminators
  projections typeName info h := (S.projections typeName info h).onCtx

/-- Renaming replacement transports definitional equality from well-formed
contexts to well-formed image contexts. -/
theorem RenamingReplacementOnCtx.isDefEq {envS envL : VEnv} {ρ : Name → Option VExpr}
    {σ : Name → Name} (S : RenamingReplacementOnCtx envS envL ρ σ)
    {U : Nat} {Γ : List VExpr} {e₁ e₂ A : VExpr}
    (H : envL.IsDefEq U Γ e₁ e₂ A) :
    OnCtx Γ (envL.IsType U) → OnCtx (Γ.map (·.replaceRen ρ σ)) (envS.IsType U) →
    envS.IsDefEq U (Γ.map (·.replaceRen ρ σ)) (e₁.replaceRen ρ σ) (e₂.replaceRen ρ σ)
      (A.replaceRen ρ σ) := by
  have hρ := S.closed
  induction H with
  | bvar h => intro _ _; exact .bvar (h.replaceRen hρ)
  | symm _ ih => intro hΓ hΓ'; exact .symm (ih hΓ hΓ')
  | trans _ _ ih1 ih2 => intro hΓ hΓ'; exact .trans (ih1 hΓ hΓ') (ih2 hΓ hΓ')
  | sortDF h1 h2 h3 => intro _ _; exact .sortDF h1 h2 h3
  | @constDF c ci ls ls' Γ₀ h1 h2 h3 h4 h5 =>
    intro _ _
    rw [VExpr.replaceRen_instL]
    cases hc : ρ c with
    | some t =>
      rw [VExpr.replaceRen_const_some hc, VExpr.replaceRen_const_some hc]
      have ht := S.replaced c ci t h1 hc
      have := IsDefEq.instL_r S.ordered (Γ := []) trivial h2 h3 h5 ht
      exact this.weak0 S.ordered
    | none =>
      rw [VExpr.replaceRen_const_none hc, VExpr.replaceRen_const_none hc]
      obtain ⟨ci', hci', hu, _, ht⟩ := S.kept c ci h1 hc
      have hconst : envS.IsDefEq U (Γ₀.map (·.replaceRen ρ σ)) (.const (σ c) ls)
          (.const (σ c) ls') (ci'.type.instL ls) :=
        IsDefEq.constDF hci' h2 h3 (h4.trans hu.symm) h5
      have ht' := (ht.instL h2 (Γ := [])).weak0 S.ordered (Γ := Γ₀.map (·.replaceRen ρ σ))
      exact .defeqDF ht' hconst
  | elimDF hlookup htype hclosed hperm hright heq _ ih =>
    intro hΓ hΓ'
    obtain ⟨hS, htypes, _⟩ := S.eliminators _ _ hlookup
    have hfix := htypes _ _ htype
    have ih := ih hΓ hΓ'
    simp only [VExpr.replaceRen_instL, hfix, VExpr.replaceRen] at ih ⊢
    exact .elimDF hS htype hclosed hperm hright heq ih
  | elimIota hlookup hgen hmem hclosed hperm _ _ ihLeft ihRight =>
    intro hΓ hΓ'
    obtain ⟨hS, _, hrules⟩ := S.eliminators _ _ hlookup
    obtain ⟨hl, hr, ht⟩ := hrules _ _ hgen _ hmem
    have ihLeft := ihLeft hΓ hΓ'
    have ihRight := ihRight hΓ hΓ'
    simp only [VExpr.replaceRen_instL, hl, hr, ht] at ihLeft ihRight ⊢
    exact .elimIota hS hgen hmem hclosed hperm ihLeft ihRight
  | appDF _ _ ih1 ih2 =>
    intro hΓ hΓ'
    rw [VExpr.replaceRen_inst hρ]
    exact .appDF (ih1 hΓ hΓ') (ih2 hΓ hΓ')
  | projDF hinfo hlevels huvars hparams hindices hfield _ _ _ hclosed hguard
      ihField ihLeft ihRight =>
    intro hΓ hΓ'
    exact (S.projections _ _ hinfo).projDF hΓ' hlevels huvars hparams hindices hfield hclosed
      hguard (ihField hΓ hΓ') (ihLeft hΓ hΓ') (ihRight hΓ hΓ')
  | projIota h1 _ h3 _ ih1 ih2 =>
    intro hΓ hΓ'
    exact (S.projections _ _ h1).projIota hΓ' (ih1 hΓ hΓ') h3 (ih2 hΓ hΓ')
  | structEta h1 h2 h3 _ _ ih1 ih2 =>
    intro hΓ hΓ'
    exact (S.projections _ _ h1).structEta hΓ' h2 h3 (ih1 hΓ hΓ') (ih2 hΓ hΓ')
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 =>
    intro hΓ hΓ'
    exact (S.projections _ _ h1).unitLike hΓ' h2 h3 h4 (ih1 hΓ hΓ') (ih2 hΓ hΓ')
  | lamDF h1 _ ih1 ih2 =>
    intro hΓ hΓ'
    have ih1 := ih1 hΓ hΓ'
    exact .lamDF ih1 (ih2 ⟨hΓ, _, h1.hasType.1⟩ ⟨hΓ', _, ih1.hasType.1⟩)
  | forallEDF h1 _ ih1 ih2 =>
    intro hΓ hΓ'
    have ih1 := ih1 hΓ hΓ'
    exact .forallEDF ih1 (ih2 ⟨hΓ, _, h1.hasType.1⟩ ⟨hΓ', _, ih1.hasType.1⟩)
  | defeqDF _ _ ih1 ih2 => intro hΓ hΓ'; exact .defeqDF (ih1 hΓ hΓ') (ih2 hΓ hΓ')
  | beta _ h2 ih1 ih2 =>
    intro hΓ hΓ'
    have ih2 := ih2 hΓ hΓ'
    have ih1 := ih1 ⟨hΓ, h2.isType S.orderedL hΓ⟩ ⟨hΓ', ih2.isType S.ordered hΓ'⟩
    simp only [VExpr.replaceRen, VExpr.replaceRen_inst hρ]
    exact .beta ih1 ih2
  | eta _ ih =>
    intro hΓ hΓ'
    simp only [VExpr.replaceRen, VExpr.replaceRen_lift hρ]
    exact .eta (ih hΓ hΓ')
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    intro hΓ hΓ'; exact .proofIrrel (ih1 hΓ hΓ') (ih2 hΓ hΓ') (ih3 hΓ hΓ')
  | extra h1 h2 h3 =>
    intro _ _
    obtain ⟨df', hS, hu, hl, hr, ht⟩ := S.defeqs _ h1
    simp only [VExpr.replaceRen_instL, ← hl, ← hr, ← ht]
    exact .extra hS h2 (h3.trans hu.symm)

theorem RenamingReplacementOnCtx.onCtx {envS envL : VEnv} {ρ : Name → Option VExpr}
    {σ : Name → Name} (S : RenamingReplacementOnCtx envS envL ρ σ) {U : Nat} :
    ∀ {Γ : List VExpr}, OnCtx Γ (envL.IsType U) →
      OnCtx (Γ.map (·.replaceRen ρ σ)) (envS.IsType U)
  | [], _ => trivial
  | _ :: _, ⟨hΓ, _, hA⟩ => ⟨S.onCtx hΓ, _, S.isDefEq hA hΓ (S.onCtx hΓ)⟩

/-- A projection whose type and constructor names are fixed by the
replacement, registered in `envS` with a constructor type that is a beta
reduct of the transported constructor type (of the same syntactic arity),
transports in well-formed contexts, by beta subject reduction of `envS`. -/
theorem ProjectionTransportOnCtx.of_ctorType_betaRed {envS : VEnv}
    {ρ : Name → Option VExpr} {σ : Name → Name} {typeName : Name}
    {info : VProjectionInfo} {ctorType' : VExpr}
    (henv : envS.Ordered) (hβ : ∀ U, envS.BetaSubjectReduction U)
    (hρ : VExpr.ReplacementsClosed ρ)
    (hS : envS.projections typeName { info with ctorType := ctorType' })
    (htn : ρ typeName = none) (hσtn : σ typeName = typeName)
    (hctorName : ρ info.ctorName = none) (hσctor : σ info.ctorName = info.ctorName)
    (hclosed : ctorType'.Closed) (harity : ctorType'.forallArity = info.ctorType.forallArity)
    (hBR : VExpr.BetaRed (info.ctorType.replaceRen ρ σ) ctorType') :
    ProjectionTransportOnCtx envS ρ σ typeName info where
  projDF := by
    intro U Γ levels params index sourceMajor fieldType fieldLevel major indexArgs major'
      hΓ hlevels huvars hparams hindices hfield _ hguard ihField ihLeft ihRight
    have h1 := VProjectionInfo.fieldType_replaceRen' (typeName := typeName) (levels := levels)
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

namespace VerifyInductive

/-! ### Primary field types -/

theorem RestorationTableData.projNamesAvoid_eq {decl : VInductDecl}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us₀ : List Name} {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀) (e : VExpr) :
    e.projNamesAvoid (compilationRestoration decl aux₀).restorableNames =
      e.projNamesAvoid (compilationRestoration decl aux₁).restorableNames := by
  induction e with
  | bvar | sort | elim | const => rfl
  | app f a ihf iha | lam f a ihf iha | forallE f a ihf iha =>
    simp only [VExpr.projNamesAvoid, ihf, iha]
  | proj n i e ih =>
    have hn : (compilationRestoration decl aux₀).restorableNames.contains n =
        (compilationRestoration decl aux₁).restorableNames.contains n := by
      rw [Bool.eq_iff_iff]
      simpa using D₀.restorable_iff D₁ n
    simp only [VExpr.projNamesAvoid, ih, hn]

/-- **The `primaryFields` field of `NestedProjectionTransportGap`**, given beta
conversion in arbitrary contexts in the final environment and projection-name
avoidance of the lowered constructor types (field `constructorProjNames` of
`NestedRestoredEquationGaps`). The source field type is a beta reduct of the
transported lowered field type. -/
theorem NestedValidatedRunResult.projectionPrimaryFields_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        C.finalBaseVEnv.BetaConversionAnyContext →
        (∀ lc ∈ E.production.loweredDecl.constructorConstants,
          lc.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
            true) →
        ∀ entry ∈ E.production.loweredDecl.projectionEntries,
          ∀ src ∈ sourceDecl.projectionEntries, src.typeName = entry.typeName →
          entry.info.ctorType.containsAnyConst
            (compilationRestoration sourceDecl auxiliaries).restorableNames = true →
          VEnv.ProjectionFieldTransport C.finalBaseVEnv
            ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
              fun _ => E.production.compilationSignature.params)
            (compilationRestoration sourceDecl auxiliaries).renaming
            entry.typeName entry.info src.info.ctorType := by
  intro auxiliaries D C hC hβ hPN₀ entry hentry src hsrc hname _
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion, -, D', Hrestoring, -⟩
  -- work with the table of `restorationTablesRestoringAll`
  rw [D.lambdaReplacement_eq D', D.renaming_eq D']
  have hPN : ∀ lc ∈ E.production.loweredDecl.constructorConstants,
      lc.type.projNamesAvoid (compilationRestoration sourceDecl aux').restorableNames =
        true := by
    intro lc hlc
    rw [← D.projNamesAvoid_eq D']
    exact hPN₀ lc hlc
  clear hPN₀
  let r := compilationRestoration sourceDecl aux'
  obtain ⟨-, -, hauxNames, hheadNames', -, -, -, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D' True.intro
  obtain ⟨-, hheadNames, hnp, hargs, hPclosed, -, -⟩ :=
    E.headerSetup wf hadded henvTypes Haux Hexpansion hnodup
  have hclosed := Restoration.lambdaReplacement_closed hnp hargs hPclosed
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hlevels := E.loweredConstructorLevels_heads wf Hsources hheadNames'
  have hordered := henvTypes.ordered
  have Hsource := E.nativeSource.core
  rw [E.nativeSourceDecl_eq] at Hsource
  have hsourceNodup := TrInductDeclCore.sourceNames_nodup Hsource
  -- source constructor types mention no restorable name
  have hsourceFree : ∀ family ∈ sourceDecl.types, ∀ sc ∈ family.ctors,
      sc.type.containsAnyConst r.restorableNames = false := by
    have htypesEq : E.nativeSource.envTypes = envTypes :=
      Option.some.inj (Hsource.typesAdded.symm.trans hadded)
    intro family hfamily sc hsc
    obtain ⟨T, -, hT⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hsource.types family hfamily
    obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r hT.ctors sc hsc
    obtain ⟨u, hu⟩ := hC.wf
    rw [htypesEq, hC.uvars, ← Hsource.uvars] at hu
    exact (hu.noFreshConsts hordered hfreshAll (by intro _ h; simp at h)).1
  -- the source type name is not restorable
  have hTN : entry.typeName ∉ r.restorableNames := by
    rw [← hname]
    obtain ⟨st₁, hst₁, ctor₁, _, hsrc₁⟩ := sourceDecl.projectionEntries_origin hsrc
    rw [hsrc₁]
    intro hm
    have h1 := hfreshAll _ hm
    have h2 := VEnv.addConstVals_get hadded
      (List.mem_map.mpr ⟨st₁, hst₁, rfl⟩ : st₁.toVConstVal ∈ sourceDecl.typeConstants)
    change envTypes.constants st₁.name = _ at h2
    rw [h1] at h2
    cases h2
  -- the expansion of the source families into the lowered prefix
  have hassembly := C.formationAssembly.types
  rw [C.formationExpanded, hC] at hassembly
  have hlen : sourceDecl.types.length =
      (E.production.loweredDecl.types.take sourceDecl.types.length).length := by
    have := Lean4Lean.List.Forall₂.length_eq hassembly
    simp only [List.length_append] at this
    simp only [List.length_take]
    omega
  rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types]
    at hassembly
  have hprefixExp := ((Lean4Lean.List.Forall₂.append_of_left hlen).mp hassembly).1
  have Hboth := Lean4Lean.List.Forall₂.and hprefixExp Hrestoring
  -- the lowered entry
  obtain ⟨t, ht, lc, hlct, rfl⟩ := E.production.loweredDecl.projectionEntries_origin hentry
  simp only at hTN hname ⊢
  have htTake : t ∈ E.production.loweredDecl.types.take sourceDecl.types.length := by
    rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at ht
    rcases List.mem_append.mp ht with h | h
    · exact h
    · exfalso
      apply hTN
      apply List.mem_append_left
      rw [hheadNames]
      exact mem_familyNames.mpr ⟨t, h, .inl rfl⟩
  obtain ⟨st, hst, hexpT, hrestT⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hboth t htTake
  have hlcmem : lc ∈ t.ctors := by rw [hlct]; exact List.mem_singleton_self lc
  obtain ⟨sc, hsc, hcexp⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r hexpT.constructors lc hlcmem
  obtain ⟨sc', hsc', hcrest⟩ := Lean4Lean.List.Forall₂.forall_exists_r hrestT lc hlcmem
  have hstCtors : st.ctors = [sc] := by
    have hl := Lean4Lean.List.Forall₂.length_eq hexpT.constructors
    rw [hlct] at hl
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
    rw [hx] at hsc ⊢
    rw [List.mem_singleton.mp hsc]
  have hsc'eq : sc' = sc := by
    rw [hstCtors] at hsc'
    simpa using hsc'
  rw [hsc'eq] at hcrest
  have hrestore : r.expr lc.type = some sc.type :=
    hcrest.restore (hsourceFree st hst sc hsc) (hlevels t htTake lc hlcmem)
  -- the given source entry is the entry of `st`
  have hsrcEntry : (⟨st.name, ⟨sourceDecl.uvars, sourceDecl.nparams, st.numIndices,
      st.resultLevel, sc.name, sc.type⟩⟩ : VProjectionEntry) ∈
        sourceDecl.projectionEntries := by
    rw [VInductDecl.projectionEntries, List.mem_filterMap]
    exact ⟨st, hst, by simp [hstCtors]⟩
  have hsrcEq := VInductDecl.projectionEntries_unique hsourceNodup hsrc hsrcEntry
    (by rw [hname]; exact hexpT.name)
  subst hsrcEq
  simp only
  -- the transported constructor type beta reduces to the source constructor type
  have hσtn : r.renaming t.name = t.name := Restoration.renaming_eq_self hTN
  have hfixLc : lc.type.ProjNamesFixed r.renaming :=
    Restoration.projNamesFixed_of_avoid
      (hPN lc (List.mem_flatMap.mpr ⟨t, ht, hlcmem⟩))
  have hBR : VExpr.BetaRed
      (lc.type.replaceRen (r.lambdaReplacement fun _ => E.production.compilationSignature.params)
        r.renaming) sc.type :=
    Restoration.expr_betaRed
      (fun c t' h => Restoration.lambdaReplacement_shape r (fun h hh => (hnp h hh).symm) h)
      (fun c h hf => by simp [Restoration.lambdaReplacement, hf])
      (fun c hf => Restoration.renaming_of_find_none hf) hfixLc hrestore
  intro levels params index major fieldType hfield
  have h1 := VProjectionInfo.fieldType_replaceRen' (typeName := t.name) (levels := levels)
    (params := params) (index := index) (major := major) (σ := r.renaming) hclosed
    ⟨E.production.loweredDecl.uvars, E.production.loweredDecl.nparams, t.numIndices,
      t.resultLevel, lc.name, lc.type⟩
  rw [hfield, hσtn] at h1
  obtain ⟨Y, hY, hXY⟩ := VProjectionInfo.fieldType_betaRed (ctorType' := sc.type) hBR h1
  exact ⟨Y, hY, fun hty => (hβ hXY hty).symm⟩

/-! ### The gap -/

/-- **The `auxiliary` field of `NestedProjectionTransportGap`**, the transport
of the projection rules of the auxiliary structure-like families (renamed to
their containers) in arbitrary contexts. It is not a consequence of the run:
the transported major premise of `projDF` has a beta-redex type
`(λ params, J levels args) params' indices'`, convertible to the syntactic
container application only when that redex has a typing, which an ill-formed
lowered context does not provide (module docstring). In well-formed contexts
the transport is the field `projections` of `RenamingReplacementOnCtx`. -/
def NestedAuxiliaryProjectionTransport
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (auxiliaries : List ContainerSpecialization) : Prop :=
  ∀ entry ∈ E.production.loweredDecl.projectionEntries,
    entry.typeName ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames →
    VEnv.ProjectionTransport C.finalBaseVEnv
      ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
        fun _ => E.production.compilationSignature.params)
      (compilationRestoration sourceDecl auxiliaries).renaming
      entry.typeName entry.info

/-- `NestedProjectionTransportGap` from beta conversion in arbitrary contexts,
projection-name avoidance of the lowered constructor types, and the auxiliary
transport. -/
theorem NestedValidatedRunResult.projectionTransportGap_of_projNames
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        C.finalBaseVEnv.BetaConversionAnyContext →
        (∀ lc ∈ E.production.loweredDecl.constructorConstants,
          lc.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
            true) →
        NestedAuxiliaryProjectionTransport E C auxiliaries →
        NestedProjectionTransportGap E C auxiliaries := by
  intro auxiliaries D C hC hβ hPN Haux
  exact { auxiliary := Haux
          primaryFields := E.projectionPrimaryFields_of wf Hsources auxiliaries D C hC hβ hPN }

/-- **`NestedProjectionTransportGap` for the run**, modulo beta conversion in
arbitrary contexts of the final environment (`primaryFields`) and the
auxiliary transport (`auxiliary`, not a consequence of the run). Projection-name
avoidance of the lowered constructor types is
`NestedValidatedRunResult.constructorProjNames_of`. -/
theorem NestedValidatedRunResult.projectionTransportGap_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.finalBaseVEnv →
        C.finalBaseVEnv.BetaConversionAnyContext →
        NestedAuxiliaryProjectionTransport E C auxiliaries →
        NestedProjectionTransportGap E C auxiliaries := by
  intro auxiliaries D C hC _hV hβ Haux
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, -, Haux', Hexpansion, -, D', -, -⟩
  have hPN := E.constructorProjNames_of wf hadded Haux' Hexpansion hnodup
  refine E.projectionTransportGap_of_projNames wf Hsources auxiliaries D C hC hβ ?_ Haux
  intro lc hlc
  rw [D.projNamesAvoid_eq D']
  exact hPN lc hlc

end VerifyInductive
end Lean4Lean

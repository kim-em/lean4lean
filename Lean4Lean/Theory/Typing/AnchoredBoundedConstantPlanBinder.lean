import Lean4Lean.Theory.Typing.AnchoredNativeBinderInterpretation
import Lean4Lean.Theory.Typing.AnchoredBoundedNativeBinderPair
import Lean4Lean.Theory.Typing.AnchoredNativeFitsFuture
import Lean4Lean.Theory.Typing.AnchoredConstantTelescope
import Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
import Lean4Lean.Theory.Typing.AnchoredSourceAdaptedLambdaFuture

namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

/-- Interpretation of one finite telescope-plan grammar at a fixed rank.
The generic binder proof consumes only the actual smaller-rank future child. -/
def ConstantPlanSupported (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (name : Name) (levels : List VLevel) {declaredType : VExpr}
    (signature : ConstantTelescope declaredType)
    (Plan : List VExpr → List VExpr → {n : Nat} → Profile n → Footprint → Type)
    (n : Nat) : Prop :=
  ∀ {target arguments newValues demand footprint support available},
    Plan target arguments (demand : Profile n) footprint →
    OnCtx target (env.IsType U) → arguments.length ≤ signature.domains.length →
    newValues.length = arguments.length → available.AtomClosed →
    Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst newValues)
      (signature.domains.take arguments.length).reverse →
    PairedFits current fuel env U registry (signature.domains.take arguments.length).reverse target
      (List.range arguments.length) (nativeCaptureSubst arguments)
      (nativeCaptureSubst newValues) available →
    footprint.Available available → demand.HasType support →
    TypeRelated env U registry target
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments)) support →
    Related env U registry target (mkApps (.const name levels) arguments)
      (mkApps (.const name levels) newValues)
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      demand support

private theorem lift_apps (ρ : Lift) (fn : VExpr) (args : List VExpr) :
    (mkApps fn args).lift' ρ = mkApps (fn.lift' ρ) (args.map (·.lift' ρ)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons a args ih => exact ih (.app fn a)

/-- The genuine binder induction step: original registered domain formation
extends the paired valuation, then the strict smaller-rank plan theorem
interprets the actual future child tree. -/
theorem ConstantPlanSupported.binder
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → Joint current fuel env U registry Γ l r A)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    {Plan : List VExpr → List VExpr → {n : Nat} → Profile n → Footprint → Type}
    (typeClosed : declaredType.Closed)
    (typeFormation : sourceEnv.IsDefEqStrong U [] declaredType declaredType (.sort typeLevel))
    (lower : ConstantPlanSupported current fuel env U registry name levels signature Plan n)
    {target : List VExpr} {arguments newValues : List VExpr}
    {domain : VExpr} {key : Key n} {output : Atom n}
    {domainSupport packed : Profile n} {support : Profile (n+1)}
    {domainFootprint bodyFootprint outside : Footprint} {available : Valuation}
    (origin : signature.domains[arguments.length]? = some domain)
    (domainCode : CodeCert env U registry target (List.range arguments.length)
      (nativeCaptureSubst arguments) domain domainSupport domainFootprint)
    (domainBound : domainCode.nativeDepth current ≤ fuel)
    (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key domainSupport)
    (futureBody : ∀ Δ ρ, FutureInsertion env U target Δ ρ →
      Plan Δ ((arguments ++ [key.anchor]).map (·.lift' ρ))
        (.singleton (output.rename ρ)) (Footprint.rename ρ bodyFootprint))
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (hTarget : OnCtx target (env.IsType U))
    (newLength : newValues.length = arguments.length)
    (closed : available.AtomClosed)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst newValues)
      (signature.domains.take arguments.length).reverse)
    (fits : PairedFits current fuel env U registry (signature.domains.take arguments.length).reverse target
      (List.range arguments.length) (nativeCaptureSubst arguments) (nativeCaptureSubst newValues) available)
    (resources : (domainFootprint ++ outside).Available available)
    (typed : (Profile.fn key output).HasType support)
    (code : TypeRelated env U registry target
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments)) support) :
    Related env U registry target (mkApps (.const name levels) arguments)
      (mkApps (.const name levels) newValues)
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      (Profile.fn key output) support := by
  have bound := (List.getElem?_eq_some_iff.mp origin).1
  obtain ⟨u, originalDomain⟩ := (signature.prefixFormation typeFormation arguments.length).2 bound
  rw [(List.getElem?_eq_some_iff.mp origin).2] at originalDomain
  have formedDomain := originalDomain.defeq.mono hle
  obtain ⟨v, originalBody⟩ := (signature.prefixFormation typeFormation (arguments.length+1)).1
  rw [signature.prefixContext_cons origin] at originalBody
  have formedBody := originalBody.defeq.mono hle
  let B := wrapForalls (signature.domains.drop (arguments.length+1)) signature.result
  let A := domain.subst (nativeCaptureSubst arguments)
  let C := B.subst (nativeCaptureSubst arguments).lift
  have rawA : env.IsType U target A := ⟨u, formedDomain.subst henv raw.left hTarget⟩
  have rawB : env.IsType U (A :: target) C :=
    ⟨v, formedBody.subst henv (raw.left.lift henv formedDomain) ⟨hTarget, rawA⟩⟩
  rw [signature.prefixResidual_cons origin] at code ⊢
  change TypeRelated env U registry target (.forallE A C) (.forallE A C) support at code
  change Related env U registry target _ _ (.forallE A C) _ _
  obtain ⟨protoA, protoB, dom, rows, result, member, wf, _, _, row, outTyped⟩ :=
    typed.fn_inv (List.mem_singleton_self _)
  change Profile n at dom result
  change List (Key n × Profile n) at rows
  have cover := code.singleton member
  have anchorCode := TypeRelated.literalPiArguments henv hscoped hTarget cover row guard.anchor
  have constructed := Related.nativeBinder henv hscoped hTarget rawA rawB cover row outTyped
    outTyped.wf_type guard.inputTyped guard.formed guard.path guard.domains guard.anchor
    (left := mkApps (.const name levels) arguments)
    (right := mkApps (.const name levels) newValues)
    (origin := mkApps (.const name levels) (arguments ++ [key.anchor])) ?_
  · exact constructed.retag henv typed code
  intro Δ ρ future z admitted
  have hΔ := future.targetWF henv
  have prefixLength : arguments.length = (signature.domains.take arguments.length).reverse.length := by
    simp only [List.length_reverse, List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  have raw' := raw.nativeFuture henv future prefixLength (newLength.trans prefixLength)
  have fits' := fits.nativeFuture henv future raw.wf prefixLength (newLength.trans prefixLength)
  have scope := signature.domain_scope typeClosed origin
  let domain' := (domainCode.future henv future).realizePrefix scope
    (nativeCaptureSubst (arguments.map (·.lift' ρ)))
    (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ hi)
  have guard' := guard.future henv future
  have he := subst_congr_closedN scope
    (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ hi)
  have guard'' : LambdaGuard env U registry Δ
      (nativeCaptureSubst (arguments.map (·.lift' ρ))) domain (key.rename ρ) (domainSupport.rename ρ) :=
    ⟨guard'.inputTyped, guard'.formed, he ▸ guard'.path, he ▸ guard'.domains, guard'.anchor⟩
  have body' := futureBody Δ ρ future
  simp only [List.map_append, List.map_cons, List.map_nil, Profile.rename_singleton] at body'
  have pack' := pack.rename ρ
  have covered' : ∀ a ∈ (packed.rename ρ).atoms, a ∈ (key.rename ρ).input.atoms := by
    intro a hm
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    exact List.mem_map_of_mem (covered b hb)
  have resources' := resources.rename ρ
  rw [Footprint.rename_append] at resources'
  have invoke {other : List VExpr}
      (length : other.length = arguments.length)
      (rawOther : Ctx.SubstEq env U Δ (nativeCaptureSubst (arguments.map (·.lift' ρ)))
        (nativeCaptureSubst other) (signature.domains.take arguments.length).reverse)
      (fitsOther : PairedFits current fuel env U registry (signature.domains.take arguments.length).reverse Δ
        (List.range arguments.length) (nativeCaptureSubst (arguments.map (·.lift' ρ)))
        (nativeCaptureSubst other) (Valuation.rename ρ available)) :
      Related env U registry Δ
        ((mkApps (.const name levels) (arguments ++ [key.anchor])).lift' ρ)
        (mkApps (.const name levels) (other ++ [z]))
        ((C.inst key.anchor).lift' ρ) (.singleton (output.rename ρ)) (result.rename ρ) := by
    obtain ⟨rawChild, fitsChild, resourcesChild⟩ := LambdaGuard.nativeBinderPair henv hscoped hΔ
      formedDomain (earlier originalDomain) (closed.rename ρ) rawOther fitsOther domain' (by
        simpa only [domain', CodeCert.nativeDepth_realizePrefix, CodeCert.nativeDepth_future] using domainBound) guard'' 
      pack' covered' resources' admitted
    have contextEq : (signature.domains.take
        ((arguments.map (·.lift' ρ)) ++ [key.anchor.lift' ρ]).length).reverse =
        domain :: (signature.domains.take arguments.length).reverse := by
      simpa only [List.length_append, List.length_map, List.length_singleton] using
        signature.prefixContext_cons origin
    have localsEq : List.range ((arguments.map (·.lift' ρ)) ++ [key.anchor.lift' ρ]).length =
        Locals.push (List.range arguments.length) := by
      simp only [List.length_append, List.length_map, List.length_singleton,
        List.range_succ_eq_map, Locals.push]
    have childCode := anchorCode.future henv future
    have Bscope : B.ClosedN (arguments ++ [key.anchor]).length := by
      have h := formedBody.closedN henv (CtxWF.closed henv ⟨raw.wf, ⟨u, formedDomain⟩⟩)
      simpa only [B, List.length_cons, List.length_reverse, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt bound), List.length_append, List.length_singleton, List.length_nil] using h
    have childType :
        (wrapForalls (signature.domains.drop
          ((arguments.map (·.lift' ρ)) ++ [key.anchor.lift' ρ]).length) signature.result).subst
          (nativeCaptureSubst ((arguments.map (·.lift' ρ)) ++ [key.anchor.lift' ρ])) =
        ((C.inst key.anchor).lift' ρ) := by
      simp only [List.length_append, List.length_map, List.length_singleton]
      have he := nativeCaptureSubst_rename_expression Bscope ρ
      simp only [List.map_append, List.map_cons, List.map_nil] at he
      rw [← he, nativeCaptureSubst_append, ← inst_lift_cons]
    have result' := lower (newValues := other ++ [z]) body' hΔ (by
        simp only [List.length_append, List.length_map, List.length_singleton]
        omega)
      (by simp only [List.length_append, List.length_map, List.length_singleton, length])
      (Valuation.push_atomized_closed (closed.rename ρ) _)
      (by simpa only [contextEq, nativeCaptureSubst_append, Key.rename] using rawChild)
      (by simpa only [contextEq, localsEq, nativeCaptureSubst_append, Key.rename] using fitsChild)
      resourcesChild (Profile.rename_hasType_iff.mpr outTyped)
      (by rw [childType]; exact childCode)
    simpa only [childType, lift_apps, lift', List.map_append, List.map_cons, List.map_nil] using result'
  have first := invoke (by simp only [List.length_map]) raw'.left fits'.left
  have second := invoke (by simp only [List.length_map, newLength]) raw' fits'
  have mapApp (args : List VExpr) :
      mkApps (.const name levels) (args.map (·.lift' ρ) ++ [z]) =
        .app ((mkApps (.const name levels) args).lift' ρ) z := by
    rw [lift_apps]
    simp only [lift', mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simpa only [mapApp] using And.intro first second

end Lean4Lean.AnchoredSource.Adapted.Staged

import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderPairedFrame
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFuture
import Lean4Lean.Theory.Typing.AnchoredNativeBinderInterpretation
import Lean4Lean.Theory.Typing.AnchoredConstantTelescope

/-! Native rich family plans are interpreted at their actual substitutions.
The telescope's captured variables, rather than an identity extension outside
its source context, determine the two displayed constant applications. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail InductiveSignature
set_option backward.isDefEq.respectTransparency false

def realizedCaptures (count : Nat) (σ : Subst) : List VExpr :=
  (constantCaptureVariables count).map (·.subst σ)

theorem realizedCaptures_cons (count : Nat) (σ : Subst) (value : VExpr) :
    realizedCaptures (count + 1) (σ.cons value) = realizedCaptures count σ ++ [value] := by
  simp only [realizedCaptures, constantCaptureVariables, List.range_succ_eq_map,
    List.reverse_cons, ← List.map_reverse, List.map_append, List.map_map, List.map_cons,
    List.map_nil, Function.comp_def, subst_bvar, Subst.cons]

theorem realizedCaptures_future (count : Nat) (σ : Subst) (ρ : Lift) :
    realizedCaptures count (σ.lift_r ρ) = (realizedCaptures count σ).map (·.lift' ρ) := by
  simp only [realizedCaptures, List.map_map, Function.comp_def, ← lift'_subst]

private theorem lift_apps (ρ : Lift) (fn : VExpr) (args : List VExpr) :
    (mkApps fn args).lift' ρ = mkApps (fn.lift' ρ) (args.map (·.lift' ρ)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons a args ih => exact ih (.app fn a)

def RichFamilyPlanSupported
    (header : EndpointRef headerEnv U [] declaredType (.sort headerLevel))
    (field : EndpointRef sourceEnv U source fieldExpression fieldAssigned)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (env : VEnv) (registry : CanonicalHead.Registry)
    (name : Name) (levels : List VLevel) (signature : ConstantTelescope declaredType) (n : Nat) : Prop :=
  ∀ {target arguments source} {context : ContextDerivation headerEnv U source}
    {σ τ : Subst} {demand support : Profile n} {footprint available},
    RichFamilyPlan env U registry target header name levels signature context σ arguments demand footprint →
    OnCtx target (env.IsType U) → arguments.length ≤ signature.domains.length →
    source = (signature.domains.take arguments.length).reverse → available.AtomClosed →
    Ctx.SubstEq env U target σ τ source →
    HeaderBinderFrame header field major env registry target context (List.range arguments.length) σ τ available →
    footprint.Available available → demand.HasType support →
    TypeRelated env U registry target
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ)
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ) support →
    Related env U registry target (mkApps (.const name levels) (realizedCaptures arguments.length σ))
      (mkApps (.const name levels) (realizedCaptures arguments.length τ))
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ) demand support

/-- The actual rich domain certificate enters each child frame unchanged.
The only semantic recursion is the smaller-rank future body plan. -/
theorem RichFamilyPlanSupported.binder
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldAssigned}
    {major : EndpointRef sourceEnv U source majorExpression majorAssigned}
    {signature : ConstantTelescope declaredType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (lower : RichFamilyPlanSupported header field major env registry name levels signature n)
    {arguments : List VExpr} {key : Key n} {output : Atom n}
    (origin : signature.domains[arguments.length]? = some domain)
    (original : EndpointRef headerEnv U headerSource domain (.sort level))
    (location : Located header (.ref original)) (lineage : location.contextDerivation .nil = context)
    (domainCode : RichCert headerEnv env U registry target (.ref original) (List.range arguments.length)
      σ true domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target σ domain key domainSupport)
    (body : RichFamilyPlan env U registry target header name levels signature (.cons context original)
      (σ.cons key.anchor) (arguments ++ [key.anchor]) (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (formed : OnCtx target (env.IsType U))
    (sourceEq : headerSource = (signature.domains.take arguments.length).reverse)
    (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target σ τ headerSource)
    (frame : HeaderBinderFrame header field major env registry target context (List.range arguments.length) σ τ available)
    (resources : (domainFootprint ++ outside).Available available)
    (typed : (Profile.fn key output).HasType support)
    (code : TypeRelated env U registry target
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ)
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ) support) :
    Related env U registry target (mkApps (.const name levels) (realizedCaptures arguments.length σ))
      (mkApps (.const name levels) (realizedCaptures arguments.length τ))
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst σ)
      (Profile.fn key output) support := by
  have bound := (List.getElem?_eq_some_iff.mp origin).1
  have formedDomain := original.sound.defeq.mono headerBelow
  obtain ⟨v, originalBody⟩ := (signature.prefixFormation header.sound (arguments.length + 1)).1
  rw [signature.prefixContext_cons origin, ← sourceEq] at originalBody
  have formedBody := originalBody.defeq.mono headerBelow
  let B := wrapForalls (signature.domains.drop (arguments.length + 1)) signature.result
  let A := domain.subst σ
  let C := B.subst σ.lift
  have rawA : env.IsType U target A := ⟨level, formedDomain.subst henv substitutions.left formed⟩
  have rawB : env.IsType U (A :: target) C :=
    ⟨v, formedBody.subst henv (substitutions.left.lift henv formedDomain) ⟨formed, rawA⟩⟩
  rw [signature.prefixResidual_cons origin] at code ⊢
  change TypeRelated env U registry target (.forallE A C) (.forallE A C) support at code
  change Related env U registry target _ _ (.forallE A C) _ _
  obtain ⟨protoA, protoB, dom, rows, result, member, _, _, _, row, outTyped⟩ :=
    typed.fn_inv (List.mem_singleton_self _)
  change Profile n at dom result
  change List (Key n × Profile n) at rows
  have cover := code.singleton member
  have anchorCode := TypeRelated.literalPiArguments henv hscoped formed cover row guard.anchor
  apply Related.retag henv typed code
  apply Related.nativeBinder henv hscoped formed rawA rawB cover row outTyped
    outTyped.wf_type guard.inputTyped guard.formed guard.path guard.domains guard.anchor
    (origin := mkApps (.const name levels) (realizedCaptures arguments.length σ ++ [key.anchor]))
  intro next ρ future z admitted
  have nextFormed := future.targetWF henv
  let domain' := domainCode.future henv future
  have guard' := guard.future henv future
  have pack' := pack.rename ρ
  have covered' : ∀ atom ∈ (packed.rename ρ).atoms, atom ∈ (key.rename ρ).input.atoms := by
    intro atom member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    exact List.mem_map_of_mem (covered old oldMember)
  have resources' := resources.rename ρ
  rw [Footprint.rename_append] at resources'
  let body' := body.future henv future
  have invoke {other : Subst}
      (rawOther : Ctx.SubstEq env U next (σ.lift_r ρ) other headerSource)
      (otherFrame : HeaderBinderFrame header field major env registry next context (List.range arguments.length)
        (σ.lift_r ρ) other (available.rename ρ)) :
      Related env U registry next
        ((mkApps (.const name levels) (realizedCaptures arguments.length σ ++ [key.anchor])).lift' ρ)
        (mkApps (.const name levels) (realizedCaptures arguments.length other ++ [z]))
        ((C.inst key.anchor).lift' ρ) (.singleton (output.rename ρ)) (result.rename ρ) := by
    have domainResources : (Footprint.rename ρ domainFootprint).Available (available.rename ρ) :=
      fun i need hm => resources' i need (List.mem_append_left _ hm)
    have outsideResources : (Footprint.rename ρ outside).Available (available.rename ρ) :=
      fun i need hm => resources' i need (List.mem_append_right _ hm)
    let required := Footprint.rename ρ bodyFootprint
    let needs := required.localNeeds ++ required.localNeeds.flatMap Need.singletons
    obtain ⟨rawAnchor, _, _, _, _, _, anchor, _⟩ := admitted
    have pair := Related.convert henv guard'.inputTyped guard'.domains anchor
    let childFrame := HeaderBinderFrame.bind otherFrame original location lineage domain' domainResources
      guard'.inputTyped pair needs
      (fun need hm => (pack'.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered' atom ((pack'.atomized_localNeeds need hm).2 atom ha))
    have childRaw : Ctx.SubstEq env U next
        ((σ.lift_r ρ).cons (key.anchor.lift' ρ)) (other.cons z) (domain :: headerSource) :=
      .cons rawOther formedDomain (guard'.path.cast rawAnchor)
    have childSource : domain :: headerSource =
        (signature.domains.take ((arguments ++ [key.anchor]).map (·.lift' ρ)).length).reverse := by
      simp only [List.length_map, List.length_append, List.length_singleton]
      rw [signature.prefixContext_cons origin, sourceEq]
    have localsEq : List.range ((arguments ++ [key.anchor]).map (·.lift' ρ)).length =
        Locals.push (List.range arguments.length) := by
      simp only [List.length_map, List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
    have childType :
        (wrapForalls (signature.domains.drop ((arguments ++ [key.anchor]).map (·.lift' ρ)).length)
          signature.result).subst ((σ.cons key.anchor).lift_r ρ) = ((C.inst key.anchor).lift' ρ) := by
      simp only [List.length_map, List.length_append, List.length_singleton, ← lift'_subst, C, B, inst_lift_cons]
    have child := lower body' nextFormed (by
        simp only [List.length_map, List.length_append, List.length_singleton]; omega)
      childSource (Valuation.push_atomized_closed (closed.rename ρ) required.localNeeds)
      (by simpa only [subst_cons_future] using childRaw)
      (by simpa only [localsEq, subst_cons_future, Key.rename, needs] using childFrame)
      (pack'.available_atomized_localNeeds outsideResources) (Profile.rename_hasType_iff.mpr outTyped)
      (by rw [childType]; exact anchorCode.future henv future)
    rw [childType] at child
    simpa only [List.length_map, List.length_append, List.length_singleton, realizedCaptures_future,
      realizedCaptures_cons, lift_apps, lift', List.map_append, List.map_cons, List.map_nil,
      Profile.rename_singleton] using child
  have raw' := substitutions.future henv future
  have frame' := frame.future henv future
  have first := invoke raw'.left frame'.leftDiagonal
  have second := invoke raw' frame'
  have mapApp (s : Subst) :
      mkApps (.const name levels) (realizedCaptures arguments.length (s.lift_r ρ) ++ [z]) =
        .app ((mkApps (.const name levels) (realizedCaptures arguments.length s)).lift' ρ) z := by
    rw [realizedCaptures_future, lift_apps]
    simp only [lift', mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simpa only [mapApp] using And.intro first second

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource

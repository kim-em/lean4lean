import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPackingData
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationInput
import Lean4Lean.Theory.Typing.AnchoredOriginalRichOutputReplay

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {function : EndpointState sourceEnv U source f (.forallE A B)}
  {argument : EndpointState sourceEnv U source a A}
  {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available}
  {substitutions : Ctx.SubstEq env U target σ τ source}
  {ordered : sourceEnv.Ordered}

/-- Both the key and its adapted original argument query are computed from
ONE exact pack. The raw observer need not equal the advertised key input. -/
theorem ApplicationBackwardQueries.piRequestWithArgument
    {n : Nat} {profile : Profile n}
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (domainF : OriginalCodeInductionAt env registry ordered initial (.appDomain location)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (supply : RichArgumentSupply sourceEnv env U registry target argument locals σ available packet.footprint.localNeeds) :
    Nonempty (GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant profile) := by
  obtain ⟨packed⟩ := packet.typedPack (n := n) henv hscoped formed closed domainF
  obtain ⟨argumentQuery⟩ := binderPackArgumentQuery henv hscoped formed packed.pack supply
  let key : Key packed.rank := ⟨A.subst σ, a.subst σ, packed.input⟩
  have raw := (argument.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions.left
  have related := packed.related.left_diagonal
  have guard : LambdaGuard env U registry target σ A key packed.support :=
    ⟨packed.typed, packed.certificate.formed, .refl, packed.code,
      ⟨raw, raw, packed.support, packed.typed, packed.certificate.formed, packed.code, related, related⟩⟩
  have bodyCode : RichCert sourceEnv env U registry target body (Locals.push locals)
      (σ.cons (a.subst σ)) relevant (raiseProfile packed.rank packed.bound profile) packet.footprint := by
    have positions := packet.reply.answer.reply.locals_eq
    change packet.reply.answer.reply.locals = Locals.push locals at positions
    have realization : (Subst.id.cons (a.subst .id)).comp σ = σ.cons (a.subst σ) := by
      funext i; cases i <;> simp only [Subst.comp, Subst.cons, subst_id] <;> rfl
    simpa only [positions, realization] using packet.certificate.raise packed.bound
  let rows : RichRows sourceEnv env U registry target (.ref domain) body locals σ relevant
      packed.support [(key, raiseProfile packed.rank packed.bound profile)] (packed.outside ++ []) :=
    .cons guard bodyCode packed.pack (fun _ member => member) .nil
  let request : GeneratedApplicationPiRequest domain body hu hv env registry target locals σ available a relevant profile :=
    ⟨packed.rank, packed.bound, key, packed.support,
      packed.footprint ++ (packed.outside ++ []),
      .pi hu hv packed.certificate PiGuard.literal rows,
      (fun i need member => (List.mem_append.mp member).elim
        (packed.resources i need)
        (fun member => packed.external i need (by simpa only [List.append_nil] using member))),
      guard.anchor, rfl⟩
  exact ⟨⟨request, argumentQuery, packed.footprint, packed.certificate,
    packed.resources, packed.typed, packed.code⟩⟩
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource

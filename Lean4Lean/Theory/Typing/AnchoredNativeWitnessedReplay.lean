import Lean4Lean.Theory.Typing.AnchoredNativeSupportedReplay

/-! The witnessed capture valuation is available in the original target
world. Each diagonal data entry reuses its stored source certificate on both
sides; no new proof slot or declaration-stage semantic call is needed. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem NativeSupportedReplay.witnessed
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hle : sourceEnv ≤ env)
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (rawArguments : Ctx.SubstEq env U target arguments arguments argumentSource)
    (argumentFits : PairedFits env U registry argumentSource target argumentLocals
      arguments arguments argumentAvailable)
    {declared : List VExpr} {plan : CapturePlan declared} {captures : Subst}
    {locals : List Nat} {available : Valuation}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available) :
    Ctx.SubstEq env U target captures captures declared ∧
    PairedFits env U registry declared target locals captures captures available := by
  induction replay with
  | nil => exact ⟨.nil, .nil⟩
  | @commonPrefix later declared plan source literal count added captures =>
    have raw := rawArguments
    have fits := argumentFits
    rw [source] at raw fits
    exact ⟨Ctx.SubstEq.nativePrefix raw, fits.nativePrefix (List.range declared.length)⟩
  | @index n level declared plan captures locals available domain natural position support input footprint
      previous formation lookup needed domainCode resources typed alignment declaredCode closed localNeeds bounded covered ih =>
    obtain ⟨raw, fits⟩ := ih
    have formed := formation.defeq.mono hle |>.hasType.1
    obtain ⟨entry⟩ := argumentFits.forward.entry position ⟨n, input⟩ needed natural lookup
    have pair := alignment.related henv typed declaredCode entry.related
    exact ⟨.cons raw formed (alignment.path.cast (rawArguments.lookup lookup)),
      fits.pushCertificates henv hTarget domainCode domainCode resources resources
        typed typed pair pair localNeeds bounded covered⟩
  | @proof declared plan captures locals available domain witness previous formation inhabitant
      localNeeds n bounded empty ih =>
    obtain ⟨raw, fits⟩ := ih
    have certificate : CodeCert env U registry target locals captures domain
        (Profile.empty (n := n)) [] := .seed .empty (.empty (.sort true))
    have related : Related env U registry target witness witness (domain.subst captures)
        (Profile.empty (n := n)) .empty := by
      apply Related.of_singletons
      intro atom member
      cases member
    exact ⟨.cons raw formation inhabitant,
      fits.pushCertificates henv hTarget certificate certificate
        (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
        (.empty .empty) (.empty .empty) related related localNeeds bounded
        (fun need member atom atomMember => (empty need member atom atomMember).elim)⟩

end Lean4Lean.AnchoredSource.Adapted

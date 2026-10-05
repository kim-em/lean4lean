import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFrame
import Lean4Lean.Theory.Typing.AnchoredLiteralPiPair

/-! Reconstruct Pi-shaped declared field types from actual captured fields.
The domain and codomain retain their original header occurrences. Each finite
row queries the captured codomain slot, including in future target contexts.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem capturedRows
    {domain : EndpointState headerEnv U source (.bvar domainIndex) (.sort u)}
    {body : EndpointState headerEnv U (.bvar domainIndex :: source)
      (.bvar (bodyIndex + 1)) (.sort v)}
    {ambient : Profile n} (rows : List (Key n × Profile n))
    (guards : ∀ key support, (key, support) ∈ rows →
      LambdaGuard env U registry target σ (.bvar domainIndex) key ambient)
    (formed : ∀ key support, (key, support) ∈ rows → support.HasType (.sort relevant))
    (needs : ∀ key support, (key, support) ∈ rows → Need.mk n support ∈ available bodyIndex) :
    ∃ footprint, Nonempty (RichRows headerEnv env U registry target domain body
      locals σ relevant ambient rows footprint) ∧ footprint.Available available := by
  induction rows with
  | nil => exact ⟨[], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | cons row rows ih =>
    obtain ⟨key, support⟩ := row
    obtain ⟨footprint, ⟨rest⟩, resources⟩ := ih
      (fun key support member => guards key support (List.mem_cons_of_mem _ member))
      (fun key support member => formed key support (List.mem_cons_of_mem _ member))
      (fun key support member => needs key support (List.mem_cons_of_mem _ member))
    let code : RichCert headerEnv env U registry target body (Locals.push locals)
        (σ.cons key.anchor) relevant support [(bodyIndex + 1, Need.mk n support)] :=
      .legacy (.seed (.var _ _ _ support) (formed key support List.mem_cons_self))
    refine ⟨[(bodyIndex, Need.mk n support)] ++ footprint,
      ⟨.cons (guards key support List.mem_cons_self) code (.external _ _ .nil)
        (fun _ member => nomatch member) rest⟩, ?_⟩
    intro index need member
    rcases List.mem_append.mp member with member | member
    · cases List.mem_singleton.mp member
      exact needs key support List.mem_cons_self
    · exact resources index need member

/-- Produce a native rich Pi certificate, at the exact original Pi node,
for a declared `T → S` whose two types are previously captured values.
The captured values may themselves be dependent projections. No semantic
Pi capability or source certificate is supplied by the caller. -/
theorem HeaderBinderFrame.capturedPi
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (tail : HeaderBinderFrame header field major env registry target context locals σ τ available)
    (domain : EndpointRef headerEnv U headerSource (.bvar domainIndex) (.sort u))
    (body : EndpointState headerEnv U (.bvar domainIndex :: headerSource)
      (.bvar (bodyIndex + 1)) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    {ambient : Profile n} (rows : List (Key n × Profile n))
    (ambientFormed : ambient.HasType (.sort true))
    (domainNeed : Need.mk n ambient ∈ available domainIndex)
    (domainLookup : Lookup headerSource domainIndex domainType)
    (bodyLookup : Lookup headerSource bodyIndex bodyType)
    (guard : PiGuard env U target σ (.bvar domainIndex) (.bvar (bodyIndex + 1))
      prototypeDomain prototypeBody)
    (guards : ∀ key support, (key, support) ∈ rows →
      LambdaGuard env U registry target σ (.bvar domainIndex) key ambient)
    (rowFormed : ∀ key support, (key, support) ∈ rows → support.HasType (.sort relevant))
    (rowNeeds : ∀ key support, (key, support) ∈ rows → Need.mk n support ∈ available bodyIndex) :
    ∃ footprint,
      Nonempty (RichCert headerEnv env U registry target (.pi hu hv (.ref domain) body)
        locals σ relevant (Profile.pi prototypeDomain prototypeBody ambient rows) footprint) ∧
      footprint.Available available ∧
      TypeRelated env U registry target
        ((VExpr.forallE (.bvar domainIndex) (.bvar (bodyIndex + 1))).subst σ)
        ((VExpr.forallE (.bvar domainIndex) (.bvar (bodyIndex + 1))).subst σ)
        (Profile.pi prototypeDomain prototypeBody ambient rows) := by
  obtain ⟨rowFootprint, ⟨rowCode⟩, rowResources⟩ := capturedRows
    (domain := EndpointState.ref domain) (body := body) rows guards rowFormed rowNeeds
  let domainCode : RichCert headerEnv env U registry target (.ref domain) locals σ true
      ambient [(domainIndex, Need.mk n ambient)] :=
    .legacy (.seed (.var locals σ domainIndex ambient) ambientFormed)
  refine ⟨_, ⟨.pi hu hv domainCode guard rowCode⟩, ?_, ?_⟩
  · intro index need member
    rcases List.mem_append.mp member with member | member
    · cases List.mem_singleton.mp member
      exact domainNeed
    · exact rowResources index need member
  · obtain ⟨entry⟩ := tail.lookup henv formed domainNeed domainLookup
    have domainRelated :=
      (entry.related.code_of_sortable henv hscoped formed ambientFormed).left_diagonal
    have originalDomain := domain.sound.defeq.mono headerBelow
    have originalBody := body.sound.defeq.mono headerBelow
    have hA := originalDomain.subst henv substitutions formed
    have hB := originalBody.subst henv (substitutions.lift henv originalDomain) ⟨formed, _, hA⟩
    apply TypeRelated.literalPiPair henv formed ⟨_, hA⟩ ⟨_, hA⟩ ⟨_, hB⟩ ⟨_, hB⟩
      .refl .refl guard.domainPath guard.bodyPath domainRelated
    · intro key output member
      have selected := guards key output member
      exact ⟨ambient, selected.inputTyped, ambientFormed, Profile.le_refl _,
        selected.path, selected.domains⟩
    · intro key output member Δ ρ future x y admitted
      obtain ⟨entry⟩ := tail.lookup henv formed (rowNeeds key output member) bodyLookup
      have result :=
        ((entry.related.code_of_sortable henv hscoped formed (rowFormed key output member)).left_diagonal).future henv future
      have instantiated (z : VExpr) :
          (((VExpr.bvar (bodyIndex + 1)).subst σ.lift).lift' ρ.cons).inst z =
            (σ bodyIndex).lift' ρ := by
        rw [lift'_subst, ← Subst.lift_r_lift, inst_lift_cons]
        rfl
      have row : TypeRelated env U registry Δ
          (((VExpr.bvar (bodyIndex + 1)).subst σ.lift).lift' ρ.cons |>.inst x)
          (((VExpr.bvar (bodyIndex + 1)).subst σ.lift).lift' ρ.cons |>.inst y)
          (output.rename ρ) := by
        simpa only [instantiated] using result
      exact ⟨row, row, by simpa only [instantiated] using result⟩

private theorem boundRows
    {domain : EndpointState headerEnv U source A (.sort u)}
    {body : EndpointState headerEnv U (A :: source) (.bvar 0) (.sort v)}
    {ambient : Profile n} (rows : List (Key n × Profile n))
    (guards : ∀ key support, (key, support) ∈ rows →
      LambdaGuard env U registry target σ A key ambient)
    (formed : ∀ key support, (key, support) ∈ rows → support.HasType (.sort relevant))
    (covered : ∀ key support, (key, support) ∈ rows →
      ∀ atom ∈ support.atoms, atom ∈ key.input.atoms) :
    Nonempty (RichRows headerEnv env U registry target domain body
      locals σ relevant ambient rows []) := by
  induction rows with
  | nil => exact ⟨.nil⟩
  | cons row rows ih =>
    obtain ⟨key, support⟩ := row
    obtain ⟨rest⟩ := ih
      (fun key support member => guards key support (List.mem_cons_of_mem _ member))
      (fun key support member => formed key support (List.mem_cons_of_mem _ member))
      (fun key support member => covered key support (List.mem_cons_of_mem _ member))
    let code : RichCert headerEnv env U registry target body (Locals.push locals)
        (σ.cons key.anchor) relevant support [(0, Need.mk n support)] :=
      .legacy (.seed (.var _ _ _ support) (formed key support List.mem_cons_self))
    have pack : BinderPack n support [(0, Need.mk n support)] [] := by
      simpa only [Need.atGrade, dif_pos (Nat.le_refl n), raiseProfile_self,
        Profile.union, Profile.empty, Profile.atoms, Profile.mk, List.append_nil] using
        (BinderPack.local (Need.mk n support) (Nat.le_refl n) BinderPack.nil)
    exact ⟨.cons (guards key support List.mem_cons_self) code pack
      (covered key support List.mem_cons_self) rest⟩

/-- The codomain can be the freshly bound argument itself. Every row's
body certificate is made at the actual original body occurrence, with the
exact finite local demand packed against the original input. Future body
capabilities follow from the same admitted pair, with no synthetic owner. -/
theorem HeaderBinderFrame.boundPi
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available)
    (domain : EndpointRef headerEnv U headerSource (.bvar domainIndex) (.sort u))
    (body : EndpointState headerEnv U (.bvar domainIndex :: headerSource) (.bvar 0) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    {ambient : Profile n} (rows : List (Key n × Profile n))
    (ambientFormed : ambient.HasType (.sort true))
    (domainNeed : Need.mk n ambient ∈ available domainIndex)
    (domainLookup : Lookup headerSource domainIndex domainType)
    (guard : PiGuard env U target σ (.bvar domainIndex) (.bvar 0) prototypeDomain prototypeBody)
    (guards : ∀ key support, (key, support) ∈ rows →
      LambdaGuard env U registry target σ (.bvar domainIndex) key ambient)
    (rowFormed : ∀ key support, (key, support) ∈ rows → support.HasType (.sort relevant))
    (covered : ∀ key support, (key, support) ∈ rows →
      ∀ atom ∈ support.atoms, atom ∈ key.input.atoms) :
    Nonempty (RichCert headerEnv env U registry target (.pi hu hv (.ref domain) body)
      locals σ relevant (Profile.pi prototypeDomain prototypeBody ambient rows)
      [(domainIndex, Need.mk n ambient)]) ∧
    TypeRelated env U registry target
      ((VExpr.forallE (.bvar domainIndex) (.bvar 0)).subst σ)
      ((VExpr.forallE (.bvar domainIndex) (.bvar 0)).subst σ)
      (Profile.pi prototypeDomain prototypeBody ambient rows) := by
  obtain ⟨rowCode⟩ := boundRows (domain := EndpointState.ref domain) (body := body)
    rows guards rowFormed covered
  let domainCode : RichCert headerEnv env U registry target (.ref domain) locals σ true
      ambient [(domainIndex, Need.mk n ambient)] :=
    .legacy (.seed (.var locals σ domainIndex ambient) ambientFormed)
  refine ⟨⟨.pi hu hv domainCode guard rowCode⟩, ?_⟩
  obtain ⟨entry⟩ := frame.lookup henv formed domainNeed domainLookup
  have domainRelated :=
    (entry.related.code_of_sortable henv hscoped formed ambientFormed).left_diagonal
  have originalDomain := domain.sound.defeq.mono headerBelow
  have originalBody := body.sound.defeq.mono headerBelow
  have hA := originalDomain.subst henv substitutions formed
  have hB := originalBody.subst henv (substitutions.lift henv originalDomain) ⟨formed, _, hA⟩
  apply TypeRelated.literalPiPair henv formed ⟨_, hA⟩ ⟨_, hA⟩ ⟨_, hB⟩ ⟨_, hB⟩
    .refl .refl guard.domainPath guard.bodyPath domainRelated
  · intro key output member
    have selected := guards key output member
    exact ⟨ambient, selected.inputTyped, ambientFormed, Profile.le_refl _,
      selected.path, selected.domains⟩
  · intro key output member Δ ρ future x y admitted
    obtain ⟨_, _, oldSupport, _, _, _, _, pair⟩ := admitted
    have smaller : Related env U registry Δ x y ((key.rename ρ).domain)
        (output.rename ρ) oldSupport := by
      apply Related.of_singletons
      intro atom atomMember
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp atomMember
      exact Related.singleton_of_mem pair (List.mem_map_of_mem (covered key output member old oldMember))
    have result := smaller.code_of_sortable henv hscoped (future.targetWF henv)
      (by simpa only [Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr (rowFormed key output member))
    have instantiated (z : VExpr) :
        (((VExpr.bvar 0).subst σ.lift).lift' ρ.cons).inst z = z := by
      simp [subst, Subst.lift, lift', Lift.liftVar, inst]
    exact ⟨by simpa only [instantiated] using result,
      by simpa only [instantiated] using result,
      by simpa only [instantiated] using result.left_diagonal⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource

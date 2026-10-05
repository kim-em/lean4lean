import Lean4Lean.Theory.Typing.AnchoredOriginalRichFramePeel
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichLookupDepth

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
set_option backward.isDefEq.respectTransparency false

structure OriginalRichHeadCode
    {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (locals : List Nat) (left right : Subst) (available : Valuation) (need : Need) where
  support : Profile need.rank
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target (.ref domain) locals left.tail true support footprint
  resources : footprint.Available (fun i => available (i+1))
  typed : need.profile.HasType support
  related : Related env U registry target left.head right.head (A.subst left.tail) need.profile support

private noncomputable def lowerHead
    {right : Subst}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals left true
      (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (related : Related env U registry target x y (A.subst left) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (member : need ∈ needs) :
    OriginalRichHeadCode (env := env) (registry := registry) (target := target)
      domain locals (left.cons x) (right.cons y) (available.push needs) need := by
  have hn := bounded need member
  have hc := covered need member
  simp only [Need.atGrade, dif_pos hn] at hc
  have ht := lowerProfile.hasType hn (typed_subset hc typed)
  have hr : Related env U registry target x y (A.subst left)
      (raiseProfile n hn need.profile) support :=
    Related.of_singletons (fun atom hm => related.singleton_of_mem (hc atom hm))
  exact ⟨_, _, certificate.lower need.rank hn, resources, ht, lowerProfile.related hn henv formed hr⟩

private theorem headerHead
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {header : EndpointRef sourceEnv U [] he ht}
    {field : EndpointRef capturedEnv U capturedSource fe ft}
    {major : EndpointRef capturedEnv U capturedSource me majorType}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (frame : HeaderBinderFrame header field major env registry target
      (.cons context domain) locals left right available)
    (member : need ∈ available 0) :
    ∃ tailLocals, Locals.push tailLocals = locals ∧
      Nonempty (OriginalRichHeadCode (env := env) (registry := registry) (target := target)
        domain tailLocals left right available need) := by
  cases frame with
  | bind tail domain location lineage certificate resources typed arguments needs bounded covered =>
    exact ⟨_, rfl, ⟨lowerHead henv formed certificate resources typed arguments needs bounded covered member⟩⟩
  | captured tail =>
    cases tail with
    | skip tail domain location lineage arguments => cases member
    | push tail domain location lineage owner answer arguments needs bounded covered =>
      exact ⟨_, rfl, ⟨lowerHead henv formed answer.aligned.certificate answer.aligned.resources
        answer.value.typed arguments needs bounded covered member⟩⟩

/-- Every head demand is supported at the exact original declared domain,
with resources in the complete suffix table, including all merge branches. -/
theorem OriginalRichFrame.headCode
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (frame : OriginalRichFrame sourceEnv env U registry target
      (.cons context domain) locals left right available)
    (member : need ∈ available 0) :
    Nonempty (OriginalRichHeadCode (env := env) (registry := registry) (target := target)
      domain frame.peel.tailLocals left right available need) := by
  suffices answer : ∃ tailLocals, Locals.push tailLocals = locals ∧
      Nonempty (OriginalRichHeadCode (env := env) (registry := registry) (target := target)
        domain tailLocals left right available need) by
    obtain ⟨tailLocals, positions, answer⟩ := answer
    have same : tailLocals = frame.peel.tailLocals :=
      (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp
        (List.cons.inj (positions.trans frame.peel.positions.symm)).2
    cases same
    exact answer
  rcases frame with ⟨raw, valid⟩
  match raw, valid with
  | .reserve frame _, valid =>
    let inner : OriginalRichFrame _ _ _ _ _ _ _ _ _ _ :=
      ⟨frame, by simpa only [RawOriginalRichFrame.Valid] using valid⟩
    exact ⟨inner.peel.tailLocals, inner.peel.positions, inner.headCode henv formed member⟩
  | .header _ _ header, _ => exact headerHead henv formed header member
  | .bind tail domain certificate resources typed arguments needs bounded covered, _ =>
    exact ⟨_, rfl, ⟨lowerHead henv formed certificate resources typed arguments needs bounded covered member⟩⟩
  | .capture tail domain _ _ _ _ _ _ certificate resources typed arguments needs bounded covered, _ =>
    exact ⟨_, rfl, ⟨lowerHead henv formed certificate resources typed arguments needs bounded covered member⟩⟩
  | .group tail domain ordered initial entries, _ =>
    obtain ⟨support, fp, certificate, resources, typed, related, _⟩ :=
      entries.lookup_allDepth henv formed member
    exact ⟨_, rfl, ⟨⟨support, fp, certificate, resources, typed, related⟩⟩⟩
  | .merge first second, valid =>
    simp only [RawOriginalRichFrame.Valid] at valid
    rcases List.mem_append.mp member with member | member
    · let selected : OriginalRichFrame _ _ _ _ _ _ _ _ _ _ := ⟨first, valid.1⟩
      obtain ⟨answer⟩ := selected.headCode henv formed member
      exact ⟨_, selected.peel.positions, ⟨{ answer with
        resources := fun i need hm => List.mem_append_left _ (answer.resources i need hm) }⟩⟩
    · let selected : OriginalRichFrame _ _ _ _ _ _ _ _ _ _ := ⟨second, valid.2⟩
      obtain ⟨answer⟩ := selected.headCode henv formed member
      exact ⟨_, selected.peel.positions, ⟨{ answer with
        resources := fun i need hm => List.mem_append_right _ (answer.resources i need hm) }⟩⟩
termination_by sizeOf frame.raw
decreasing_by all_goals simp_wf <;> omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource

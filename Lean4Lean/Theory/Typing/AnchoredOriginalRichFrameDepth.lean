import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame
import Lean4Lean.Theory.Typing.AnchoredOriginalRichRawFrameDepth

/-! Declaration fuel counts every retained source certificate, separately
from the original-proof closure measure. In a captured entry both the owner's
assigned-type query and its aligned header-domain query are counted. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

@[simp] theorem RichCert.nativeDepth_lower (current : Name → Bool) {n N : Nat}
    {profile : Profile N}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (bound : n ≤ N) :
    (certificate.lower n bound).nativeDepth current = certificate.nativeDepth current := by
  induction N with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases hn : n = N + 1
    · subst n
      simp only [RichCert.lower, Nat.recAux, dite_true]
      exact RichCert.nativeDepth_mpr current rfl rfl (lowerProfile_self ..).symm rfl _ certificate
    · simp only [RichCert.lower, Nat.recAux, dif_neg hn]
      refine (RichCert.nativeDepth_mpr current rfl rfl
        (lowerProfile_step (show n ≤ N by omega) profile).symm rfl _ _).trans ?_
      change (certificate.down.lower n (show n ≤ N by omega)).nativeDepth current = _
      simpa only [RichCert.nativeDepth] using ih (.down certificate) (by omega)

noncomputable def OriginalRichFrame.nativeDepth (current : Name → Bool)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Nat :=
  frame.raw.nativeDepth current

@[simp] theorem OriginalRichFrame.nativeDepth_merge (current : Name → Bool)
    {context : ContextDerivation sourceEnv U source}
    (left : OriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable)
    (right : OriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable) :
    (left.merge right).nativeDepth current = max (left.nativeDepth current) (right.nativeDepth current) := by
  simp only [OriginalRichFrame.nativeDepth, OriginalRichFrame.merge, RawOriginalRichFrame.nativeDepth]

/-- The actual head lookup returns the same lowered certificate, with all
filters bounded simultaneously. No new domain query is chosen here. -/
theorem OriginalRichFrame.lookupHead_allDepth
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (tail : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (member : need ∈ needs) :
    ∃ resultSupport, ∃ result : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (resultSupport : Profile need.rank) footprint,
      footprint.Available available ∧ need.profile.HasType resultSupport ∧
      Related env U registry target x y (A.subst σ) need.profile resultSupport ∧
      ∀ current, result.nativeDepth current ≤
        (OriginalRichFrame.bind tail domain certificate resources typed arguments needs bounded covered).nativeDepth current := by
  have bound := bounded need member
  have included := covered need member
  simp only [Need.atGrade, dif_pos bound] at included
  have selected : Related env U registry target x y (A.subst σ) (raiseProfile n bound need.profile) support :=
    Related.of_singletons (fun atom hm => arguments.singleton_of_mem (included atom hm))
  refine ⟨_, certificate.lower need.rank bound, resources,
    lowerProfile.hasType bound ?_, lowerProfile.related bound henv formed selected, ?_⟩
  · cases n with
    | zero => exact fun atom present => typed atom (included atom present)
    | succ n => exact ⟨fun atom present => typed.1 atom (included atom present), typed.2.1,
        fun atom present => typed.2.2 atom (included atom present)⟩
  · intro current
    simp only [RichCert.nativeDepth_lower, OriginalRichFrame.nativeDepth,
      OriginalRichFrame.bind, RawOriginalRichFrame.nativeDepth]
    exact Nat.le_max_left _ _

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource

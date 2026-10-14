import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTelescope
import Lean4Lean.Theory.Typing.PrefixUnfolding.Abstraction
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSubstitution

/-! # Computing residual telescope erasures from erased inputs

Typed supply commutes with erasure. Peeling a typed residual type then recovers
its exact erased annotations and final body, without choosing original argument
representatives or using a family-conversion guard.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature

namespace ProofShape
/-- Supply raw arguments through a literal erased Pi telescope. -/
def supplyType : List ProofShape → ProofShape → Option ProofShape
  | [], type => some type
  | arg :: args, .forallE _ body => supplyType args (body.inst arg)
  | _ :: _, _ => none

/-- Peel a fixed number of raw Pi binders, retaining their annotations. -/
def takeForalls : Nat → ProofShape → Option (List ProofShape × ProofShape)
  | 0, type => some ([], type)
  | count + 1, .forallE A B => do
    let (domains, body) ← takeForalls count B
    return (A :: domains, body)
  | _ + 1, _ => none

/-- Compute the residual telescope directly from a raw initial type and prefix. -/
def residualTelescope (count : Nat) (args : List ProofShape) (type : ProofShape) :
    Option (List ProofShape × ProofShape) := do
  let residual ← supplyType args type
  takeForalls count residual
end ProofShape

variable [Params]

/-- Supplying a typed prefix is computed exactly by raw supply on the erased
initial type and argument list. No comparison of the arguments is required. -/
theorem proofErase_supplyType (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ fn type)
    (ht : VExpr.WF env univs Γ (mkApps fn args))
    (hg : RecursorData.supplyType args type = some residual) :
    ProofShape.supplyType (args.map (proofErase Γ)) (proofErase Γ type) =
      some (proofErase Γ residual) := by
  induction args generalizing fn type with
  | nil => cases hg; rfl
  | cons arg args ih =>
    cases type <;> try contradiction
    rename_i A B
    obtain ⟨u, hPi⟩ := hf.isType henv.ordered hΓ
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hPi.forallE_inv henv.ordered
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    have hfa : VExpr.WF env univs Γ (.app fn arg) :=
      VExpr.WF.of_mkApps henv.orderedStrong hΓ (f := .app fn arg) ht
    obtain ⟨A', B', hf', ha⟩ := hfa.app_inv henv.orderedStrong hΓ
    obtain ⟨⟨_, hdom⟩, _, _⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
    have harg := ha.defeqU_r henv hΓ ⟨_, hdom.symm⟩
    have hnext := ih (hf.app harg) ht hg
    rw [show proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
      if_neg (not_isProof_of_sort hΓ hPi)]
    simpa only [List.map_cons, ProofShape.supplyType,
      proofErase_instN hΓA harg Ctx.InstN.zero hB] using hnext

/-- Peeling a typed type recovers exactly the erased residual domains and body,
with each body interpreted in the corresponding original extended context. -/
theorem proofErase_takeForalls (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.IsType univs Γ type)
    (hg : VExpr.takeForalls count type = some (domains, body)) :
    ProofShape.takeForalls count (proofErase Γ type) =
      some (proofEraseDomains Γ domains, proofErase (domains.reverse ++ Γ) body) := by
  induction count generalizing Γ type domains body with
  | zero => cases hg; rfl
  | succ count ih =>
    cases type <;> try contradiction
    rename_i A B
    simp only [VExpr.takeForalls, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨⟨ds, tail⟩, htake, he⟩ := hg
    cases he
    obtain ⟨u, hPi⟩ := ht
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hPi.forallE_inv henv.ordered
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    rw [show proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
      if_neg (not_isProof_of_sort hΓ hPi)]
    simp only [ProofShape.takeForalls, ih hΓA ⟨w, hB⟩ htake,
      bind, Option.bind_some, pure, proofEraseDomains, List.reverse_cons,
      List.append_assoc, List.singleton_append]

/-- The actual generator's residual telescope is determined by its erased
arguments and the fixed closed recursor type, without a family guard or check. -/
theorem proofErase_singleton_prefix_telescope (hΓ : OnCtx Γ (env.IsType univs))
    (H : RecursorRegistered env data) (hw : ∀ l ∈ levels, l.WF univs)
    (hrec : data.recursorType = some recType)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args)) :
    ProofShape.residualTelescope (data.majorOffset + 1 - args.length)
      (args.map (proofErase Γ)) (proofErase [] (recType.instL levels)) =
      some (proofEraseDomains Γ program.domains,
        proofErase (program.domains.reverse ++ Γ) program.result) := by
  unfold RecursorData.singletonUnfolding at hg
  dsimp only at hg
  split at hg <;> try contradiction
  rename_i hguard
  simp at hguard
  have hlen : levels.length = data.uvars := hguard.1
  simp only [bind, Option.bind_eq_some_iff] at hg
  obtain ⟨recType', htype, residual, hsupply, ⟨domains, result⟩, htake,
    ⟨constructor, fields⟩, _, equation, _, body, _, hg⟩ := hg
  cases Option.some.inj (htype.symm.trans hrec)
  split at hg <;> try contradiction
  cases hg
  have hf : env.HasType univs Γ (.const data.name levels) (recType.instL levels) :=
    .const (H.recursorType htype) hw hlen
  have hf₀ : env.HasType univs [] (.const data.name levels) (recType.instL levels) :=
    .const (H.recursorType htype) hw hlen
  obtain ⟨u, htype₀⟩ := hf₀.isType henv.ordered (by trivial)
  have hc := proofErase_closed_context ((H.recursorType_closed henv htype).instL)
    htype₀ hΓ
  have hs := proofErase_supplyType hΓ hf ht hsupply
  rw [hc] at hs
  have hr := (hf.supply henv hΓ ht hsupply).isType henv.ordered hΓ
  exact (show _ = _ from by
    simp only [ProofShape.residualTelescope, hs, bind, Option.bind_some]
    exact proofErase_takeForalls hΓ hr htake)

/-- Equal erased prefixes yield identical erased residual domains and results,
even in unrelated well-formed contexts. No original argument conversion or
singleton family comparison is assumed. -/
theorem proofErase_singleton_prefix_telescope_congr
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (H : RecursorRegistered env data) (hw : ∀ l ∈ levels, l.WF univs)
    (hrec : data.recursorType = some recType)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (hg' : data.singletonUnfolding env univs levels args' = some program')
    (ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args))
    (ht' : VExpr.WF env univs Γ' (mkApps (.const data.name levels) args'))
    (ha : args.map (proofErase Γ) = args'.map (proofErase Γ')) :
    proofEraseDomains Γ program.domains = proofEraseDomains Γ' program'.domains ∧
      proofErase (program.domains.reverse ++ Γ) program.result =
        proofErase (program'.domains.reverse ++ Γ') program'.result := by
  have hlen : args.length = args'.length := by
    simpa only [List.length_map] using congrArg List.length ha
  have h₁ := proofErase_singleton_prefix_telescope hΓ H hw hrec hg ht
  have h₂ := proofErase_singleton_prefix_telescope hΓ' H hw hrec hg' ht'
  rw [ha, hlen] at h₁
  exact Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))

end Lean4Lean.VEnv.Strengthening

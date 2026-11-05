import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLowerTypeHistory

/-! # Constructor payloads beneath temporary control binders

Only the family type keeps a lower history. Fields remain arbitrary and may
depend on every temporary control. Native output ancestry uses the computed
header theorem at the current context and then descends the type computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open ProofShape.PiOriginObservation (FixedTail)
variable [Params] {D : PureObservation.Definitions}

/-- A saturated one-parameter constructor whose literal family type has a
lower positive history. The fields need no native certificates or lower-scope
restriction; ordinary term typing is supplied only when interpreting recovery. -/
def ConstructorTypePayload (D : PureObservation.Definitions) (Γ : List VExpr)
    (r : Name) (info : VProjectionInfo) (origin : ProofShape)
    (n : Nat) (Δ : List ProofShape) (source : ProofShape) : Prop :=
  ∃ p fields, source = ProofShape.mkApps (.const info.ctorName []) (p :: fields) ∧
    fields.length = info.numFields ∧ LowerTypeHistory D Γ origin n Δ (.app (.const r []) p)

/-- The payload has its registered constructor head even when its fields
contain arbitrary control expressions. -/
theorem ConstructorTypePayload.head
    (H : ConstructorTypePayload D Γ r info origin n Δ source) :
    source.constHead = some info.ctorName := by
  obtain ⟨_, _, rfl, _, _⟩ := H
  exact constHead_mkApps _ _

/-- Ordinary substitution changes all dependent fields and fixes the lower
family history. No native recovery of the substituted controls is required. -/
theorem ConstructorTypePayload.substitute
    (H : ConstructorTypePayload D Γ r info origin n Δ source)
    (W : ContextSubstitution Δ Δ' σ) (HT : FixedTail n m σ) :
    ConstructorTypePayload D Γ r info origin m Δ' (source.subst σ) := by
  obtain ⟨p, fields, rfl, hf, HP⟩ := H
  refine ⟨p.subst σ, fields.map (·.subst σ), ?_, by simpa using hf, ?_⟩
  · simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons]
  · exact HP.substitute W HT

/-- Every native type of a typed payload inherits its lower family history,
even when fields mention temporary controls and native conversions occur at
every constructor application. No exact argument recovery is assumed. -/
theorem ConstructorTypePayload.native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (H : ConstructorTypePayload D Γ r info origin n Δ source)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ source out) :
    LowerTypeHistory D Γ origin n Δ out := by
  cases EΓ
  obtain ⟨p, fields, Es, hf, HP⟩ := H
  obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv (Ee.trans Es)
  cases args with
  | nil => cases Eargs
  | cons a args =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj Eargs
    have hf' : args.length = info.numFields := by simpa using hf
    rw [Es] at RN
    have R := registered_computed_header_raw_origin heq hs hΓ' hi hx HH
      (args := [a]) (by simpa using hp.symm) hf' ht
      (List.Forall₂.rfl (fun _ _ => .refl)) (List.Forall₂.rfl (fun _ _ => .refl)) RN
    exact HP.compute heq hs hΓ hΓ' W R

/-- Complete beta computation preserves the payload and its historical
family type. Beta cannot replace the constructor head; all parameter and field
reductions are recovered by constant-spine inversion. -/
theorem ConstructorTypePayload.beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : ConstructorTypePayload D Γ r info origin n (proofEraseCtx Γ') source)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (R : BetaRed source out) : ConstructorTypePayload D Γ r info origin n (proofEraseCtx Γ') out := by
  obtain ⟨p, fields, rfl, hf, HP⟩ := H
  obtain ⟨args, rfl, HR⟩ := R.const_spine
  cases HR with
  | cons RP RF =>
    exact ⟨_, _, rfl, RF.length_eq.symm.trans hf, HP.compute heq hs hΓ hΓ' W (.app .refl (.beta RP))⟩

/-- A constructor state at the original context supplies the payload
predicate directly. Positivity follows from native recovery of its retained
constructor, so it is not an additional registration assumption. -/
theorem ConstructorFamilyState.type_payload
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (H : ConstructorFamilyState D Γ r info origin source) :
    ConstructorTypePayload D Γ r info origin 0 (proofEraseCtx Γ) source := by
  obtain ⟨e, T, p, fields, ht, Ee, Es, hf, RO⟩ := H
  have RN := computed_constructor_image_native (Target := ErasedStaticStructureEtaExpansionUnion D)
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hi hx
    (images := p :: fields) (by simp [hp, hf, Nat.add_comm]) ht
    (show ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (ProofShape.mkApps (.const info.ctorName []) (p :: fields)) from
      by rw [Ee, Es]; exact .refl)
  have RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (.app (.const r []) p) := by
    rw [← Es, ← Ee] at RN
    simpa only [hp, List.take_succ_cons, List.take_zero, ProofShape.mkApps] using RN
  exact ⟨p, fields, Es, hf, LowerTypeHistory.of_native heq hs hΓ ht RN' RO⟩

end Lean4Lean.VEnv.Strengthening

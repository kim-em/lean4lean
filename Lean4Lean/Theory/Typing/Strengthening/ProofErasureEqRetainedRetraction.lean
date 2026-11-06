import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqUnusedEmbedding

/-! # Restore completion through an unused retained expression

Read the actual lambda paths while lifting a constructed reverse embedding.
An exact round trip for the retained expression supplies the annotation
identities needed at each binder. The execution uses the whole source, while
the round trip tracks only the bounded target prefix and retained annotations.
Wrapper argument vectors remain unrestricted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- The annotations around the bounded Eq prefix do not use the outer top
binder. The shell contains the recorded lambdas without their argument vectors;
extra arguments of the inner Eq spine beyond the target arity are also excluded. -/
def UnusedRetainedEqPrefix (shell : ProofShape → ProofShape) (slots : Nat)
    (ls : List VLevel) (args : List ProofShape) : Prop :=
  ∃ lower : ProofShape, shell (ProofShape.mkApps (.const ``Eq.rec ls) (args.take slots)) = lower.liftN 1

private theorem lambda_round_trip
    (E : ((ProofShape.lam A body).subst τ).subst κ = ProofShape.lam A body) :
    (A.subst τ).subst κ = A ∧ (body.subst τ.lift).subst κ.lift = body := by
  simp only [ProofShape.subst] at E
  exact ProofShape.lam.inj E

/-- Instantiation and reinsertion restore every raw expression which is
literally lifted across the consumed top binder. No typing is required. -/
theorem unused_top_round_trip {e lower : ProofShape} (E : e = lower.liftN 1) (x : ProofShape) :
    (e.subst (ProofShape.Subst.one x)).subst (fun i => .bvar (liftVar 1 i 0)) = e := by
  rw [E]
  simp only [ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id, subst_bvar_liftN]

variable [Params]

/-- The actual retained prefix together with its annotation-only shell.
The executable plug keeps every recorded argument; the shell retains the same
lambdas and domains but omits those arguments. No independence is assumed. -/
inductive PiInertRetainedShellCount (D : Definitions) :
    List ProofShape → List ProofShape → (ProofShape → ProofShape) →
      (ProofShape → ProofShape) → Nat → Prop where
  | refl : PiInertRetainedShellCount D Δ Δ id id 0
  | retained : DomainSort Δ A u → ScopedComputeCount (PiInertStage D n) cd Δ A A' →
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id →
      PiInertRetainedShellCount D Δ Θ plug shell depth →
      PiInertRetainedShellCount D (A :: Δ) Θ
        (fun e => plug (ProofShape.mkApps (.lam A' e) args))
        (fun e => shell (.lam A' e)) (depth+1)

/-- Every actual counted prefix determines an annotation-only shell with
the same original contexts, annotation paths and depth. -/
theorem PiInertRetainedPrefixCount.with_shell
    (H : PiInertRetainedPrefixCount D Δ Θ plug depth) :
    ∃ shell, PiInertRetainedShellCount D Δ Θ plug shell depth := by
  induction H with
  | refl => exact ⟨id, .refl⟩
  | retained SD RD WI _ ih =>
    obtain ⟨shell, HS⟩ := ih
    exact ⟨_, .retained SD RD WI HS⟩

/-- Forget the shell while retaining every actual application argument. -/
theorem PiInertRetainedShellCount.forget
    (H : PiInertRetainedShellCount D Δ Θ plug shell depth) :
    PiInertRetainedPrefixCount D Δ Θ plug depth := by
  induction H with
  | refl => exact .refl
  | retained SD RD WI _ ih => exact .retained SD RD WI ih

/-- Refocus every nonempty retained prefix while restoring a separately
tracked payload. The recorded annotation paths are replayed in the restored
context, and each annotation identity follows from the supplied shell round
trip. Actual wrapper arguments need no round-trip identity. No semantic target
assignment or proof-valued domain is assumed. The actual whole-source minimum
loses the application frame as before. -/
theorem PiInertRetainedShellCount.focus_retraction
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertRetainedShellCount D Δ Θ plug shell depth) (hd : 0 < depth)
    (HH : PiInertContextHistory D Θ Υ) (WK : ContextEmbedding Ξ Υ κ)
    (ER : ((shell tracked).subst τ).subst κ = shell tracked)
    (HM : PiInertFrameMinimum D Ω out Ξ (ProofShape.mkApps ((plug e).subst τ) pending) cost frames) :
    ∃ Λ Υ' smaller, PiInertContextHistory D Δ Υ' ∧
      ContextEmbedding Λ Υ' (κ.liftN depth) ∧
      (tracked.subst (τ.liftN depth)).subst (κ.liftN depth) = tracked ∧
      smaller ≤ cost ∧
      PiInertFrameMinimum D Ω out Λ (e.subst (τ.liftN depth)) smaller (frames+depth) := by
  induction H generalizing e tracked Ξ Υ τ κ pending cost frames with
  | refl => omega
  | @retained Δ A u n cd A' Θ plug shell depth args SD RD WI HP ih =>
    by_cases hz : depth = 0
    · subst depth
      cases HP with
      | refl =>
        simp only [id_eq] at ER
        obtain ⟨EA, EB⟩ := lambda_round_trip ER
        have WB := WK.binder (A := A'.subst τ)
        rw [EA] at WB
        simp only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, ← ProofShape.mkApps_append] at HM
        obtain ⟨smaller, hsmall, HMbody⟩ := HM.lambda_body heq hs
        exact ⟨_, _, smaller, .step (.head RD.forget) HH.tail, WB, EB, hsmall, HMbody⟩
    · obtain ⟨Λ, Υ', smaller, HHinner, WKinner, ERinner, hsmall, HMinner⟩ :=
        ih (by omega) HH WK ER HM
      obtain ⟨EA, EB⟩ := lambda_round_trip ERinner
      have WB := WKinner.binder (A := A'.subst (τ.liftN depth))
      rw [EA] at WB
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at HMinner
      obtain ⟨last, hlast, HMbody⟩ := HMinner.lambda_body heq hs
      refine ⟨_, _, last, .step (.head RD.forget) HHinner.tail, WB, EB,
        Nat.le_trans hlast hsmall, ?_⟩
      simpa only [Nat.add_assoc, ProofShape.Subst.liftN] using HMbody

/-- An unused annotation shell around the bounded prefix permits non-proof
consumption at its outer scope. Reinsert the actual domain, refocus the existing whole-source
minimum, replay its annotations and pull the bounded completion back. The
returned minimum has strictly fewer frames than the removed prefix plus
application, even when its primitive count is unchanged. -/
theorem EqTargetPrefixEmbedding.consume_unused_retained
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HR : PiInertRetainedShellCount D Δ (A :: Ξ) plug shell depth) (hd : 0 < depth)
    (SD : DomainSort Ξ A u)
    (HU : UnusedRetainedEqPrefix shell original.length ls args)
    (HM : PiInertFrameMinimum D Ω out Ξ
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec ls) args)).subst (ProofShape.Subst.one x)) pending)
      cost frames) :
    ∃ Λ smaller, smaller ≤ cost ∧
      PiInertFrameMinimum D Ω out Λ
        (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst ((ProofShape.Subst.one x).liftN depth))))
        smaller (frames+depth) ∧
      EqTargetPrefixEmbedding Γ v w original Λ
        (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst ((ProofShape.Subst.one x).liftN depth)))) := by
  obtain ⟨lower, EL⟩ := HU
  have WK : ContextEmbedding Ξ (A :: Ξ) (fun i => .bvar (liftVar 1 i 0)) :=
    ContextEmbedding.insert .identity SD
  obtain ⟨Λ, Υ, smaller, HH, WB, ER, hsmall, Hbody⟩ :=
    HR.focus_retraction heq hs hd .refl WK (unused_top_round_trip EL x) HM
  have HPprefix := HP.prefix_congr (args' := args.take original.length)
    (by simp only [List.take_take, Nat.min_self])
  have HPcontext := HPprefix.context_history heq hs hΓ HH
  have HPbody := (ER.symm ▸ HPcontext).pullback WB
  simp only [ProofShape.subst_mkApps, ProofShape.subst] at HPbody Hbody
  refine ⟨Λ, smaller, hsmall, Hbody, HPbody.prefix_congr ?_⟩
  simp only [← List.map_take, List.take_take, Nat.min_self]

end Lean4Lean.VEnv.Strengthening

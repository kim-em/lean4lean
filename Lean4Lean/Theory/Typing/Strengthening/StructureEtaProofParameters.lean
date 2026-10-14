import Lean4Lean.Theory.Typing.Strengthening.StructureEtaParameterReduction

/-! # Completing structure eta when its parameters are proofs

Typing identifies the exposed constructor's parameters with the eta instance.
When the original parameters are proofs, these conversions are already ordinary
normal comparisons by proof irrelevance. Exact field joins then finish every
root eta/computation overlap, including neutral and constructor-exposing majors.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

private abbrev actualD : Definitions :=
  RegisteredStructure.definitions (Definitions.ofEnv env univs henv)

/-- Pairwise conversion with proof-valued left endpoints is ordinary normal
comparison; no computational or eta certificate for the conversion is needed. -/
theorem normal_parameters_of_proofs (hΓ : OnCtx Γ (env.IsType univs))
    (HE : List.Forall₂ (env.IsDefEqU univs Γ) xs ys)
    (hp : ∀ x ∈ xs, IsProof Γ x) : List.Forall₂ (NormalEq Γ) xs ys := by
  induction HE with
  | nil => exact .nil
  | cons H _ ih =>
    obtain ⟨P, hx, hP⟩ := hp _ (List.mem_cons_self ..)
    exact .cons (.proofIrrel hP hx (H.of_l henv hΓ hx).hasType.2)
      (ih (fun x hx => hp x (List.mem_cons_of_mem _ hx)))

/-- Every structure eta root whose actual parameters are proofs admits a
symmetric phase after arbitrary finite computation. This includes all majors,
all field types, and constructor exposure at converted parameters/universes.
It assumes neither canonical Eq nor a strengthening front. -/
theorem proof_parameters_structure_eta_compute_phase
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : params.length = info.nparams)
    (hx : info.nindices = 0)
    (hm : env.HasType univs Γ major (mkApps (.const family levels) params))
    (hc : env.HasType univs Γ (structExpand family info levels params major)
      (mkApps (.const family levels) params))
    (hproof : ∀ p ∈ params, IsProof Γ p)
    (R : PrefixCompute actualD Γ (structExpand family info levels params major) out) :
    PrefixEtaJoin actualD Γ major out := by
  classical
  by_cases hn : ∃ ls args, PrefixCompute actualD Γ major (mkApps (.const info.ctorName ls) args)
  · obtain ⟨ls, args, HM⟩ := hn
    have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
    have htCtor := (HM.simAt hs hΓ _ hm).hasType.2
    have hlen := (projection_major_family henv hΓ hi (henv.projectionRigid hi) htCtor).2
    obtain ⟨outArgs, rfl, HA⟩ := R.rigid_spine_paths (henv.projectionCtorRigid hi)
      (fun _ _ => RegisteredStructure.definitions_ofEnv_no_rigid (henv.projectionCtorRigid hi))
    have hlenOut : outArgs.length = info.nparams + info.numFields := by
      simpa [hp] using HA.length_eq.symm
    have hpc : (args.take info.nparams).length = info.nparams := by simp [hlen]
    have hfc : (args.drop info.nparams).length = info.numFields := by simp [hlen]
    have hpo : (outArgs.take info.nparams).length = info.nparams := by simp [hlenOut]
    have hfo : (outArgs.drop info.nparams).length = info.numFields := by simp [hlenOut]
    have HC : List.Forall₂ (env.IsDefEqU univs Γ) (args.take info.nparams) params :=
      constructor_parameters_defeq hΓ hi hpc hp hfc (by simp)
        (by simpa only [List.take_append_drop] using htCtor) hc
    have HO : List.Forall₂ (env.IsDefEqU univs Γ) params (outArgs.take info.nparams) :=
      constructor_parameters_defeq hΓ hi hp hpo (by simp) hfo hc
        (by simpa only [List.take_append_drop] using (R.simAt hs hΓ _ hc).hasType.2)
    have NC := normal_parameters_of_proofs hΓ (HC.flip.imp (fun _ _ (H : env.IsDefEqU univs Γ _ _) => H.symm)) hproof
    have NO := normal_parameters_of_proofs hΓ HO hproof
    have NC' : List.Forall₂ (NormalEq Γ) (args.take info.nparams) params :=
      NC.flip.imp (fun _ _ H => NormalEq.symm hΓ H)
    have N : List.Forall₂ (NormalEq Γ) (args.take info.nparams) (outArgs.take info.nparams) :=
      NC'.trans (fun x y z (H1 : NormalEq Γ x y) (H2 : NormalEq Γ y z) => H1.trans hΓ H2) NO
    have HP : List.Forall₂ (PrefixEtaJoin actualD Γ) (args.take info.nparams) (outArgs.take info.nparams) :=
      N.imp (fun _ _ H => .of_eta (EtaNormal.normal H).join)
    have H := structure_eta_compute_parameter_phase (outFields := outArgs.drop info.nparams) hcon hΓ hi hp hpc hfc hpo hm hc
      (by simpa only [List.take_append_drop] using HM)
      (by simpa only [List.take_append_drop] using R) HP
    simpa only [List.take_append_drop] using H
  · exact neutral_eta_compute_symmetric_phase hcon hΓ hi hp hx hm hc
      (fun ls args HM => hn ⟨ls, args, HM⟩) R

end Lean4Lean.VEnv.Strengthening.PureObservation

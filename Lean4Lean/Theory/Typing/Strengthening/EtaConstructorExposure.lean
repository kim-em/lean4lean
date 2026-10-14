import Lean4Lean.Theory.Typing.Strengthening.EtaExpansionHeads
import Lean4Lean.Theory.Typing.Strengthening.EtaStructureExchange

/-! # Constructor exposure through finite typed eta expansion

A constant spine exposed by eta was either already present, with expanded
arguments, or was created by a registered structure expansion. In the latter
case every final field expands from a projection of the original source, even
when many eta steps preceded and followed the constructor creation.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Information retained when structure eta creates a constructor head.
Parameters in the final spine may differ from the source's typing parameters;
only the field suffix must expand from actual projections of the source. -/
def EtaCreatedConstructor (Γ : List VExpr) (e : VExpr) (name : Name)
    (levels : List VLevel) (args : List VExpr) : Prop :=
  ∃ family info params, env.projections family info ∧ info.ctorName = name ∧
    params.length = info.nparams ∧ info.nindices = 0 ∧
    env.HasType univs Γ e (mkApps (.const family levels) params) ∧
    ((info.resultLevel.inst levels).IsNeverZero ∨ StructureReplay.ProofFields env univs info levels) ∧
    args.length = info.nparams + info.numFields ∧
    List.Forall₂ (TypedEtaExpansion Γ)
      ((List.range info.numFields).map (fun i => .proj family i e)) (args.drop info.nparams)

/-- All finite eta paths ending at a constant spine admit the two alternatives.
No normalization, front, or canonical-Eq premise is used. -/
theorem TypedEtaExpansion.constructor_exposure (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedEtaExpansion Γ e (mkApps (.const name levels) args))
    (ht : env.HasType univs Γ e T) :
    (∃ args', e = mkApps (.const name levels) args' ∧
      List.Forall₂ (TypedEtaExpansion Γ) args' args) ∨
    EtaCreatedConstructor Γ e name levels args := by
  generalize hout : mkApps (.const name levels) args = target at R
  induction R generalizing name levels args T with
  | refl => exact .inl ⟨args, hout.symm, List.Forall₂.rfl (fun _ _ => .refl)⟩
  | @structEta family info Γ major ls ps hi hp hx hm hc =>
    have hh := congrArg getAppFn hout
    simp only [getAppFn_mkApps, getAppFn, VExpr.const.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    have ha := congrArg getAppArgs hout
    simp only [getAppArgs_mkApps, getAppArgs, List.nil_append] at ha
    subst args
    refine .inr ⟨family, info, ps, hi, rfl, hp, hx, hm,
      (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc, by simp [hp], ?_⟩
    rw [← hp, List.drop_left]
    exact List.Forall₂.rfl (fun _ _ => .refl)
  | @trans Γ a b c R1 R2 ih1 ih2 =>
    rcases ih2 hΓ (R1.simAt hΓ _ ht).hasType.2 hout with ⟨args1, hb, H1⟩ | H2
    · rcases ih1 hΓ ht hb.symm with ⟨args0, ha, H0⟩ | H0
      · exact .inl ⟨args0, ha, H0.trans (fun _ _ _ h h' => h.trans h') H1⟩
      · obtain ⟨family, info, ps, hi, hc, hp, hx, hm, hz, hlen, HF⟩ := H0
        exact .inr ⟨family, info, ps, hi, hc, hp, hx, hm, hz,
          H1.length_eq.symm.trans hlen,
          HF.trans (fun _ _ _ h h' => h.trans h') (List.forall₂_drop H1 _)⟩
    · obtain ⟨family, info, ps, hi, hc, hp, hx, hm, hz, hlen, HF⟩ := H2
      refine .inr ⟨family, info, ps, hi, hc, hp, hx,
        hm.defeqU_l henv hΓ ⟨_, (R1.simAt hΓ _ ht).symm⟩, hz, hlen, ?_⟩
      have HP : List.Forall₂ (TypedEtaExpansion Γ)
          ((List.range info.numFields).map (fun i => .proj family i a))
          ((List.range info.numFields).map (fun i => .proj family i b)) := by
        apply List.forall₂_of_getElem (by simp)
        intro i hi hi'
        simpa only [List.getElem_map, List.getElem_range] using
          (TypedEtaExpansion.proj (s := family) (i := i) R1)
      exact HP.trans (fun _ _ _ h h' => h.trans h') HF
  | @app Γ f f' a a' Rf Ra ihf iha =>
    obtain ⟨args0, rfl, hf'⟩ := RigidHead.const.mkApps_eq_app hout
    obtain ⟨A, B, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨args', hf0, HA⟩ := (hf' ▸ Rf).const_spine_source hΓ (.inr ⟨A, B, hf⟩)
    refine .inl ⟨args' ++ [a], ?_, HA.append' (.cons Ra .nil)⟩
    rw [mkApps_snoc, ← hf0]
  | lam | forallE | proj | funEta =>
    have hh := congrArg getAppFn hout
    simp only [getAppFn_mkApps, getAppFn] at hh
    cases hh

/-- Any finite eta path before a saturated constructor projection exchanges
with that projection. An existing constructor projects first; an eta-created
constructor needs no computation and retains only its selected field path. -/
theorem eta_projection_compute (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedEtaExpansion Γ major (mkApps (.const info.ctorName levels) args))
    (hm : env.HasType univs Γ major T) (hi : env.projections family info)
    (hlen : args.length = info.nparams + info.numFields)
    (hg : args[info.nparams + index]? = some field) :
    ∃ out, PrefixCompute D Γ (.proj family index major) out ∧
      TypedEtaExpansion Γ out field := by
  rcases R.constructor_exposure hΓ hm with ⟨args0, rfl, HA⟩ | H
  · obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.1 hg
    have hj0 : info.nparams + index < args0.length := by rw [HA.length_eq]; exact hj
    refine ⟨args0[info.nparams + index], .base (.base (.projIota hi
      (HA.length_eq.trans hlen) (List.getElem?_eq_getElem hj0))), ?_⟩
    simpa only [he] using HA.getElem_of (info.nparams + index) hj0 hj
  · obtain ⟨family', info', ps, hi', hc, _, _, _, _, hlen', HF⟩ := H
    obtain ⟨rfl, rfl⟩ := henv.ordered.projectionConstructor_family hi' hi hc
    have hp : (args.take info'.nparams).length = info'.nparams := by simp [hlen]
    have hg' : (args.take info'.nparams ++ args.drop info'.nparams)[info'.nparams + index]? =
        some field := by simpa only [List.take_append_drop] using hg
    exact ⟨_, .refl, projection_eta_exchange HF hp hg'⟩

end Lean4Lean.VEnv.Strengthening.PureObservation

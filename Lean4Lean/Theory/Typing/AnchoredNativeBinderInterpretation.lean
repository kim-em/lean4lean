import Lean4Lean.Theory.Typing.AnchoredNativeLambdaAlignment
import Lean4Lean.Theory.Typing.AnchoredFunctionIntroduction

/-! The native binder consumes its actual recursive applications at the
stored anchor. Literal Pi code transports their assigned codomain to the
caller's argument before semantic symmetry and transitivity join them. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- A literal Pi row compares two actual admitted arguments at the base
world, even when its chosen canonical display has private proof slots. -/
theorem TypeRelated.literalPiArguments
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {A B prototypeDomain prototypeBody : VExpr} {domain : Profile n}
    {rows : List (Key n × Profile n)} {key : Key n} {result : Profile n} {x y : VExpr}
    (whole : TypeRelated env U registry Γ (.forallE A B) (.forallE A B)
      (.pi prototypeDomain prototypeBody domain rows))
    (member : (key, result) ∈ rows)
    (admitted : Admitted env U registry Γ key x y) :
    TypeRelated env U registry Γ (B.inst x) (B.inst y) result := by
  have atBase := whole Γ .refl (.refl hΓ)
  simp only [lift'_refl, Profile.rename_refl] at atBase
  obtain ⟨display⟩ := atBase (.pi prototypeDomain prototypeBody domain rows)
    (List.mem_singleton_self _)
  have insertion := display.leftExposure.insertion henv
  have args := insertion.admitted henv admitted
  have row := display.rowBodies key result member display.context .refl
    (.refl (display.leftExposure.targetWF henv))
    (x.lift' display.map) (y.lift' display.map) (by
      simpa only [Lift.comp, Admitted] using args)
  have leftBody := display.leftExposure.literalPi_components |>.2
  have bodyCode : TypeRelated env U registry display.context
      ((B.inst x).lift' display.map) ((B.inst y).lift' display.map)
      (result.rename display.map) := by
    simpa only [TypeRelated, Lift.comp, lift'_depth_zero (l := Lift.refl.cons) rfl,
      leftBody, lift'_inst_hi] using row.1
  exact insertion.codeBack henv hscoped bodyCode

/-- The strict child call returns both applications relative to one fixed
anchor application. The enclosing binder needs no type evidence obtained by
reinterpreting a synthesized source typing derivation. -/
theorem Related.nativeBinder
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {left right origin A B prototypeDomain prototypeBody : VExpr}
    {key : Key n} {output : Atom n} {domain result guardSupport : Profile n}
    {rows : List (Key n × Profile n)}
    (hA : env.IsType U Γ A) (hB : env.IsType U (A :: Γ) B)
    (whole : TypeRelated env U registry Γ (.forallE A B) (.forallE A B)
      (.pi prototypeDomain prototypeBody domain rows))
    (member : (key, result) ∈ rows)
    (resultTyped : (Profile.singleton output).HasType result)
    (resultWF : result.WF)
    (inputTyped : key.input.HasType guardSupport)
    (guardFormed : guardSupport.HasType (.sort true))
    (path : TypeConversion env U Γ key.domain A)
    (bridge : TypeRelated env U registry Γ key.domain A guardSupport)
    (seed : Admitted env U registry Γ key key.anchor key.anchor)
    (children : ∀ Δ ρ, FutureInsertion env U Γ Δ ρ → ∀ z,
      Admitted env U registry Δ (key.rename ρ) z z →
      Related env U registry Δ (origin.lift' ρ) (.app (left.lift' ρ) z)
        ((B.inst key.anchor).lift' ρ) (.singleton (output.rename ρ)) (result.rename ρ) ∧
      Related env U registry Δ (origin.lift' ρ) (.app (right.lift' ρ) z)
        ((B.inst key.anchor).lift' ρ) (.singleton (output.rename ρ)) (result.rename ρ)) :
    Related env U registry Γ left right (.forallE A B) (Profile.fn key output)
      (.pi A B guardSupport [(key, result)]) := by
  have row : ∀ Δ ρ, FutureInsertion env U Γ Δ ρ → ∀ x y,
      Admitted env U registry Δ (key.rename ρ) x y →
      TypeRelated env U registry Δ ((B.lift' ρ.cons).inst x)
        ((B.lift' ρ.cons).inst y) (result.rename ρ) := by
    intro Δ ρ future x y admitted
    have whole' := whole.future henv future
    have member' : (key.rename ρ, result.rename ρ) ∈
        rows.map (fun (k, r) => (k.rename ρ, r.rename ρ)) :=
      List.mem_map.mpr ⟨(key, result), member, rfl⟩
    exact TypeRelated.literalPiArguments henv hscoped (future.targetWF henv) whole' member' admitted
  let display := PiWitness.literal henv hΓ hA hB inputTyped guardFormed path bridge row
  have code := TypeRelated.literalPi henv hA hB inputTyped guardFormed path bridge row
  have typed : (Profile.fn key output).HasType (.pi A B guardSupport [(key, result)]) := by
    apply Profile.HasType.fn _ (List.mem_singleton_self _) resultTyped
    apply Profile.WF.pi_iff.mpr
    refine ⟨guardFormed, ?_⟩
    intro k r hm
    cases List.mem_singleton.mp hm
    exact ⟨inputTyped, resultWF⟩
  have behavior : FunctionBehavior env U registry (relations env U registry n)
      Γ left right (.forallE A B) key output (.pi A B guardSupport [(key, result)]) := by
    refine ⟨seed, A, B, guardSupport, [(key, result)], result,
      List.mem_singleton_self _, List.mem_singleton_self _, resultTyped, display, ?_⟩
    intro Δ ρ future x y admitted
    simp only [display, PiWitness.literal, Lift.refl_comp] at admitted ⊢
    change Admitted env U registry Δ (key.rename ρ) x y at admitted
    obtain ⟨ha, hp, ds, tp, formed, dc, ax, xy⟩ := admitted
    change Related env U registry Δ (key.rename ρ).anchor x
      (key.rename ρ).domain (key.rename ρ).input ds at ax
    change Related env U registry Δ x y
      (key.rename ρ).domain (key.rename ρ).input ds at xy
    have selfX : Admitted env U registry Δ (key.rename ρ) x x :=
      ⟨ha, hp.hasType.1, ds, tp, formed, dc, ax, xy.left_diagonal⟩
    have selfY : Admitted env U registry Δ (key.rename ρ) y y :=
      ⟨ha.trans hp, hp.hasType.2, ds, tp, formed, dc,
        ax.trans henv hscoped xy, (xy.symm henv).left_diagonal⟩
    have atX := children Δ ρ future x selfX
    have atY := children Δ ρ future y selfY
    have anchorX : Admitted env U registry Δ (key.rename ρ) (key.anchor.lift' ρ) x :=
      ⟨ha.hasType.1, ha, ds, tp, formed, dc, ax.left_diagonal, ax⟩
    have bodyBridge := row Δ ρ future (key.anchor.lift' ρ) x anchorX
    rw [← lift'_inst_hi] at bodyBridge
    have typed' : (Profile.singleton (output.rename ρ)).HasType (result.rename ρ) :=
      Profile.rename_hasType_iff.mpr resultTyped
    have leftX := atX.1.convert henv typed' bodyBridge
    have rightX := atX.2.convert henv typed' bodyBridge
    have leftY := atY.1.convert henv typed' bodyBridge
    have rightY := atY.2.convert henv typed' bodyBridge
    exact ⟨(leftX.symm henv).trans henv hscoped leftY,
      (rightX.symm henv).trans henv hscoped rightY,
      (leftX.symm henv).trans henv hscoped rightX⟩
  exact Related.function henv hscoped typed code behavior

end Lean4Lean.AnchoredSemantics

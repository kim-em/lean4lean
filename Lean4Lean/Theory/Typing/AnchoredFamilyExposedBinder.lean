import Lean4Lean.Theory.Typing.AnchoredNativeBinderInterpretation

/-! A finite family-plan binder can use an actual Pi exposure of its assigned
code. The assigned expression need not be a literal Pi or a literal suffix of
a declaration telescope. The recursive premises below are lower-rank child
interpretations, and are not stored semantic answers in the query grammar. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- Interpret one binder against the same selected Pi witness. The child is
interpreted in the witness's actual display context, then under an ordinary
future insertion. This deliberately does not assert that the display itself
is a future insertion: it can also contain a terminal context conversion.

Both recursive results compare the fixed anchored application with one actual
application. Their assigned type is the same exposed body at the fixed anchor,
so the witness's row capability supplies the required dependent conversion. -/
theorem FunctionBehavior.ofAnchoredChildren
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {left right assigned prototypeDomain prototypeBody : VExpr}
    {key : Key n} {output : Atom n} {domain result : Profile n}
    {rows : List (Key n × Profile n)} {support : Profile (n+1)}
    (member : AtomData.pi prototypeDomain prototypeBody domain rows ∈ support.atoms)
    (row : (key, result) ∈ rows)
    (resultTyped : (Profile.singleton output).HasType result)
    (seed : Admitted env U registry Γ key key.anchor key.anchor)
    (display : PiWitness env U registry (relations env U registry n)
      Γ assigned assigned prototypeDomain prototypeBody domain rows)
    (children : ∀ Δ ρ, FutureInsertion env U display.context Δ ρ → ∀ z,
      Admitted env U registry Δ (key.rename (display.map.comp ρ)) z z →
      Related env U registry Δ
        ((VExpr.app left key.anchor).lift' (display.map.comp ρ))
        (.app (left.lift' (display.map.comp ρ)) z)
        ((display.leftBody.inst (key.anchor.lift' display.map)).lift' ρ)
        (.singleton (output.rename (display.map.comp ρ)))
        (result.rename (display.map.comp ρ)) ∧
      Related env U registry Δ
        ((VExpr.app left key.anchor).lift' (display.map.comp ρ))
        (.app (right.lift' (display.map.comp ρ)) z)
        ((display.leftBody.inst (key.anchor.lift' display.map)).lift' ρ)
        (.singleton (output.rename (display.map.comp ρ)))
        (result.rename (display.map.comp ρ))) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right assigned key output support := by
  refine ⟨seed, prototypeDomain, prototypeBody, domain, rows, result,
    member, row, resultTyped, display, ?_⟩
  intro Δ ρ future x y admitted
  change Admitted env U registry Δ (key.rename (display.map.comp ρ)) x y at admitted
  obtain ⟨ha, hp, ds, tp, formed, dc, ax, xy⟩ := admitted
  change Related env U registry Δ (key.rename (display.map.comp ρ)).anchor x
    (key.rename (display.map.comp ρ)).domain
    (key.rename (display.map.comp ρ)).input ds at ax
  change Related env U registry Δ x y (key.rename (display.map.comp ρ)).domain
    (key.rename (display.map.comp ρ)).input ds at xy
  have selfX : Admitted env U registry Δ (key.rename (display.map.comp ρ)) x x :=
    ⟨ha, hp.hasType.1, ds, tp, formed, dc, ax, xy.left_diagonal⟩
  have selfY : Admitted env U registry Δ (key.rename (display.map.comp ρ)) y y :=
    ⟨ha.trans hp, hp.hasType.2, ds, tp, formed, dc,
      ax.trans henv hscoped xy, (xy.symm henv).left_diagonal⟩
  have atX := children Δ ρ future x selfX
  have atY := children Δ ρ future y selfY
  have anchorX : Admitted env U registry Δ (key.rename (display.map.comp ρ))
      (key.anchor.lift' (display.map.comp ρ)) x :=
    ⟨ha.hasType.1, ha, ds, tp, formed, dc, ax.left_diagonal, ax⟩
  have bodyBridge := (display.rowBodies key result row Δ ρ future
    (key.anchor.lift' (display.map.comp ρ)) x anchorX).1
  change TypeRelated env U registry Δ _ _ _ at bodyBridge
  rw [lift'_comp, ← lift'_inst_hi] at bodyBridge
  have typed' : (Profile.singleton (output.rename (display.map.comp ρ))).HasType
      (result.rename (display.map.comp ρ)) :=
    Profile.rename_hasType_iff.mpr resultTyped
  have leftX := atX.1.convert henv typed' bodyBridge
  have rightX := atX.2.convert henv typed' bodyBridge
  have leftY := atY.1.convert henv typed' bodyBridge
  have rightY := atY.2.convert henv typed' bodyBridge
  exact ⟨(leftX.symm henv).trans henv hscoped leftY,
    (rightX.symm henv).trans henv hscoped rightY,
    (leftX.symm henv).trans henv hscoped rightX⟩

/-- Select an actual Pi exposure from the already supplied assigned-code
capability and interpret the strict child of a finite family-plan binder.
Neither a source-literal Pi nor a normalized declaration telescope is assumed.
The child hypothesis must be established by the plan interpreter's lower-rank
induction; it is not an additional source constructor field. -/
theorem Related.familyBinderOfAssigned
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {left right assigned : VExpr} {key : Key n} {output : Atom n}
    {support : Profile (n+1)}
    (typed : (Profile.fn key output).HasType support)
    (code : TypeRelated env U registry Γ assigned assigned support)
    (seed : Admitted env U registry Γ key key.anchor key.anchor)
    (children : ∀ {A B : VExpr} {domain result : Profile n} {rows : List (Key n × Profile n)},
      (AtomData.pi A B domain rows ∈ support.atoms) →
      (key, result) ∈ rows → (Profile.singleton output).HasType result →
      ∀ display : PiWitness env U registry (relations env U registry n)
        Γ assigned assigned A B domain rows,
      ∀ Δ ρ, FutureInsertion env U display.context Δ ρ → ∀ z,
      Admitted env U registry Δ (key.rename (display.map.comp ρ)) z z →
      Related env U registry Δ
        ((VExpr.app left key.anchor).lift' (display.map.comp ρ))
        (.app (left.lift' (display.map.comp ρ)) z)
        ((display.leftBody.inst (key.anchor.lift' display.map)).lift' ρ)
        (.singleton (output.rename (display.map.comp ρ)))
        (result.rename (display.map.comp ρ)) ∧
      Related env U registry Δ
        ((VExpr.app left key.anchor).lift' (display.map.comp ρ))
        (.app (right.lift' (display.map.comp ρ)) z)
        ((display.leftBody.inst (key.anchor.lift' display.map)).lift' ρ)
        (.singleton (output.rename (display.map.comp ρ)))
        (result.rename (display.map.comp ρ))) :
    Related env U registry Γ left right assigned (Profile.fn key output) support := by
  obtain ⟨A, B, domain, rows, result, member, _, _, _, row, resultTyped⟩ :=
    typed.fn_inv (List.mem_singleton_self _)
  have baseCode := code Γ .refl (.refl hΓ) (.pi A B domain rows)
    (by simpa only [Profile.rename_refl] using member)
  simp only [lift'_refl, CodeAtom] at baseCode
  obtain ⟨display⟩ := baseCode
  exact Related.function henv hscoped typed code
    (FunctionBehavior.ofAnchoredChildren henv hscoped member row resultTyped seed display
      (children member row resultTyped display))

end Lean4Lean.AnchoredSemantics

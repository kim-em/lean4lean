import Lean4Lean.Verify.Level.Std

open Lean

private def p : Level := .param `p
private def q : Level := .param `q
private def m : Level := .mvar ⟨`m⟩
private def n : Level := .mvar ⟨`n⟩

private def atoms : Array Level := #[.zero, p, q, m, n]

private def levels : Nat → Array Level
  | 0 => atoms
  | n + 1 =>
    let xs := levels n
    xs ++ xs.map .succ ++ xs.flatMap fun a =>
      xs.flatMap fun b => #[.max a b, .imax a b]

private def samples :=
  (((levels 2).toList.take 200) ++
    ((levels 2).toList.drop 3000).take 200 ++
    ((levels 2).toList.drop 6000).take 200).toArray

private def valuations : Array (Nat × Nat × Nat × Nat) := #[
  (0, 0, 0, 0), (0, 1, 0, 1), (1, 0, 1, 0),
  (1, 1, 1, 1), (2, 5, 3, 7), (5, 2, 7, 3)]

private def paramVal (v : Nat × Nat × Nat × Nat) : Name → Nat
  | `p => v.1
  | `q => v.2.1
  | _ => 0

private def mvarVal (v : Nat × Nat × Nat × Nat) : LMVarId → Nat
  | ⟨`m⟩ => v.2.2.1
  | ⟨`n⟩ => v.2.2.2
  | _ => 0

-- Finite regression coverage for the semantic assumption on opaque `Level.normalize`.
#guard samples.all fun u => valuations.all fun v =>
  Level.Std.eval (paramVal v) (mvarVal v) u.normalize ==
    Level.Std.eval (paramVal v) (mvarVal v) u

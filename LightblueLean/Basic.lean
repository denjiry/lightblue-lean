import Lean
open Lean Elab Term

def hello := "world"
def get := IO.Process.StdioConfig
def a := Lean.Elab.Term.elabTerm
def e := Lean.Parser.runParserCategory


theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp


elab "myterm[" s:str "]" : term => do
  let env ← getEnv
  let parsedSyntax ← match Lean.Parser.runParserCategory env `term s.getString with
                      | Except.ok stx => pure stx
                      | Except.error errmsg => throwError errmsg
  let prop ← elabTerm parsedSyntax none-- (mkConst `Lean.Prop)
  pure prop

theorem propStr : myterm["∀a b, a → b → a ∧ b"] :=
  fun {a b : Prop} (ha : a) (hb : b) => ⟨ha,hb⟩

theorem prop : ∀a b, a → b → a ∧ b :=
  fun {a b : Prop} (ha : a) (hb : b) => ⟨ha,hb⟩

def p := myterm["∀a b, a → b → a ∧ b"]
#print p


elab "#shell_ls" : command => do
  logInfo "shell_ls"
  let cmd: IO.Process.SpawnArgs := {cmd := "ls", args := #["-l"]}
  let output <- IO.Process.output cmd
  logInfo output.stdout

#shell_ls

elab "#shell" s:str+ : command => do
  logInfo "shell"
  let cmds := s.map TSyntax.getString
  if cmds.size < 1 then
    throwUnsupportedSyntax
  let (cmd, args) := (cmds[0]!, cmds[1:])
  let cmd: IO.Process.SpawnArgs := {cmd, args}
  let output <- IO.Process.output cmd
  logInfo output.stdout

#shell "ls" "-l"

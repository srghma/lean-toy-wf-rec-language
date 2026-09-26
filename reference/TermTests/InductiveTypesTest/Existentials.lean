module

public import TyTests.InductiveTypesTest.NestedRecursion
public import LeanScript.Eval
public import LeanScript.CtorFn
public import LeanScript.ToTerm.Elab
public meta import LeanScript.KernelRfl

@[expose] public section

/-!
# `deriving LeanScriptTyWf`: declarations with existentially typed fields

Part of the `deriving LeanScriptTyWf` suite that starts in `TyTests.InductiveTypesTest.Basic`; like it, this
file deliberately does not start with `module`.
-/

open LeanScript

-- 1. recursive tagged union with existential in both constructors and different

mutual
  inductive Process (α : Type) : Type 1 where
    | halt (HaltedState : Type) (getOutOfHalt : HaltedState -> Nat) : Process α
    | step (State : Type)
           (seed  : State)
           (trans : State → ProcessOption α State) : Process α
           -- same as `(trans : State → Option (State × α × Process α)) : Process α`

  inductive ProcessOption (α : Type) : Type → Type 1 where
    | none {State : Type} : ProcessOption α State
    | some {State : Type} (nextState : State)
                          (value : α)
                          (proc : Process α) : ProcessOption α State
end

/--
error: the type `Process` has no `Ty`: existential typing is not yet supported, `HaltedState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Process, ProcessOption

-- TODO: we should be able to model using Term
def mixedProcess : Process Nat :=
  -- Top level: State is Nat
  Process.step Nat 0 (fun n =>
    -- We must return `ProcessOption Nat Nat`
    ProcessOption.some (n + 1) 42 (
      -- Next level: State is String
      Process.step String "hello" (fun s =>
        -- We must return `ProcessOption Nat String`
        ProcessOption.some (s ++ "!") 99 (
          -- Leaf level: a `Process Nat`
          Process.halt Bool (fun b => if b then 1 else 0)
        )
      )
    )
  )

def varyingProcess : Process Nat :=
  Process.step Nat 0 (fun n =>
    if n = 0 then
      ProcessOption.some 1 7 (Process.step Unit () (fun _ => ProcessOption.none))
    else
      ProcessOption.some 1 7 (Process.step Bool true (fun _ => ProcessOption.none)))

/-! ### `mixedProcess` and `varyingProcess`, as terms

Both values are closed, so every existential witness they use is known, and each value
is described with ordinary records, tagged unions and functions of the language. The
existential is simply replaced, at each constructor application, by the witness that
application uses.

`#leanscript_to_term` does this on its own.  `Process` and `ProcessOption` have no
`LeanScriptTyWf` instance, so a constructor application of either is built by the
**constructor function** of `#leanscript_ctor` (`LeanScript.CtorFn`), generated the first
time and reused from its cache after that:

* `Process` has existentials, so each of its constructors builds its own layout:
  `Process.step S seed trans` is the record `{ seed : S, trans : S ⇒ transTy }`, and
  `Process.halt H get` has one field, so it is that field, `H ⇒ nat`;
* `ProcessOption α S` has no existential of its own (its `State` is its index), so it is
  one tagged union, `none | some (nextState : S) (value : α) (proc : procTy)` with Lean's
  tags (`none` = 0, `some` = 1);
* `transTy` and `procTy` — the trees of the fields whose type is `Process`/`ProcessOption`
  itself — are read off the translation of those fields: the type of the term follows the
  value, and is inferred rather than written;
* a witness that is `Unit` is erased as everywhere in the language: the constructor function
  generated for that use (`…_erased01`) drops the `Unit` field `seed` and the `Unit` binder
  of `trans`;
* where values built with *different* witnesses meet (the two branches of the `if` in
  `varyingProcess`), the two types are joined: the value is injected into `TyWf.oneOf`, the
  tagged union with one constructor per layout that occurs there.

The one free choice is the type of `proc` in a `ProcessOption` in which only `none` is ever
built (the inner transitions of `varyingProcess`): no process is ever stored there, so any
closed type works, and `nat` is used.

Arithmetic and string append are external to the language, so they are the two
declarations of the signature `ProcessModel.sig`, named after `Nat.add` and
`String.append`, which `n + 1` and `s ++ "!"` unfold to. The `example`s at the end check,
by `kernel_rfl`, that each term evaluates to the Lean definition with the witnesses filled in.
-/

namespace ProcessModel

abbrev natT : TyWf := .prim .nat
abbrev boolT : TyWf := .prim .bool
abbrev stringT : TyWf := .prim .string

/-- The signature: `add : nat ⇒ nat ⇒ nat` (for `n + 1`) and
    `append : string ⇒ string ⇒ string` (for `s ++ "!"`). -/
def sig : Sig :=
  ⟨[⟨"add", natT ⇒ natT ⇒ natT⟩, ⟨"append", stringT ⇒ stringT ⇒ stringT⟩], by decide⟩

/-- The values of the declarations of `sig`. -/
def env : GlobalEnv sig.decls := (Nat.add, String.append, PUnit.unit)

/-- `mixedProcess`, as a term. -/
def mixedProcess_term   := #leanscript_to_term (sig := sig) mixedProcess
/-- `varyingProcess`, as a term. -/
def varyingProcess_term := #leanscript_to_term (sig := sig) varyingProcess

/-! Every constructor function the two translations used, generated once and cached — the
`#leanscript_layout`s below are these same definitions, found in the cache.  (`_erased01`:
the use at which the hidden type is `Unit`.) -/
/--
info: layout of Process.step: Process.step.leanScriptLayout
fn of Process.step: Process.step.leanScriptCtor
layout of ProcessOption: ProcessOption.leanScriptLayout
fn of ProcessOption.some: ProcessOption.some.leanScriptCtor
layout of Process.halt: Process.halt.leanScriptLayout
fn of Process.halt: Process.halt.leanScriptCtor
layout of Process.step._erased01: Process.step.leanScriptLayout_erased01
fn of Process.step._erased01: Process.step.leanScriptCtor_erased01
layout of ProcessOption._erased01: ProcessOption.leanScriptLayout_erased01
fn of ProcessOption.none._erased01: ProcessOption.none.leanScriptCtor_erased01
fn of ProcessOption.none: ProcessOption.none.leanScriptCtor
-/
#guard_msgs in
#leanscript_ctor_cache

/-! #### Their types

The types were inferred; here they are written out with the layouts of
`#leanscript_layout`, which are the constructor functions' own. -/

/-- `ProcessOption Nat S` whose `proc` field has type `P`:
    `none | some (nextState : S) (value : nat) (proc : P)`. -/
abbrev optionTy (S P : TyWf) : TyWf := #leanscript_layout `ProcessOption `some natT S P
/-- `Process.step S seed trans`, whose transition answers with `O`:
    the record `{ seed : S, trans : S ⇒ O }`. -/
abbrev stepTy (S O : TyWf) : TyWf := #leanscript_layout `Process `step natT S O
/-- `Process.halt H get`: its one field, `get : H ⇒ nat`. -/
abbrev haltTy (H : TyWf) : TyWf := #leanscript_layout `Process `halt natT H

-- [SKIPPED BY PROFILE_LAKE] /-- The generated layouts are the ones the language would write by hand. -/
-- [SKIPPED BY PROFILE_LAKE] example (S P : TyWf) :
-- [SKIPPED BY PROFILE_LAKE]     optionTy S P = .taggedUnion (.skip (.here ⟨S, [natT, P]⟩ [])) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (S O : TyWf) : stepTy S O = .record ⟨S, S ⇒ O, []⟩ := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example (H : TyWf) : haltTy H = TyWf.fn H natT := by kernel_rfl

/-- `mixedProcess`: `Process.step Nat`, holding `ProcessOption Nat Nat`, holding
    `Process.step String`, holding `ProcessOption Nat String`, holding `Process.halt Bool`. -/
abbrev mixedTy : TyWf :=
  stepTy natT (optionTy natT (stepTy stringT (optionTy stringT (haltTy boolT))))

example : Term sig [] mixedTy := mixedProcess_term

/-- `ProcessOption Nat Unit`: `nextState : Unit` is erased, and only `none` is ever built,
    so `proc` is `nat` (see above). -/
abbrev varyingOptUnitTy : TyWf := .taggedUnion (.skip (.here ⟨natT, [natT]⟩ []))
/-- The two processes the `if` chooses between, one constructor per layout:
    0. `Process.step Unit () trans`: `seed : Unit` is erased and so is the `Unit` binder of
       `trans`, which leaves the one field `ProcessOption Nat Unit`;
    1. `Process.step Bool true trans`: the record of `bool` and
       `bool ⇒ ProcessOption Nat Bool`. -/
abbrev varyingProcTy : TyWf := .oneOf varyingOptUnitTy (stepTy boolT (optionTy boolT natT)) []
/-- `varyingProcess`: `Process.step Nat`, holding `ProcessOption Nat Nat`, holding one of
    the two processes. -/
abbrev varyingTy : TyWf := stepTy natT (optionTy natT varyingProcTy)

example : Term sig [] varyingTy := varyingProcess_term

/-! #### What they evaluate to -/

/-- Running a closed term of `sig`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig) env $t)

-- [SKIPPED BY PROFILE_LAKE] /-- `mixedProcess`, with the witnesses `Nat`, `String` and `Bool` filled in. -/
-- [SKIPPED BY PROFILE_LAKE] example : run mixedProcess_term =
-- [SKIPPED BY PROFILE_LAKE]     (0, fun n => ⟨⟨1, by decide⟩, (n + 1, 42,
-- [SKIPPED BY PROFILE_LAKE]       ("hello", fun s => ⟨⟨1, by decide⟩, (s ++ "!", 99,
-- [SKIPPED BY PROFILE_LAKE]         (fun b => match b with | true => 1 | false => 0), ())⟩, ()), ())⟩, ()) := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] /-- `varyingProcess`, with the witnesses `Nat`, then `Unit` or `Bool`, filled in. -/
-- [SKIPPED BY PROFILE_LAKE] example : run varyingProcess_term =
-- [SKIPPED BY PROFILE_LAKE]     (0, fun n => match n with
-- [SKIPPED BY PROFILE_LAKE]       | 0 => ⟨⟨1, by decide⟩, (1, 7, ⟨⟨0, by decide⟩, (⟨⟨0, by decide⟩, ()⟩, ())⟩, ())⟩
-- [SKIPPED BY PROFILE_LAKE]       | _ + 1 => ⟨⟨1, by decide⟩, (1, 7,
-- [SKIPPED BY PROFILE_LAKE]           ⟨⟨1, by decide⟩, ((true, fun _ => ⟨⟨0, by decide⟩, ()⟩, ()), ())⟩, ())⟩, ()) := rfl

end ProcessModel

-- 2. recursive tagged union with existential in both constructors and different

inductive ProcessHaltIsOut (α : Type) : Type 1 where
  | halt (HaltedState : Type) (getOutOfHalt : HaltedState -> Nat)
  | step (State : Type) (seed : State)
         (emit : State → Option (State × α)) -- no recursion here
         (next : State → ProcessHaltIsOut α) -- no nesting here

/--
error: the type `ProcessHaltIsOut` has no `Ty`: existential typing is not yet supported, `HaltedState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for ProcessHaltIsOut

-- 3. recursive tagged union with existential in both constructors and different

mutual
  /-- A Client hides its `ClientState` and emits a request to a `Server`. -/
  inductive Client (Req Resp : Type) : Type 1 where
    | stop (ServerState : Type) (get : ServerState -> Nat) : Client Req Resp
    | mk   (ClientState : Type)
           (seed        : ClientState)
           (send        : ClientState → Req × Server Req Resp)
           : Client Req Resp

  /-- A Server hides its `ServerState`, processes a request,
      produces a response, and transitions to a `Client`. -/
  inductive Server (Req Resp : Type) : Type 1 where
    | stop (ClientState : Type) (get : ClientState -> Nat) : Server Req Resp
    | mk   (ServerState : Type)
           (seed        : ServerState)
           (receive     : ServerState → Req → Resp × Client Req Resp)
           : Server Req Resp
end

/--
error: the type `Client` has no `Ty`: existential typing is not yet supported, `ServerState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Client, Server

-- but this can
mutual
  /-- The twin of `Client`, at client states `C` and server states `S`. -/
  inductive ClientTwin (C S Req Resp : Type) : Type where
    | stop
    | mk (seed : C) (send : C → Req × ServerTwin C S Req Resp)

  /-- The twin of `Server`, at the same two choices. -/
  inductive ServerTwin (C S Req Resp : Type) : Type where
    | stop
    | mk (seed : S) (receive : S → Req → Resp × ClientTwin C S Req Resp)
end

deriving instance LeanScriptTyWf for ClientTwin, ServerTwin

/-- Hides two types: the state and an intermediate token type. -/
structure StreamPipeline (α : Type) (β : Type) where
  State : Type
  Inter : Type
  seed  : State
  feed  : State → α → State × Option Inter
  emit  : State → Inter → State × Option β

/--
error: the type `StreamPipeline` has no `Ty`: existential typing is not yet supported, `State` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for StreamPipeline

/-- Hides three types: the lexer's state, the syntax tree and the evaluator's environment. -/
structure CompilerEngine (α : Type) (β : Type) where
  LexState : Type
  AstType  : Type
  EvalEnv  : Type
  start    : LexState
  lex      : LexState → α → LexState
  parse    : LexState → AstType
  eval     : EvalEnv → AstType → β

-- as with `Unfold`: the refusal is pinned by the `deriving instance` below.

/--
error: the type `CompilerEngine` has no `Ty`: existential typing is not yet supported, `LexState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for CompilerEngine

structure Keyed where
  State : Type
  Elem  : State → Type
  seed  : State
  get   : (s : State) → Elem s

/--
error: the type `Keyed` has no `Ty`: existential typing is not yet supported, `State` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Keyed

structure Layered (α : Type) where
  State : Type
  seed  : State
  subs  : List (Layered α)
  tag   : α

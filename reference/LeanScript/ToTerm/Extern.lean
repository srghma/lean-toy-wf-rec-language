module

public meta import LeanScript.ToTerm.TransRec
public meta import LeanScript.ToTerm.ExternTable

@[expose] public section

meta section

/-!
# The translation: calls of externs

A Lean function of `Init` that is implemented by an extern (`@[extern "lean_…"]`) has no
definition the translation could read: its meaning is the extern.  The catalogue
`LeanScript.LeanInitPureExtern` models the pure externs of `Init`, and
`LeanScript.ToTerm.ExternTable` lists, for each Lean function it models, the entry of the
catalogue that stands for it.  `LeanScript.Extern` is the catalogue applied to values, and
a call is translated to that entry:

* when every argument (and every proof) is a closed Lean value and the entry takes a
  proof, to `Term.extern` of the entry applied to them — the proof is the program's own;
* otherwise to `Term.externCall` applied to the terms of the value arguments, with the
  function that builds the entry from their values; for an entry that takes a proof, to
  `Term.externCallChecked`, whose function *decides* each proposition on those values and
  hands the proof it gets to the entry, and whose fallback (for values that do not
  satisfy it, which a Lean program cannot give) is the translation of the `Inhabited`
  default of the result type.

The catalogue is in two levels (a family per section of `Init`, and `LeanInitPureExtern`
with one constructor per family), so an entry is built through its shorthand
(`LeanInitPureExtern.lean_nat_add`, which takes the parameters of the catalogue like a
constructor would) and then unfolded to the two constructors it stands for
(`.preludeExtern (.lean_nat_add a b)`).

What each argument of the Lean function is, is read off the table:

* a type argument is a type of the language, fixed where the term is written
  (`.lean_array_push αt`);
* the string `s` of an argument `pos : s.Pos` is fixed where the term is written too, since
  the type of `pos` names it, and must be a closed Lean value;
* a value argument is translated;
* the `Inhabited` instance of an entry that takes a default value is translated as its
  `default`;
* a `USize` argument is a `Nat` here: `Array.uget`, `Array.uset` and
  `String.Internal.ugetUTF8Byte` are translated to the entries of `Array.getInternal`,
  `Array.set` and `String.Internal.getUTF8Byte`, and `String.Pos.Raw.next'` to the entry of
  `String.next'`;
* a proof is decided when the term runs (see above).

Externs are never looked up in the signature.  `Nat.gcd` is translated as an ordinary
function, as if it had no `@[extern]` (so it must be declared in the signature), and
`Nat.gcd._unary ⟨a, b⟩` is read as `Nat.gcd a b`.  A call of any other function marked
`@[extern]` that the catalogue does not model is refused.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- The name a catalogue comment writes, with a numeric component (as in the name of a
    private declaration, `_private.Init.Meta.Defs.0.…`) read as a number. -/
def externNameOf (s : String) : Name :=
  (s.splitOn ".").foldl (init := .anonymous) fun n part =>
    match part.toNat? with
    | some k => .num n k
    | none => .str n part

/-- The externs a term can call, by the Lean function they model. -/
def externMap : Std.HashMap Name ExternEntry :=
  externTable.foldl (init := {}) fun m e => m.insert (externNameOf e.leanFn) e

/-- Is `n` a Lean function the translation calls as an extern? -/
def isKnownExtern (n : Name) : Bool := externMap.contains n

/-- The Lean functions marked `@[extern]` that are translated as ordinary functions. -/
def externAsOrdinary : List Name := [``Nat.gcd]

/-- The parameters of the catalogue at the types of the language: the arguments
    `LeanScript.Extern` applies `LeanScript.LeanInitPureExtern` to. -/
def externParams : MetaM (Array Expr) := do
  let some v := (← getConstInfo ``LeanScript.Extern).value?
    | throwError "`#leanscript_to_term`: internal: `LeanScript.Extern` has no definition"
  return v.eta.getAppArgs

/-- The type of the language an entry of the catalogue answers with: the index of its
    type. -/
def externResultTy (entry : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType entry)
  let some τ := ty.getAppArgs.back?
    | throwError "`#leanscript_to_term`: internal: {entry} is not an extern"
  return τ

/-- The domain of the next argument of a partially applied entry. -/
def externNextDomain (cur : Expr) : MetaM (Expr × BinderInfo) := do
  let .forallE _ d _ bi ← whnf (← inferType cur)
    | throwError "`#leanscript_to_term`: internal: {cur} takes no more arguments"
  return (d.cleanupAnnotations, bi)

/-- Hand the value `x` to an argument of type `d` of an entry: it has that type, or is a
    value of the language standing for it (a list read back as a Lean `List`, a value
    wrapped in a `Thunk`). -/
def externConvert (x d : Expr) : MetaM Expr := do
  if ← isDefEq (← inferType x) d then return x
  for f in [``LeanScript.TyWf.Den.toList, ``Thunk.pure] do
    try
      let y ← mkAppM f #[x]
      if ← isDefEq (← inferType y) d then return y
    catch _ => pure ()
  throwError "`#leanscript_to_term`: internal: the value{indentExpr x}\nof type\
    {indentExpr (← inferType x)}\nis not an argument of type{indentExpr d}"

/-- The `Nat` a `USize` argument stands for. -/
def natOfUSize (a : Expr) : MetaM Expr := do
  let a := a.consumeMData
  match a.getAppFnArgs with
  | (``USize.ofNat, #[n]) => return n
  | (``Nat.toUSize, #[n]) => return n
  | (``USize.ofNatLT, #[n, _]) => return n
  | (``USize.ofNatTruncate, #[n]) => return n
  | _ => return mkApp (mkConst ``USize.toNat) a

/-- The list `[σ₁, …, σₙ]` of types of the language. -/
def tyListE (σs : Array Expr) : Expr :=
  σs.foldr (init := mkApp (mkConst ``List.nil [0]) (mkConst ``LeanScript.TyWf)) fun σ acc =>
    mkApp3 (mkConst ``List.cons [0]) (mkConst ``LeanScript.TyWf) σ acc

/-- An entry built from its shorthand (`LeanInitPureExtern.lean_nat_add a b`, from
    `LeanScript.LeanInitPureExternShorthands`), unfolded to the constructors it stands for:
    the constructor of the family, wrapped in the one of `LeanInitPureExtern`
    (`.preludeExtern (.lean_nat_add a b)`), so a translated term does not go through the
    shorthand. -/
def externUnfoldShorthand (entry : Expr) : MetaM Expr := do
  match ← unfoldDefinition? entry with
  | some e => return e.headBeta
  | none => return entry

/-- The spine of the terms `ts`, of the types `σs`. -/
def spineE (c : TCtx) (ts σs : Array Expr) : Expr := Id.run do
  let mut acc := mkAppN (mkConst `LeanScript.Spine.nil) #[c.sg, c.gamma]
  for j in (List.range ts.size).reverse do
    acc := mkAppN (mkConst `LeanScript.Spine.cons)
      #[c.sg, c.gamma, σs[j]!, tyListE (σs.extract (j + 1) σs.size), ts[j]!, acc]
  return acc

/-- The entry `cur`, applied to the rest of its arguments, from the argument number `i` on
    (`j` is the number of values used so far).  The values are `vals`; a proof is decided,
    and the answer is then an `Option` (`checked`).  Also gives the result type. -/
partial def externBody (kinds : Array Char) (args vals : Array Expr) (checked : Bool) :
    Nat → Nat → Expr → MetaM (Expr × Expr)
  | i, j, cur => do
    if h : i < kinds.size then
      let (d, _) ← externNextDomain cur
      match kinds[i] with
      | 't' => externBody kinds args vals checked (i + 1) j (mkApp cur (← tyOfType args[i]!))
      | 's' =>
          let a := args[i]!
          if a.hasFVar || a.hasMVar then
            throwError "`#leanscript_to_term`: the type of an argument of this extern names \
              the value{indentExpr a}\nso it must be fixed where the term is written, \
              and this one is only known when the term runs"
          externBody kinds args vals checked (i + 1) j (mkApp cur a)
      | 'p' =>
          let inst ← match ← trySynthInstance (mkApp (mkConst ``Decidable) d) with
            | .some inst => pure inst
            | _ => throwError "`#leanscript_to_term`: the extern takes a proof of{indentExpr d}\n\
                which the language erases and which is not decidable, so it cannot be \
                checked when the term runs"
          let (thenB, τ) ← withLocalDeclD `h d fun h => do
            let (b, τ) ← externBody kinds args vals checked (i + 1) j (mkApp cur h)
            return (← mkLambdaFVars #[h] b, τ)
          let optTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``LeanScript.Extern) τ)
          let elseB ← withLocalDeclD `h (mkNot d) fun h =>
            mkLambdaFVars #[h] (mkApp (mkConst ``Option.none [0])
              (mkApp (mkConst ``LeanScript.Extern) τ))
          return (mkAppN (mkConst ``dite [Level.one]) #[optTy, d, inst, thenB, elseB], τ)
      | _ =>
          let x ← externConvert vals[j]! d
          externBody kinds args vals checked (i + 1) (j + 1) (mkApp cur x)
    else
      let τ ← externResultTy cur
      let cur ← externUnfoldShorthand cur
      if checked then
        return (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``LeanScript.Extern) τ) cur, τ)
      return (cur, τ)

/-- The entry of a call whose arguments are all closed Lean values, applied to them (and to
    the proofs of the program), or `none` if one of them is not an argument of the entry
    as it stands. -/
def externClosedEntry? (kinds : Array Char) (args : Array Expr) (ctor : Expr) :
    MetaM (Option Expr) := do
  let mut cur := ctor
  for i in [0:kinds.size] do
    let a := args[i]!
    let (d, _) ← externNextDomain cur
    let x ← match kinds[i]! with
      | 't' => tyOfType a
      | 'i' => mkAppOptM ``Inhabited.default #[none, some a]
      | 'u' => return none
      | _ => pure a
    unless ← isDefEq (← inferType x) d do return none
    cur := mkApp cur x
  return some (← externUnfoldShorthand cur)

/-- The call `e` (whose head is the constant `n`, applied to `args`) as a call of an
    extern, or `none` if `n` is not implemented by an extern.  A function marked
    `@[extern]` that the catalogue does not model is refused. -/
def transExternApp? (trans : TransFn) (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  -- `Nat.gcd._unary ⟨a, b⟩` is `Nat.gcd a b`, which is an ordinary function
  if n == ``Nat.gcd._unary then
    let some p := args[0]? | return some (← trans c (← etaExpand e))
    let (a, b) ← match p.consumeMData.getAppFnArgs with
      | (``PSigma.mk, #[_, _, a, b]) => pure (a, b)
      | _ => pure (← mkAppM ``PSigma.fst #[p], ← mkAppM ``PSigma.snd #[p])
    let e' := mkAppN (mkApp2 (mkConst ``Nat.gcd) a b) (args.extract 1 args.size)
    return some (← trans c e')
  if externAsOrdinary.contains n then return none
  let some ent := externMap[n]? | do
    if isExtern env n then
      let sym := match getExternNameFor env `c n with
        | some s => s!" `{s}`"
        | none => ""
      throwError "`#leanscript_to_term`: `{n}` is implemented by the extern{sym}, which is \
        not one of the pure externs of `Init` the language models \
        (`LeanScript.LeanInitPureExtern`), so a term cannot call it"
    return none
  let kinds := ent.kinds.toList.toArray
  let arity ← forallTelescopeReducing (← inferType (mkConst n lvls)) fun xs _ =>
    return xs.size
  unless arity == kinds.size do
    throwError "`#leanscript_to_term`: internal: `{n}` takes {arity} arguments, but the \
      entry `{ent.ctor}` of the catalogue models {kinds.size}"
  -- a partial application: the missing arguments become binders
  if args.size < kinds.size then
    return some (← trans c (← etaExpand e))
  let own := args.extract 0 kinds.size
  -- the shorthand of the entry, which takes the parameters of `LeanInitPureExtern`
  let ctor := mkAppN (mkConst (``LeanScript.LeanInitPureExtern ++ Name.mkSimple ent.ctor))
    (← externParams)
  let checked := kinds.contains 'p'
  let call := mkAppN e.getAppFn own
  -- the extern of a Lean program applied to closed values: the entry, with its own proof
  let closed := own.all fun a => !a.hasFVar && !a.hasMVar
  let entry? ← if checked && closed then externClosedEntry? kinds own ctor else pure none
  let t ← match entry? with
    | some entry =>
        pure (mkAppN (mkConst `LeanScript.Term.extern)
          #[c.sg, c.gamma, ← externResultTy entry, entry])
    | none => do
      -- the values: translated, and handed to the entry when the term runs
      let mut ts : Array Expr := #[]
      let mut σs : Array Expr := #[]
      for i in [0:kinds.size] do
        let a := own[i]!
        let arg? ← match kinds[i]! with
          | 'v' => pure (some a)
          | 'i' => some <$> mkAppOptM ``Inhabited.default #[none, some a]
          | 'u' => some <$> natOfUSize a
          | _ => pure none
        if let some arg := arg? then
          ts := ts.push (← trans c arg)
          σs := σs.push (← tyOfTerm arg)
      let σsE := tyListE σs
      let (mk, τ) ← withLocalDeclD `vs (mkApp (mkConst ``LeanScript.TyWf.DenList) σsE)
          fun vs => do
        let mut vals : Array Expr := #[]
        let mut rest := vs
        for j in [0:σs.size] do
          let tl := tyListE (σs.extract (j + 1) σs.size)
          vals := vals.push (mkAppN (mkConst ``LeanScript.TyWf.DenList.head) #[σs[j]!, tl, rest])
          rest := mkAppN (mkConst ``LeanScript.TyWf.DenList.tail) #[σs[j]!, tl, rest]
        let (body, τ) ← externBody kinds own vals checked 0 0 ctor
        if τ.containsFVar vs.fvarId! then
          throwError "`#leanscript_to_term`: internal: the type of `{n}` depends on a value"
        return (← mkLambdaFVars #[vs] body, τ)
      let spine := spineE c ts σs
      if checked then
        -- the value where the proposition does not hold: a `default` of the result type
        let α ← inferType call
        let inst ← match ← trySynthInstance (← mkAppM ``Inhabited #[α]) with
          | .some inst => pure inst
          | _ => throwError "`#leanscript_to_term`: `{n}` takes a proof, which the language \
              erases, so the term decides the proposition when it runs; it needs a value \
              to answer with where the proposition does not hold, but{indentExpr α}\nhas \
              no `Inhabited` instance"
        -- (the default of `Nat` unfolds to `Nat.zero`, which is written as the literal)
        let dflt ← if (← whnfR α).isConstOf ``Nat then pure (mkNatLit 0)
          else mkAppOptM ``Inhabited.default #[α, inst]
        let fb ← trans c dflt
        pure (mkAppN (mkConst `LeanScript.Term.externCallChecked')
          #[c.sg, c.gamma, σsE, τ, spine, mk, fb])
      else
        pure (mkAppN (mkConst `LeanScript.Term.externCall) #[c.sg, c.gamma, σsE, τ, spine, mk])
  -- the arguments past the extern's own, if it answers with a function
  return some (← applyArgs trans c t call (args.extract kinds.size args.size))

/-- The call of an extern a decision procedure unfolds to: `instDecidableEqNat a b` is
    `Nat.decEq a b`, which is the extern `lean_nat_dec_eq`.  Unfolds `inst` a few steps,
    as long as its head is not a known extern. -/
def decidableExtern? (inst : Expr) : MetaM (Option Expr) := do
  let mut i := inst.headBeta
  for _ in [0:8] do
    if let .const m _ := i.getAppFn then
      if isKnownExtern m then return some i
    -- a projection out of an instance (`GetElem.getElem inst …`) is the instance's field
    if let some i' ← unfoldProjInst? i then
      i := i'.headBeta
      continue
    match ← unfoldDefinition? i with
    | some i' => i := i'.headBeta
    | none => return none
  return none

end LeanScript.ToTerm

end

end

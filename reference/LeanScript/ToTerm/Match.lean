module

public meta import LeanScript.ToTerm.Ctx

@[expose] public section

meta section

/-!
# A dispatch Lean compiled with a default

A `match` that repeats one branch, and the `_sparseCasesOn_` auxiliary an incomplete set
of patterns compiles to.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## A dispatch that repeats one branch

A `match` whose last pattern is a wildcard is compiled into a dispatch that names *every*
constructor, with the wildcard's body repeated in the branch of each constructor the
earlier patterns did not name.  The grammar has a form for exactly that shape —
`LeanScript.Term.enum_casesOnWithDefault'` and
`LeanScript.Term.taggedUnion_casesOnWithDefault'`, which name some of the constructors and
send the rest to one default branch — so the repetition is detected here and the partial
form is what is built.

A branch counts as the default only when it **ignores the fields it binds**: a wildcard
whose body mentions the value it matched (`| _ => f x`) is a different body in each
branch, and then the exhaustive form is the honest translation. -/

/-- The body of a branch that binds its constructor's fields and uses none of them, and
    nothing when the branch does use one: only such a branch can be the default of a
    partial dispatch, since the default binds nothing. -/
def branchDefaultBody? (minor : Expr) (ctorName : Name) : MetaM (Option Expr) := do
  let ci ← getConstInfoCtor ctorName
  forallBoundedTelescope (← inferType minor) (some ci.numFields) fun xs _ => do
    let body := (mkAppN minor xs).headBeta
    if xs.any (fun x => body.containsFVar x.fvarId!) then return none
    return some body

/-- The branch a dispatch repeats, and the constructors that take it: the largest group
    of branches that are the *same* field-free body.  There has to be more than one of
    them — a single branch is no shorter written with a default — and they cannot be all
    of them, since the default of a dispatch that names every constructor is unreachable
    and the grammar refuses it. -/
def repeatedBranch? (minors : Array Expr) (ctors : Array Name) :
    MetaM (Option (Expr × Array Nat)) := do
  let n := ctors.size
  if n < 3 then return none
  if minors.size < n then return none
  let mut bodies : Array (Option Expr) := #[]
  for i in [0:n] do
    bodies := bodies.push (← branchDefaultBody? minors[i]! ctors[i]!)
  let mut best : Option (Expr × Array Nat) := none
  for i in [0:n] do
    if let some b := bodies[i]! then
      let mut idxs : Array Nat := #[]
      for j in [0:n] do
        if let some b' := bodies[j]! then
          if b' == b then idxs := idxs.push j
      if idxs.size ≥ 2 && idxs.size < n then
        match best with
        | some (_, prev) => if prev.size < idxs.size then best := some (b, idxs)
        | none => best := some (b, idxs)
  return best

/-! ## A `match` that Lean compiled with a default

A `match` whose patterns do not name every constructor is compiled into an auxiliary
Lean calls `f._sparseCasesOn_i`: the branches of the constructors the patterns *do* name,
in constructor order, followed by one `else` branch that every other constructor takes.
Which constructors are named is a **bit mask** in the type of that `else` branch
(`Nat.hasNotBit mask t.ctorIdx`), so the shape of the dispatch is read off the auxiliary
rather than guessed, and it is exactly the shape of the grammar's
`xxx_casesOnWithDefault`. -/

/-- Is this the auxiliary a `match` with an incomplete set of patterns compiles to? -/
def isSparseCasesOn (n : Name) : Bool := n.getString!.startsWith "_sparseCasesOn"

/-- What a `_sparseCasesOn_` auxiliary dispatches on: how many arguments it takes, and
    which constructors, by number, have a branch of their own, and how many parameters of
    the type come before its motive.  The rest go to the `else` branch, which is its last
    argument. -/
def sparseCasesOnInfo? (n : Name) : MetaM (Option (Nat × List Nat × Nat)) := do
  let some ci := (← getEnv).find? n | return none
  forallTelescopeReducing ci.type fun xs _ => do
    if xs.size < 3 then return none
    let elseTy ← whnf (← inferType xs[xs.size - 1]!)
    let .forallE _ dom _ _ := elseTy | return none
    let (``Nat.hasNotBit, #[maskE, _]) := dom.getAppFnArgs | return none
    let some mask ← evalNat (← whnf maskE) | return none
    let named := (List.range 64).filter fun i => mask &&& (1 <<< i) != 0
    -- the parameters of the type come first
    if named.length + 3 > xs.size then return none
    return some (xs.size, named, xs.size - 3 - named.length)

end LeanScript.ToTerm

end

end

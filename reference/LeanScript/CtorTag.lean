module

public meta import Lean.Elab.Command
public meta import LeanScript.Ty.Schema

@[expose] public section

meta section

/-!
# `ctor_tag`: the proof that a constructor number is a constructor of its type

A tagged value names its constructor by **number**, and the number comes with the proof
that the type has that many constructors — `t < l.length`.  For a concrete schema and a
concrete tag that proof is a computation, so it is the default of the argument
(`:= by ctor_tag`) and nothing has to be written by hand:

```
Term.taggedUnion_mk optNat 0 (.cons (.nat_mk 3) .nil)
```

The tactic tries, in order:

* `assumption`, for a tag whose bound is already in the context — a generic function
  over the constructors of a schema;
* `decide`, for a concrete schema and a concrete tag, which is the common case;
* `simp` on the definition of the two schema lengths followed by `omega`, for a tag that
  is concrete against a schema that is only partly known.
-/

/-- Close a goal `t < l.length`, the bound a constructor number of a tagged union or of
    a record carries.  See this module's header. -/
macro "ctor_tag" : tactic =>
  `(tactic|
    first
      | assumption
      | decide
      | (simp only [LeanScript.LeanTaggedUnionSchema.length,
            LeanScript.LeanRecordSchema.length, LeanScript.CtorsWithPayload.length]
         omega)
      | omega)

/-- Close a goal `lo ≤ i`, the bound that keeps the branches of a partial dispatch on an
    enum or on a tagged union in strictly increasing constructor order: `i` is the
    constructor this branch names and `lo` is one past the constructor the previous
    branch named.  A
    concrete pair of numbers is a computation, so this is the default of the argument
    (`:= by ctor_ge`) and a well-ordered list of branches needs nothing written by
    hand. -/
macro "ctor_ge" : tactic =>
  `(tactic|
    first
      | assumption
      | omega
      | decide)

/-- Close a goal `k < n`, where `k` is **how many constructors a partial dispatch names**
    and `n` is how many constructors the type has.  It is the bound that keeps a
    `xxx_casesOnWithDefault` from naming every constructor, which would make its default
    branch unreachable — a dispatch that names them all is an exhaustive
    `xxx_casesOn` and has to be written as one.

    Both numbers are a computation for a schema written out, so this is the default of
    the argument (`:= by ctor_lt`) and nothing has to be written by hand. -/
macro "ctor_lt" : tactic =>
  `(tactic|
    first
      | assumption
      | (simp only [LeanScript.LeanTaggedUnionSchema.length_map,
            LeanScript.LeanTaggedUnionSchema.length,
            LeanScript.LeanRecordSchema.length,
            LeanScript.CtorsWithPayload.length,
            LeanScript.LeanEnumSchema.nOfConstructors]
         omega)
      | omega
      | decide)

end

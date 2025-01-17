# Local Instances

# Structures
The usual way to define a `structure` is to write its name, then `where` (or `:=`) and then the
list of fields that we want a term of the structure be made of

    structure MyStructure where
        firstfield : firstType
        secondfield : secondType
        ...
        lastfield : lastType

where each field is a term in some known type. Every field can depend upon the previous ones.

* The `nth` field of a structure can be *any* term (of the right type...) but if we write

    `nth_field : nth_Type := myterm`
    
we are declaring that, if left unspecified, the `n`th term will be
`myterm`. This is typically what we do when `nthType = Prop`: we do not want that *some property*
is satisfied, but that *our sought-for property* is satisfied.


Declaring a structure as above automatically creates several terms:
1. A term `MyStructure.mk : firstType → secondType → ... → lastType → MyStructure` to *construct*
terms; the name `.mk` can be overridden with the syntax `constructor_name ::` on the second line (so
starting the list of fields on the third line).
1. A term `MyStructure.nthfield : MyStructure → nthType`: this *projects* a term of type
`MyStructure` onto its `nth` field.
1. If the attribute `@[ext]` is prepended on the line before the declaration, a theorem 
`MyStructure.ext` is created, of type

    ∀ {x y : MyStructure}, x.firstfield = y.firstfield → ... → x.lastfield = y.lastfield → x = y`

saying that if all fields of two terms coincide, the terms themselves coincide. Actually, if
`nthType = Prop`, the arrow `x.(n-1)stfield = y.(n-1)stfield → x.nthfield = y.nthfield → ` is skipped
thanks to proof irrelevance. Another theorem `MyStructure.ext_iff` is also added, that adds the
reverse implication.
1. It the `@[class]` attribute is added (possibly with syntax `@[ext, class]`, a new class is
created as well so that `instance : MyStructure := someterm` become accessible. 


We can define a structure `OneNat`, that "packs" a single natural number; or the structures
`TwoNat` and `Couple` that pack to numbers;  or the structure of order pairs that pack two numbers
where the second is larger or equal than the first : this is called a *mixin*.



+++ Use of parameters
It is also possible to define structures that depend on parameters. The syntax is the usual as for 
`def` or `theorem`.
+++

 `⌘`

## Constructing terms

To look at the details, let's try to buid some *terms* of the above structures.

When doing so, `VSCode` comes at rescue: once we declare that we are looking for a term in a
structure `MyStructure` (*i. e.* in an inductive type with one constructor, itself a function with
several arguments), we can type
    
    def MyTerm : MyStructure :=
    _

(beware that the underscore `_` **must not be indented**), and a (blue) bulb💡appears. Click on it 
to  generate a *skeleton* of the structure at hand (transforming `:=` into `where`), so you do not
need to remember all fields by heart.

Either using💡or not, there are three ways to define a term of a structure:

1. `MyTerm : MyStructure :=`, followed either by `by → constructor` or `{firstfield := firstterm, secondfield := secondterm, ..., lastfield := lastterm}`. 

1. `MyTerm : MyStructure where` and then the list `nthfield := nthterm`, each one a new (indented) line (observe that the💡help replaces `:=` with `where` automatically).

1. Using the so-called *anonymous constructor* provided by `⟨` and `⟩`: just insert the list of terms `⟨firstterm, secondterm, ..., lastterm⟩` and Lean will understand.


* Remember that `class`es are a special case of `structure`s: so, definining an `instance` as we did last week really means constructing a term of a certain `structure`. Points 1. − 3. above are particularly useful for this.


`⌘`


Now, constructing terms of a structure with many fields is particularly 
1. boring,
1. error-prone,
1. far from mathematical usage: to construct a term of a complicated structure I might want to 
use a term of a simpler one and "only add what is necessary".

There are two ways, somewhat parallel to the `MyStructure := ...` *vs* `Mystructure where ...` syntaxes.
* Mention `with`
* Mention `__`
e finire con un esempio con `AddMonoid`, tipo


`⌘`


+++ Labels Matter
The big difference between `TwoNat`, and `Couple` are the names of the fields: `⌘`.

These names **are relevant**! You might think of a term of type `TwoNat` (or `Couple`) as a pair of
*labelled* naturals, and that a structure is a collection of *labelled* terms. So, a term of `TwoNat` 
+++



## Extends

We have already seen the `extends` syntax before: let's try to analyze its behaviour in details
knowing how `structures` work.

The main point is to generalise to the whole type what we did for terms using `where` or `__`.

* SAY SOMETHING HERE

* THEN QUOTE
If the parent structure types have overlapping field names, then all overlapping field names must
have the same type. If the overlapping fields have different default values, then the default value
from the last parent structure that includes the field is used. New default values in the child
structure take precedence over default values from the parent structures.


+++ Interaction of `with` and `extend`
### Constructing terms when there is `extend`



# Local Instances

# Structures
The usual way to define a `structure` is to write its name, then `where` and then the list of
fields that we want a term of the structure be made of

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


We can define a structure `OneNat`, that "packs" a single natural number; or the structure
`TwoNat` that packs to numbers;  or the structure of order pairs that pack two numbers where the
second is larger or equal than the first : this is called a *mixin*.


 `⌘`


The big difference between `TwoNat`, and `Couple` are the names of the fields. These
name **are relevant**! You might think of a term of type `TwoNat` as a pair of *labelled* naturals,
and that a structure is a collection of labelled terms.

It is also possible to define structures that depend on parameters.

**TO DO SO...**

## Extends

## Constructing terms

To look at the details, let's try to buid some *terms* of the above structures.

When doing so, `VSCode` comes at rescue: once we declare that we are looking for a term in a
structure `MyStructure` (*i. e.* in an inductive type with one constructor, itself a function with
several arguments), we can type
    
    def MyTerm : MyStructure :=
    _

(beware that the underscore `_` **must not be indented**), and a (blue) bulb💡appears. Click on it 
to  generate a *skeleton* of the structure at hand, so you do not need to remember all fields by
heart.

**SAY THAT WE CAN USE ⟨ and ⟩** : anonymous constructors (3.4.1.3)

** SAY THAT ALL THIS BECOMES VERY IMPORTANT IF STRUCTURES ARE CLASSES WHEN DECLARING ISNTANCES**
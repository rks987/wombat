= Wombat4

This latest design of wombat is, even more than its predecessors, inspired 
by great programming languages of the past.
- Like Algol68 (and every Assembly language), identifiers stand for constants.
 That constant might be an Assignable (Robert Harper terminology), and hence
 effectively a memory address. In honour of Algol68 we sometimes use backward
 words for closing brackets (do-od, if-fi).
- In Python everything is a class. Wombat Structures are the nearest thing to
 classes, and every Type is a Structure. In honour of Python we use double
 dunder identiers for significant characteristics.
- In Simula67 a class is formed by an interrupted bit of code that is left with
 its innards accessible. Structures work the same. In wombat there is a 1-1
 correspondence between Types and the constraints imposed by an expression.
 So the innards of a Structure are just an expression, but the identifiers
 defined are then accessible externally through matching atoms.
- Wombat has proposition types. This derives from the Curry-Howard correspondence,
 but only `Prop` types, with 0 or 1 value, are used for propositions. These use
 mathematical style operators, so `A implies% B` has a matching `A=>>B` function
 type and conversions both ways are available. Proposition related operators
 are usually indicated with a trailing `%`. Proposition types are used to include
 the laws for types in their defining structure.
- User defined operators are inspired by Agda, but are more general.

The extra that wombat adds is to place the types in an order lattice that is
 intended to closely follow the inclusion hierarchy of sets. The type system
 closely follows the way sets are used in Mathematics (and in TLA+), where
 sets are not intended to be arbitrary but to be characterised completely by
 the properties specified at their definition. This hierarchy also provides the software
 structures commonly provided by interfaces or traits or typeclasses.

First a philosophical point. There are no actual infinite things. There are 
 unlimited things, and we conveniently act as if they all exist, but unlimited
 things are built from algorithms acting on finite things. Propositions that
 apply to unlimited things are the interesting sort, and that means proving
 things about code.

== A note on syntax

Identifiers are alphanumeric plus "`_`", starting with a non-digit, with an optional 
`%` (by convention for things related to `Prop`s) or `?` (related to boolean), followed by 0 or 
more primes (aka single quotes "`'`"). Some types have constants (decimal numbers, 
strings). An `Atom` constant is a dot ("`.`") followed by an identifier. Other 
sequences of characters, plus identifiers can be suboperators: An identifier can be 
prefixed by a backtick ("``` ` ```") to say that this is a new identifier and with
a double backtick to say this is a new free identifier (explained later). A sequence
of backticks always breaks on its left, and a sequence of primes on its right.
Identifiers and sequences of other characters can be suboperators which are
separators in an operator (for example in the if-then-else operator, `if`, `then`
and `else` are called "suboperators")

== Types and Structures

A structure has the form `< parent : expression >`. The value of the expression is ignored.
We can define basic mathematical structures:
```
`Magma = < : `T:Type; `op:T*T=>>T; >;
`Semigroup = 
  < Magma : `assoc : ∀%{T`x*T`y*T`z=>>Prop: op(x,op(y,z)) =% op(op(x,y),z) };  >;
```
Inside the structure definitions `T`, `op` and `assoc` are just identifiers
constrained by their types. Outside they are properties defined by their
corresponding atoms: `.T`, `.op` and `.assoc`, So if we have a `S:Semigroup`
then we can access its `op` property as `S.op`.

A value of type `Semigroup` has an `assoc` property value. But since it is a
`Prop` type it has at most one value, and hence takes up 0 bits. It just
constrains the other properties. We can constrain things more explicitly.
```
`NatMagma = < Magma : T = Nat; > # some binary op on Nat
```
Even if we constrain everything it is still a type (with one value):
```
`NatAddMagmaType = < Magma: T = Nat; op = addNat; >
```
Which is why we often need the `@` operator which returns the value of a type 
with only one:
```
`NatAddMagma = @ NatAddMagmaType
```
Types are created by a structure that uniquely characterises it.
Here is the definition of the natural numbers:

```
`Nat = NewType < : 
      `Nat = __unique__:Type;
      `zero:Nat;
      `succ:Nat<=>>Nat; # TEmbed, backwards fails for zero.
      `succNotZero:∀%{Nat`n=>>Prop:Neq%(Nat)(succ n,zero)};
      `induct:∀%{(Nat=>>Prop)`p=>>Prop:
          (p(zero) And% ∀%{Nat`n=>>Prop: p(n) Implies% p(succ n)})
          Implies% ∀%{Nat`n=>>Prop: p(n)} };
    > 
```
A type can be primitive, in which case the defining properties
of the type are axions. Normally a type has an implementation.
An implementation uses the defining properties of the implementing
type to construct a 
```
`Nat:Type definedBy < Equality(Nat): # equality from implementing type
       `zero:Nat;
       `succ:Nat<=>>Nat; # TEmbed, backwards fails for zero.
       `succNotZero:∀%{Nat`n=>>Prop:Neq%(Nat)(succ n,zero)};
       `induct:∀%{(Nat=>>Prop)`p=>>Prop:
           (p(zero) And% ∀%{Nat`n=>>Prop: p(n) Implies% p(succ n)})
           Implies% ∀%{Nat`n=>>Prop: p(n)} };
       `IsDistinguishable = 
           <Distinguishable(Nat)=Decideable(Nat*Nat,Eq%(Nat)): 
               decideBool (Nat``x*Nat``y) = (x,y) | (
                   {:$=(zero,zero); Bool.true } +
                   {:$:[(zero,succ _),(succ _,zero)]; Bool.false } +
                   {:$=(succ`xx,succ`yy): decideBool(xx,yy)}
               ); # other properties of Decideable get created
           >
    > ; creates a $DefinedBy%(Nat, <...>) proposition witness
```
# An exponentiation has to have  addition and multiplation
# that work with expoentiation, i.e. A^X × A^Y = A^(X+Y)
# examples include numbers, of course, but also types with
# A+B = DisjointUnion(.left->A,.right->B) and A×B = Tuple[A,B]
# and A^B = B=>>A.

`Addable = < :
    __base__ = `T :Type;
    `ConformsToMonoid: [.add]=>>Monoid;
>;
`{(40)["+"](40)} (``x.``y) = Union(Typeof(x),Typeof(y)).ConformsToMonoid.add.op(x,y);

`Multiplyable = < Addable :
    `ConformsToMonoid: [.add,.mul]=>>Monoid;
    `LeftDistributive: ∀%{T`x*T`y*T`z=>Prop: 
        `mul=ConformsToMonoid.mul.op; `add=ConformsToMonoid.add.op;
        mul(x,add(y,z)) =% add(mul(x,y).mul(x,z)) };
    `RightDistributive: ∀%{T`x*T`y*T`z=>Prop: 
        `mul=ConformsToMonoid.mul.op; `add=ConformsToMonoid.add.op;
        mul(add(y,z),x) =% add(mul(y,x).mul(z,x)) };
>;
`{(60)["×"](60)} (``x.``y) = Union(Typeof(x),Typeof(y)).ConformsToMonoid.mul.op(x,y);

`Exponentiationable = < Multiplyable :
    `mul=ConformsToMonoid.mul.op; `add=ConformsToMonoid.add.op;
    `ConformsToMagma: [.exp]=>>Magma;
    `AddMulInterchange = ∀%{T`x*T`y*T`z=>Prop: 
        `mul=ConformsToMonoid.mul.op; `add=ConformsToMonoid.add.op;
        `exp=ConformsToMagma.exp.op;
        exp(x,add(y,z)) =% exp(x,y) × exp(x,z) };
>;


# FOOTNOTE: once we have addition we would like to allow multiply by a natural
# number. I.e. 3×a=a+a+a. And when we have multiply we would like exponentiation
# by a natural number, so that a^3=a×a×a. In all of the above symmetric cases, 
# we would like types that are compatible with the natural numbers as .add and .mul
# monoids to behave compatibly with these straightforward multiply and exponent.
# And maybe we want to generalise for mixed types in some ways.
    
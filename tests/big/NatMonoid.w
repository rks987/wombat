%/include /home/rks/sw/wombat/wlib/wombat.wh

# within the structure definition, Nat refers to the implementing type
`Nat:Type definedBy < Equality(Nat): # equality from implementing type
       `zero:Nat;
       `succ:Nat<=>>Nat; # TEmbed, backwards fails for zero.
       `succNotZero:∀%{Nat`n=>>Prop:Neq%(Nat)(succ n,zero)};
       `induct:∀%{(Nat=>>Prop)`p=>>Prop:
           (p(zero) And% ∀%{Nat`n=>>Prop: p(n) Implies% p(succ n)})
           Implies% ∀%{Nat`n=>>Prop: p(n)} };
       `IsDistinguishable = <Distinguishable(Nat): decide Nat`x*Nat`y = @ >
    > ; creates a $DefinedBy%(Nat, <...>) proposition witness
Eq%(Nat) = Nat.IsDistinguihable.Eq%;
# We can access Nat's defining structure type as ^Nat.
# we implicitly assert that ^Nat uniquely defines the Nat type, i.e.
@∀%{DefinedBy%(`NatA,^Nat)*DefinedBy%(`NatB,^Nat): Eq%(Type)(NatA,NatB) };
# if the compiler can't prove that it will complain and we'll have to help it

`Magma = < : __base__ = `T:Type; `op:T*T=>>T; >;
`Semigroup = <Magma: 
                `assoc : ∀%{T`x*T`y*T`z=>>Prop: 
                              op(x,op(y,z)) =% op(op(x,y),z) 
                            }; 
             >;
`Monoid = <Semigroup: 
              `unit:T; 
              `twoSidedUnit: ∀%{T`x=>>Prop: op(x,unit) =% x =% op(unit,x)
                                }; 
          >;

# NatWithAdd isEqual Nat. (Extra fields makes NatExt1 a subtype. However
# the fields are derived from Nat's definition so the reverse also applies)
`NatWithAdd:Type DefinedBy = <Nat:
    `addNat: Nat*Nat=>>Nat;
    addNat(``i,``j) = totalCase i of [
        {[Nat.zero]: j},
        {[Nat.succ `k]: Nat.succ(addNat(k,j))}
    ];
    `assocAddNat = @ ∀%{Nat`x*Nat`y*Nat`z=>>Prop: 
        op(x,addNat(y,z)) =% addNat(addNat(x,y),z) };
    `twoSidedUnit = @ ∀%{Nat`x=>>Prop: addNat(x,zero) =% x =% addNat(zero,x) };
    `ConformsToMonoid .add = @ < Monoid: T=Nat; op=addNat; assoc=assocAddNat;
                              unit=zero; twoSidedUnit=twoSidedUnitAddNat; >;
>;
`{(50)["+"](50)} (``x:``T,``y:T) = (T.ConformsToMonoid.add:Monoid).op(x,y);
# or we could just mention the operator then define it
# `{(50)["+"](50)}; (``x:``T)+(``y:T) = T.ConformsToMonoid.add.op(x,y);

`n0 = Nat.zero; `s = Nat.succ; # shorter names
# we actually need that n is zero or a successor
foreach j:Nat do
    add(n0, j) = j;
    foreach k:Nat do add(s k, j) = s add(k,j) od od;
# the compiler needs to know that this covers all cases, and no
# overlap. I.e. every Nat is n0 or s k for some k. This can be
# proved using Nat.induct with parameter
#  p={Nat`n =>> Type: Eq%(Nat)(n,n0) Or% ∃%{Nat`m=>Type:Eq%(Nat)(n,s m)}

`AssocAddNat = ∀%{ Nat`u*Nat`v*Nat`w => Prop:
                     add(add(u,v),w) =% add(u,add(v,w))
                 };
`assocAddNat:AssocAddNat;
assocAddNat = # toForAll% makes a witness for a ∀%
    toForAll% { Nat`u*Nat`v*Nat`w =>> AssocAddNat.at(u,v,w):
        # provide a witness for every $
        `ThisProp = AssocAddNat.at(u,v,w);
        # we need to return a witness for ThisProp
        assert ThisProp==((add(add(u,v),w) =% add(u,add(v,w))));
        # to create our witness, use induction on p
        `P:Nat=>>Prop;
        P = {Nat`x==>Prop: ∀%{Nat`y*Nat`z=>>Prop:
              add(x,add(y,z)) ==% add(add(x,y),z)} };
        `Premise0=P(n0);
        `premise0:Premise0;
        premise0 = toForAll% {Nat`y*Nat`z=>>P(n0).at(y,z):
                                   `lhs=add(n0,add(y,z))=add(y,z);
                                   `rhs=add(add(n0,y),z)=add(y,z);
                                   @(lhs =% rhs)
                                }; # and that was the easy bit
         `PremiseS = ∀%{'Nat=>Type: P($) Implies% P(s $) };
         `premiseS:PremiseS = toForAll% {Nat`n=>>PremiseS.at(n):
                P(n) Implies% P(s n) by {P(n)`pn=>>P(s n): 
                    assert Pn == ∀%{Nat`y*Nat`z=>>Prop: 
                        add(n,add(y,z)) ==% add(add(n,y),z)};
                    # we need to create a value of P(s n)
                    `m = s n; `Pm = P(m);
                    assert Pm = ∀%{Nat`y*Nat`z=>>Prop:
                        add(m,add(y,z)) =% add(add(m,y),z)} };
              # we need a value of type Pm
              `pm:Pm = toForAll% {'Nat`y*Nat`z=>>Prop:
                        `pnyz = pn.instance(y,z)
                                : add(n,add(y,z)) ==% add(add(n,y),z);
                        `spnyz = pnyz.bothSides(s) # apply s to both sides
                                 :( s(add(n,add(y,z)))==% s(add(add(n,y),z)
                               = add(s n,add(y,z))==% add(s(add(n,y)),z)
                               = add(m,add(y,z)) ==% add(add(s n,y),z)
                               = add(m,add(y,z)) ==% add(add(m,y),z);
                  `lhs = add(m,add(y,z))
                             = if m==n0 then { add(y,z) } 
                               else { m = s `k; s(add(k,add(y,z))) };
                        Nat.succNotZero(m=s n); # witness m=/=n0
                        lhs = (s n = s `k; s(add(k,add(y,z)));
                        succAdd2AddSucc.instance(n,add(y,z));
                        lhs = s (add(n,add(y,z)))
                            = add(s n,add(y,z));
                        rhs = add(add(s n,y),z)
                            = add(s(add(n,y)),z);
                        @spnyz
                    };
                    pm # completing our "P(n) implies% P(s n)"
                }
            # can now use premise0, premiseS and induct
            };
            `pInduct:`PInduct = Nat.induct.instance(P);
            `PAll = Nat.associative;
            # PAll is the type that we need a value of
            `P0PS = Premise0 And% PremiseS;
            `p0PS:P0PS = premise0 and% premiseS;
            PInduct = P0PS Implies% PAll;
            # we get a witness of PAll by giving a PInduct witness
            # a witness of P0PS
            pInduct.given(p0PS)
        }# QED
    };



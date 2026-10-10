%/include /home/rks/sw/wombat/wlib/wombat.wh


#`{(50)["+"](50)} (``x:``T,``y:T) = (T.ConformsToMonoid.add:Monoid).op(x,y);
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



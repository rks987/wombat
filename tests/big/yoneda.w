%/include  /home/rks/sw/wombat/wlib/wombat.wh
# The Yoneda Lemma

# For every type T, and x:T, y:T, there is a dependent type Eq%(T)(x,y) with at most
# one value. The value, when present, is a witness that x and y are equal. These equality
# types are a "proposition type" and any two values of it are equal (i.e. no higher
# equalities). Prop is the subtype of Type consisting of proposition types.
# What we need here is the definition of equality for total functions.
# We use * infix operator for Tuple types. Note, like ",", it is
# not associative. X*Y*Z = Tuple[X,Y,Z] not = (X*Y)*Z nor X*(Y*Z).
# Our TFunc closure has the form { X =>> Y : expression } where $ is the input, $:X.
# However if you don't like $ you can introduce an identifier { X`x =>> Y : expn }.
# Identifiers (apart from free ones) are prefixed with ` when used for the first time.
# Note that if X is a type, then X x is the same as x:X, but returns X not x.

#[since a TFunc isa Func, these equality definitions have to be compatible. However these
# are builtin, so only shown here for exposition. TFunc(X,Y) usually written X=>>Y.]

# a double backquote introduces a free identifier and places it in an implicit foreach.

`comp (``g:``Y=>>``Z,``f:``X=>>Y) ``x:X = g(f(x)); # read "compose g after f"
# meaning: foreach X:,Y:,Z:Type, g:Y=>>Z, f:X=>>Y, x:X do `comp(g,f)x = g(f(x)) 
# equivalent to: `comp={(`Y=>>`Z)`g*(`X=>>Y)`f =>> (X=>>Z): {X`x=>>Z:g(f(x))}}

# A structure does the work of a dependent pair, but has multiple interdependent
# named fields. It has form <optional-parent: expression >. It creates a type, a value of
# which has values for all the fields. Note this is the "noleft" use of "<".
# Note that types in wombat are more like sets in math/tla+ than most type systemss
# so we use types instead of sets in the folowing.

`Category = < :
    `O:Type; # objects
    `M:(O*O<=>>Type); # dependent type of morphisms
    # <=>> means invertible where the reverse is not usually total. 
    `id:(O`o<=>>M(o,o)); # there are identity morphisms for each object
    # NOTE comp(x,y) means x after y, like xoy in my math texts
    # In the following we implicitly define comp multiple times. This "combine"s
    # the definitions. We could do this as one definition of the Union of the
    # inputs to a dependent output.
    `comp:M(``y,``z)*M(``x,y)=>>M(x,z); # polymorphic -- implicit foreach
    #meaning: foreach x:O,y:O,z:O do `comp:M(y,z)*M(x,y)=>>M(x,z) od; # composition if compatible
    # =% is Eq% in the intersection of left and right types. No problem here
    # because they have the same type.
    # The ∀% (forall type) takes a TFunc that builds a type for each input.
    # -- a witness is then a TFunc that generates a witness for each inner type. 
    `rightId: ∀%{O`fr*O`to*M(fr,to)`m=>>Prop: Eq%(M(fr,to))(comp(m,id(to)),m) };
    `leftId: ∀%{O`fr*O`to*M(fr,to)`m=>>Prop:  Eq%(M(fr,to))(comp(id(fr),m),m) };
    `assoc: ∀%{M(`w,`x)`wx*M(x,`y)`xy*M(y,`z)`yz=>>Prop:
            comp(comp(yz,xy),wx) =% comp(yz,comp(xy,wx)) };
>;
# To create a category we need to provide values of those 6 fields.
# Generate the opposite (arrow-reversed) category
`Op = {Category`C=>>Category: @<Category: O=C.O; M(``o,``p)=C.M(p,o); id=C.id;
     comp (``yz:M(``y,``z),``xy:M(``x,y)) = C.comp(xy,yz);
     leftId = C.rightId; rightId = C.leftId; # ???
     # we can leave the output type of a closure, it is then deduced:
     assoc = toForAll% {M(`w,`x)`wx*M(x,`y)`xy*M(y,`z)`yz : C.assoc.at(yz,xy,wx) };
> };
# Though we provide a value for each component, our Structure remains a type, but
# with only one value. @ extracts the value of a type with only one.
# @ in front of suboperators returns the value of the type got without the @.
# So x @=% y returns the witness of x =% y or fails. A chain of @=% returns the
# witness of first to last. When x and y are expressions it returns a value of
# a type that will convert to the type for any example.
Op(Op ``C) = C; # we hope the compiler can prove it?

`TypeCat = # category of types and pure total functions (TFunc)
    @<Category:
        O = Type; # objects are types
        M = {O`X*O`Y<=>>Type: X=>>Y}; # morphisms are TFuncs
        id = {O`T<=>>M(T,T): {T`X=>>T: X}}; # id morphisms
        comp={M(`Y,`Z)`yz*M(`X,Y)`xy=>>M(X,Z): {X`x=>>Z:yz(xy(x))}};
        #leftId:∀%{O`fr*O`to=>>Prop: ∀%{M(fr,to)`m=>>Prop: comp(id(to),m) =% m } }
        leftId =toForAll% {M(`fr,`to)`m=>>Eq%(M(fr,to))(comp(id(to),m),m):
                    # we have to prove two functions equal. In general we have to
                    # follow the Eq%(TFunc(X,Y)) definition above. But first try
                    # to simplify, and that actually works
                    comp(id(to),m)
                         # apply definition of comp, yz=id(to), xy=m, X=Y=fr, Z=to
                         = {% apply comp }% {fr`x=>>to: m(id(to)x)}
                         = {% apply id }% {fr`x=>>to: m({fr`xx=>>fr:xx}x)}
                         = {% apply 2 {} }% {fr`x=>>to: m(x)} # but this is just m
                         = {% axiom unelaborate }% m; #our inner witness
                    comp(id(fr),m) @=% m # return witness
            }; # end of toForAll%, producing a forall witness
        # we hope that actually the compiler can prove that and the next 2 conditions.
        rightId = @∀%{M(`fr,`to)`f=>Prop:comp(f,id(fr)) =% f };
        assoc = @∀%{M(`w,`x)`wx*M(x,`y)`xy*M(y,`z)`yz=>>Prop:
                      comp(comp(yz,xy),wx) =% comp(yz,comp(xy,wx)) };
    >;
`Functor = <: # type of functors between categories
    `fr:Category;
    `to:Category;
    `oF:fr.O=>>to.O; # we need to map objects to objects
    # mF maps morphisms -- it needs to be polymorphic
    `mF:fr.M(`x,`y)=>>to.M(oF(x),oF(y));
    # our laws are preserve identity and composition
    `presI:∀%{ fr.O`o=>>Prop: mF(fr.id(o)) =% to.id(oF(o)) };
    `presC:∀%{ fr.m(`x,`y)`xy*fr.m(y,`z)`yz=>>Prop:
            mF(fr.comp(yz,xy)) =% to.comp(mF(yz),mF(xy)) };
>;
`NatTran = <: # type of natural transformations between functors
    `frC:Category; # curly A
    `toC:Category; # curly B
    `frF:<Functor: fr=frC; to=toC;>; # F -- subtype
    `toF:<Functor: fr=frC; to=toC;>; # G -- subtype
    `tran: frC.O`A=>>toC.M(frF.oF(A),toF.oF(A)); # alpha
    `natural: ∀%{frC.M(`x,`y)`f=>>Prop: # x y corresponds to A A'
                  frC.comp(tran(y),frF.mF(f)) =% toC.comp(toF.mF(f),tran(x)) };
>;
`FunctorCat (``C:,``D:Category) = @<Category:
    O = <Functor: fr=C; to=D>;
    M (``f:,``g:O) = <NatTran: frC=C; toC=D; frF=f; toF=g;>;
    id = {O`f<=>>M(f,f): @<M(f,f): tran={C.O`A=>>D.M(f.oF(A),f.oF(A)):D.id(f.oF(A))}; > };
    comp (``ntgh:M(``g,``h),``ntfg:M(``f,g)) = 
      @<M(f,h):
        tran = {C.O`A=>>D.M(frF.oF(A),toF.oF(A)):
                   D.comp(ntgh.tran(A),ntfg.tran(A)) };
      >; # leaving out the remaining fields tells the compiler to work them out.
>;
`Isomorphism% (``C:Category,``m:C.M(`o,`p)) = 
    ∃%{C.M(p,o)`n=>>Prop: C.comp(n,m)=%C.id(o) And% C.comp(m,n)=%C.id(p)};
# the following says that natural transformation is a natural isomorphism iff
# all the .tran are isomorphisms in the target.
`Lemma_1_3_11: NatTran `α =>> # Leinster page 31
    Isomorphism%(FunctorCat(α.frC, α.toC), α) Iff%
    ∀%{α.frC.O`A=>>Prop: Isomorphism%(α.toC, α.tran(A)) };
Lemma_1_3_11 ``α : NatTran = ( # we define some ids to be similar to Leinster
    `AA = α.frC; `BB = α.toC; `F = α.frF; `G = α.toF;
    `FC=FunctorCat(AA,BB);
    `LtoR = toImplies% 
        {Isomorphism%(FC, α)`inat =>> ∀%{AA.O`A=>>Prop: Isomorphism%(BB, α.tran(A))}:
            # inat is an "exists" so we pick one - our inverse∴
            (`β , `isInv) = inat.pickOne;
            β : <NatTran: frC=AA; toC=BB; frF=G; toF=F;>;
            # isInv says that the comps are identities
            isInv: FC.comp(β : FC.M(G,F), α : FC.M(F,G)) =% FC.id(F) And% 
                   FC.comp(α , β) =% FC.id(G);
            `left1 = FC.comp(β : FC.M(G,F), α : FC.M(F,G)) = {% apply FC.comp }% 
              @<FC.M(F,F): tran = {AA`A=>>BB.M(F.oF(A),F.oF(A)):
                                     AA.comp(G.tran(A),F.tran(A)) }; >;
            `left2 = FC.comp(β , α) = {% apply FC.comp }% 
              @<FC.M(G,G): tran = {BB`B=>>AA.M(G.oF(B),G.oF(B)):
                                     BB.comp(F.tran(B),G.tran(B)) }; >;
            `right1 = FC.id(F) = {% apply FC.id }% 
              @<FC.M(F,F): tran={AA`A=>>BB.M(F.oF(A),F.oF(A)):AA.id(AA.oF(A))}; >;
            `right2 = FC.id(G) = {% apply FC.id }% 
              @<FC.M(G,G): tran={BB`B=>>AA.M(G.oF(B),G.oF(B)):BB.id(BB.oF(B))}; >;
            isInv.left = (left1 @=% right1);
            {% axiom componentsEqual }% left1.tran = right1.tran;
            {% axiom equalClosures }% 
            `l2r1 = @∀%{AA`A: AA.comp(G.tran(A),F.tran(A)) =% AA.id(AA.oF(A))};
            # we hope the compiler can do it all by itself
            `l2r2 = @∀%{AA`A: AA.comp(F.tran(A),G.tran(A)) =% AA.id(BB.oF(B))};
            l2r1 and% l2r2 = {% axiom combineInnerForAll }%
              @∀%{AA`A: AA.comp(G.tran(A),F.tran(A)) =% AA.id(AA.oF(A)) And%
                        BB.comp(F.tran(A),G.tran(A)) =% BB.id(BB.oF(B)) }
              = {% reverseApply Isomorphism% }% 
                    @∀%{AA.O`A=>>Prop: Isomorphism%(BB, α.tran(A)) }
        };
    `RtoL = toImplies% 
        {(∀%{AA.O`A=>>Prop: Isomorphism%(BB, α.tran(A)) })`allIso =>> Isomorphism%(FC, α)`rslt:
            rslt : (Isomorphism%(FC, α) = {% apply Isomorphism% }%
                ∃%{FC.M(G,F)`β =>> Prop: FC.comp(β , α)=%FC.id(F) And% FC.comp(α , β)=%FC.id(G)});
            `β : FC.M(G,F); # we prove exists by constructing this 
            β : <NatTran: frC=AA; toC=BB; frF=G; toF=F;>; # need tran and natural
            β.tran =
              {AA.O`A=>>toC.M(G.oF(A),F.oF(A)):
                (`betaA, `isInvA) = allIso.at(A).pickOne; # betaA is inverse of α.tran(A)
                betaA # result
              };
            # we omit the fairly trivial (but too hard for me) proof
            # see exercise 1.3.26 in https://positron0802.wordpress.com/wp-content/uploads/2021/01/category-0-1-leinster.pdf
            β.natural = @∀%{AA.M(`x,`y)`f=>>Prop:AA.comp(G.tran(y),G.mF(f))=%BB.comp(F.mF(g).F.tran(x))};
        };
    LtoR and% RtoL;
);

# HomFunctor takes an object in a category and returns a Functor
# subtype from the category to TypeCat. I.e. it is a dependent type.
foreach C:Category, a:C.O do `HomFunctor C a =
    @<Functor:
        fr = C;
        to = TypeCat;
        oF = {C.O`o=>>Type: C.M(a,o)}; # since Prop=TypeCat.O
        mF = {C.M(`x,`y)`xy=>>(C.M(a,x)=>>C.M(a,y)):
               #`xy is a morphism x to y, need a TFunc morphism
               {C.M(a,x)`ax=>>C.M(a,y): C.comp(xy,ax) } }; # go a to x, x to y
        # before we calculate presI, we calculate and name its inner type
        foreach o:C.O do PresIo o = mF(fr.id(o)) =% to.id(oF(o))
               = {% apply to.id }% Eq%(Type=>>Type)(mF(C.id(o)),oF(o)) od;
        presI ``o:C.o = toForAll% 
          {C.O`co=>>(PresIo co):
            mF(C.id(o)) 
              = {% apply mF }% {C.M(a,o)`ao=>>C.M(a,o): C.comp(ao,C.id(o))}
                        = {C.M(a,o)`ao=>>C.M(a,o):
                              # now we construct a witness that C.comp(ao,C.id(o))=ao
                              C.rightId.given(a,o).given(ao):C.comp(ao,C.id(o)) =% ao;
                              ao }
                        # we hope the compiler can use Eq%(Type=>Type)'s definition
                        = TypeCat.id(C.M(a,o));
             ``:PresIo o };
        #forall x:,y:,z:C.O do
        #    PresC(x,y,z) = ∀%{fr.M(x,y)`xy*fr.M(y,z)`yz=>Prop:
        #         mF(fr.comp(xy,yz)) =% to.comp(mF(xy),mF(yz)) } od;
        presC = toForAll% {C.O`x*C.O`y*C.O`z=>(PresC (x,y,z)):
                    toForAll% {fr.M(x,y)`xy*fr.M(y,z)`yz=>(PresC(x,y,z).at(xy,yz)):
                        `lhs = mF(fr.comp(xy,yz)); `rhs = to.comp(mF(xy),mF(yz));
                        # we want a witness for lhs=%rhs. Apply mF!
                        rhs = to.comp({C.M(a,x)`ax=>C.M(a,y): C.comp(ax,xy)},
                                      {C.M(a,y)`ay=>C.M(a,z): C.comp(ay,yz)})
                            = {C.M(a,x)`ax=>C.M(a,z): C.comp(C.comp(ax,xy),yz) }
                            # apply associativity
                            = {C.M(a,x)`ax=>C.M(a,z): 
                                    {% TypeCat.assoc.at(a,x,y,z).at(ax,xy,yz) }%
                                    C.comp(ax,C.comp(xy,yz)) }
                            = lhs;
                        @(lhs =% rhs) } };
     > # return a HomFunctor value
 od;
# Leinster theorem 4.2.1 p.94
# We follow the proof on p.96. Cursive A becomes AA, 
# roman A becomes lowercase a.
`yoneda ``AA:Category = @ < :
  # This has two parts. The yoneda construction specifies the two functions
  # in which a and X are arguments, and the assertion that they are inverses.
  # The 2nd part looks at the partial functions and shows they are natural.
  `YonedaConstruction (``a:AA.O, ``X:FunctorCat(Op(AA),TypeCat)) = @ <
    # we define functions yt (yoneda to) and yf (yoneda from) for Leinster's ^ & ~}
    `HA = HomFunctor AA;
    `MyFuncCat = <FunctorCat:C=AA;D=TypeCat; > ;
    HA ``a:Op(AA) : MyFuncCat.M(Op(AA),TypeCat);
    `yt = {FunctorCat(Op(AA),TypeCat).M(HA a, X)=>X.O.oF(a):
              $=`alpha:<Natran:frC=Op(AA);toC=TypeCat;frF=HA a; toF=X.O;>;
              # AA.id(a) is in HomFunctor AA a, alpha.tran is an M in the X category
              alpha.tran:AA.O=>(TypeCat.M((HA a).oF($),X.O.oF($))
                                = AA.M($,a)=>X.O.oF($));
              alpha.tran(a)(AA.id(a))
         };
   `yf = {X.O.oF(a)=>FunctorCat(Op(AA),TypeCat).M(HA a, X):
              $ = `x; # now need a NatTran HA a to X.
              `RsltType=<Natran:frC=Op(AA);toC=TypeCat;frF=HA a; toF=X; > ;
              # to get rslt we need to define tran and natural
              rTran: Op(AA).O=>( frF.oF($)=>toF.oF($)
                                 = AA.M($,a)=>X.O.oF($) ); #reverse A.M since Op
              rTran = {AA.O`b=>(AA.M(b,a)=>X.O.oF(b)): `x=X.O.oF(a);
                           {AA.M(b,a)=>X.O.oF(b): $=`f;
                                X.O.mF:Op(AA).M(``p,``q)=>(X.O.oF(p)=>X.O.oF(q));
                                X.M.tran(f)(x)
                           } #???
                      };
              RNatural=∀%{Op(AA).O*Op(AA).O=>Prop: $=(`p,`q); # naturality condition
               ∀%{Op(AA).M(x,y)=>Prop: $=`f; `Fm=Op(AA).frF.mF; `Gm=toF.mF;
                 Op(AA).comp(tran(y),Fm(f)) =% TypeCat.comp(Gm(f),tran(x)) } };
              @ < RsltType: tran=rtran; natural=@RNatural; > ;
          };
    `yIso = @Isomorphism%( FunctorCat(Op(AA),TypeCat).M(HomFunctor AA a, X),
                           X.oF(a));
  > ;
  `YonedaLemma = @`Ynata and% @`YnatX;
  Ynata = ∀%{AA.O*AA.O=>Prop: $=(`a,`b);
              ∀%{FunctorCat(Op(AA),TypeCat)=>Prop: $=`X;
                  `yCa = YonedaConstruction(a,X);
                  `yCb = YonedaConstruction(b,X);
                  ∀%{AA.M(b,a)=>Prop: $=`f;
                      `Hf = (HA a).mF(f); # Leinster top p 98
                      `topArrow = {MyFuncCat.M(HA a,X)=>MyFuncCat.M(HA b,X):
                                    MyFuncCat.comp($,Hf) };
                      `rightArrow = yCb.yt;
                      `leftArrow = yCa.yt;
                      `botArrow = X.mF(f);
                      comp(topArrow,rightArrow)=%comp(leftArrow,botArrow)
                   }
            };
      };
  YnatX = unit; #left as an exercise for the reader
#Proving Ynata and YnatX is left as an exercise for the compiler.
>

# This will follow Leinster "Basic Category Theory" in a more
# controlled way. Notational equivalence will be documented
# (A) Wombat types are designed to behave like math sets. There is
#     Set type, but we mostly use "Type" where Leinster says "set".
# (B) curly capitals become double capitals. curly-A becomes AA.
#     Also, we capitalise names of Types 
# (C) Properties given as procedures will be switched to atom access
#     1st case: ob(A) becomes A.Ob
#
# p.10
`Category = < :
    `Ob:Type; # objects
    `M:(Ob*Ob<=>>Type); # type of morphisms.
    # (D) for category AA, Leinster writes AA.M(X,Y) as AA(X,Y). We
    # therefor arrange a conversion from AA to AA.M below
    `id:(Ob`o<=>>M(o,o)); # there are identity morphisms for each object
    # (E) AA.id(A) corresponds to Leinster's 1-subscript-A
    `comp:M(``y,``z)*M(``x,y)=>>M(x,z); # polymorphic -- implicit foreach
    `associativity: ∀%{M(`w,`x)`wx*M(x,`y)`xy*M(y,`z)`yz=>>Prop:
            comp(comp(yz,xy),wx) =% comp(yz,comp(xy,wx)) };
    `identityLaws: ∀%{O`fr*O`to*M(fr,to)`m=>>Prop: comp(m,id(to)) =% m =% comp(id(fr),m) };
>;
Category``AA convertsTo AA.M by {Category`AA=>>((AA.Ob`A*AA.Ob`B)=>>AA.M) : 
                                    {(AA.Ob`A*AA.Ob`B)=>>AA.M: AA.M(A,B)}};
# The Category``A in a convertsTo translates to:
# foreach AA:Category do Category//{: $ =% AA} convertsTo AA.M by ... etc...

# p.11

# Comment (c) is covered by the reverse arrow on the definition of M

# p.12

`Isomorphism (``AA:Category) (``f:AA.M(``A,``B)) = 
    ∃%{AA.M(B,A)`g=>>Prop: AA.comp(f,g) =% AA.id(B) And% AA.comp(g,f) =% AA.id(A)};

`{(9)["≅"](9)};  (``A ≅ ``B)  = Isomorphism _ (A,B);

# p.16
# construction 1.1.9
# To create a category we need to provide values of those 6 fields.
# Generate the opposite (arrow-reversed) category
`Op = {Category`AA=>>Category: @<Category: Ob=AA.Ob; M(``A,``B)=AA.M(B,A); id=AA.id;
     comp (``yz:M(``y,``z),``xy:M(``x,y)) = AA.comp(xy,yz);
     identityLaws = toForall% {O`fr*O`to*M(fr,to)`m=>>Prop: AA.identityLaws.at(to,fr,M(to,fr))}
     # we can leave the output type of a closure, it is then deduced:
     associativity = toForAll% {M(`w,`x)`wx*M(x,`y)`xy*M(y,`z)`yz : AA.associativity.at(yz,xy,wx) };
> };

`inverseProp ``f:(``AA:Category).M(``A,``B) =  AA.M(B,A)``g=>>(AA.comp(g,f)=%AA.id(A) And% 
                                                               AA.comp(f,g)-%AA.id(B));
`exercise_1_1_13 = @(inverseProp ``f ``g And% inverseProp f ``h Implies% g =% h);

`ProductCat ``AA:,``BB:Category =
    @<Category:
        Ob = AA.Ob * BB.Ob;
        M = {Ob(`A1,`B1)*Ob(`A2,`B2)<=>>Type: AA.M(A1,A2) * BB.M(B1,B2)};
        id = {Ob(`A,`B)<=>>M(Ob(A,B),Ob(A,B)): AA.id(A,A),BB.id(B,B)};
        # leaving out the laws invites the compiler to prove them
    >;
`{(9)×(9)} = ProductCat; # This should be a general non-assoc product for a magma

# wombat types are intended to closely follow the way "set"s are used in maths
# (and TLA+). So TypeCat corresponds closely to sets and functions.
`TypeCat = # category of types and pure total functions (TFunc)
    @<Category:
        Ob = Type; # objects are types
        M = {Ob`X*Ob`Y<=>>Type: X=>>Y}; # morphisms are TFuncs
        id = {Ob`T<=>>M(T,T): {T`X=>>T: X}}; # id morphisms
        comp={M(`Y,`Z)`yz*M(`X,Y)`xy=>>M(X,Z): {X`x=>>Z:yz(xy(x))}};
        # we again leave the laws for the compiler to figure or complain
    >;

`Injective ``f:``X=>>``Y =  ∃%{(X<=>>Y)`f'=>Prop: f =% f'}; # same after conversion
`Surjective ``f:``X=>>``Y =  ∀%{ Y`y=>>Prop: ∃%{ X`x=>>Prop: f(x) =% y }};

# p.17
`Functor = <: # type of functors between categories
    `FR:Category;
    `TO:Category;
    # we use oF and mF instead of F for both
    `oF:FR.Ob=>>TO.Ob; # we need to map objects to objects
    # mF maps morphisms -- it needs to be polymorphic
    `mF:FR.M(`A,`A')=>>TO.M(oF(A),oF(A'));
    # our laws are preserve identity and composition
    `presI:∀%{ FR.Ob`o=>>Prop: mF(FR.id(o)) =% TO.id(oF(o)) };
    `presC:∀%{ FR.m(`x,`y)`xy*FR.m(y,`z)`yz=>>Prop:
            mF(FR.comp(yz,xy)) =% TO.comp(mF(yz),mF(xy)) };
>;

# p.24
`presheaf (``AA:Category) = <Functor: FR=Op(AA); TO=TypeCat;>;

`FaithfulFunctor ``F:Functor = Injective F.mF;
`FullFunctor ``F:Functor = Surjective F.mF;

# note that in the following S and S' auto convert from SS.Ob to AA.Ob
`SubCategory ``SS:,``AA:Category = Isa%(SS.Ob,AA.Ob) And% 
      ∀%{ SS.Ob`S*SS.Ob`S'=>>Prop: Isa%(SS.M(S,S'),AA.M(S,S'))};

`FullSubcategory ``SS:,``AA:Category = Subcategory SS,AA And% 
      ∀%{ SS.Ob`S*SS.Ob`S'=>>Prop: SS.M(S,S') =% AA.M(S,S') };

# p.28

`NatTran = <: # type of natural transformations between functors
    `frC:Category; # curly A
    `toC:Category; # curly B
    `frF:<Functor: fr=frC; to=toC;>; # F -- subtype
    `toF:<Functor: fr=frC; to=toC;>; # G -- subtype
    `tran: frC.O`A=>>toC.M(frF.oF(A),toF.oF(A)); # alpha
    `natural: ∀%{frC.M(`x,`y)`f=>>Prop: # x y corresponds to A A'
                  frC.comp(tran(y),frF.mF(f)) =% toC.comp(toF.mF(f),tran(x)) };
>;

# p.30

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

`{["`["]()["]"]} = FunctorCat; # so can write `[AA,BB] -- [] is already in use

# We need an Exponentiation structure type, then make a FunctorCat implementation thereof
# to allow us to write BB^AA

# p.31
`Isomorphism% (``C:Category,``m:C.M(`o,`p)) = 
    ∃%{C.M(p,o)`n=>>Prop: C.comp(n,m)=%C.id(o) And% C.comp(m,n)=%C.id(p)};
# the following says that natural transformation is a natural isomorphism iff
# all the .tran are isomorphisms in the target.
`Lemma_1_3_11_Type = NatTran `α =>> # Leinster page 31
    Isomorphism%(FunctorCat(α.frC, α.toC), α) Iff%
    ∀%{α.frC.O`A=>>Prop: Isomorphism%(α.toC, α.tran(A)) };
`Lemma_1_3_11 = @Lemma_1_3_11_Type; # compiler please prove


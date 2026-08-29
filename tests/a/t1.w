%/token Comment 100 #(?P<token>.*)

# a NewOperator maps a use to a procedure call
%/token NewOperator 200 `{(?P<token>.*?)}
# a ValueOperator maps an operator definition with no operands to a value
%/token ValueOperator 200 ``{(?P<token>.*?)}
# special tokens starting with $ go here at higher priority
%/token Identifier 200 (?P<token>\$builtin)
%/token Pragma 200 {%(?P<token>.*?)}%
%/token Identifier 100 (?P<token>[a-zA-Z\u0370-\u03ff\u1f00-\u1ffe][_a-zA-Z0-9\u0370-\u03ff\u1f00-\u1ffe]*'*[%?]?)
%/token NewIdentifier 100 `(?P<token>[a-zA-Z\u0370-\u03ff\u1f00-\u1ffe][_a-zA-Z0-9\u0370-\u03ff\u1f00-\u1ffe]*'*[%?]?)
%/token NewFreeIdentifier 100 ``(?P<token>[a-zA-Z0-9\u0370-\u03ff\u1f00-\u1ffe]+'*[%?]?)
%/token Literal 100 (?P<token>"(\\"|\\\\|[^"\\])*")
%/token Literal 100 (?P<token>[0-9]+(\.[0-9]+)?)
%/token Literal 100 (?P<token>\.[a-zA-Z\u0370-\u03ff\u1f00-\u1ffe][_a-zA-Z0-9\u0370-\u03ff\u1f00-\u1ffe]*'*[%?]?)
%/token MCTcmd 300 %\^(?P<token>[^# within the structure definition, Nat refers to the implementing type
`Nat:Type definedBy < Equality(Nat): # equality from implementing type
       `zero:Nat;
       `succ:Nat<=>>Nat; # TEmbed, backwards fails for zero.
       `succNotZero:∀%{Nat`n=>>Prop:Neq%(Nat)(succ n,zero)};
       `induct:∀%{(Nat=>>Prop)`p=>>Prop:
           (p(zero) And% ∀%{Nat`n=>>Prop: p(n) Implies% p(succ n)})
           Implies% ∀%{Nat`n=>>Prop: p(n)} };
       `IsDistinguishable = <Distinguishable(Nat): ... >
    > ; creates a $DefinedBy%(Nat, <...>) proposition witness
Eq%(Nat) = Nat.IsDistinguihable.Eq%;
# We can access Nat's defining structure type as ^Nat.
# we implicitly assert that ^Nat uniquely defines the Nat type, i.e.
@∀%{DefinedBy%(`NatA,^Nat)*DefinedBy%(`NatB,^Nat): Eq%(Type)(NatA,NatB) };
# if the compiler can't prove that it will complain and we'll have to help it

`Magma = < : __base__ = `T:Type; `op:T*T=>>T; >;
`Semigroup = <Magma: 
                `assoc : ∀%{T`x*T`y*T`z=>>Prop: 
                              op(``x,op(``y,``z)) =% op(op(x,y),z) 
                            }; 
             >;
`Monoid = <Semigroup: 
              `unit:T; 
              `twoSidedUnit: ∀%{T`x=>>Prop: op(``x,unit) =% x =% op(unit,x)
                                }; 
          >;
\n]*)\n?

# f x
%^operator ProcedureCall (100) [" "] (200)
# f(x)
%^operator ProcedureCall (100) [""] (200)
%^operator Semicolon (2) [";" repeating1 prepend associative](2)
%^operator Equal (19) ["="] (19)

$builtin.Type
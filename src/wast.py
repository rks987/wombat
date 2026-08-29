import operator
import functools
from typing import List, Tuple, Dict, Optional, Any, Union, Iterable, cast

def ppFix(lines: List[str], indent: int) -> List[str]:
    if sum((len(l) - indent) for l in lines) < 40:
        return [' ' * indent + functools.reduce(operator.add, (l.strip() + ' ' for l in lines))]
    return lines

# closure field should now be closure|structure|file
class AstNode:
    parent: Optional['AstNode']
    closure: Optional['AstClosure']
    fixed: bool
    upChain: Tuple['AstNode', ...]
    filename: Optional[str]
    start_line: Optional[int]
    start_col: Optional[int]
    end_line: Optional[int]
    end_col: Optional[int]

    def __init__(self, parent: Optional['AstNode'] = None, closure: Optional['AstClosure'] = None) -> None:
        self.parent = parent
        self.closure = closure
        self.fixed = False
        self.filename = None
        self.start_line = None
        self.start_col = None
        self.end_line = None
        self.end_col = None

    def fixUp(self, parent: Optional['AstNode'], closure: Optional['AstClosure'], upChain: Tuple['AstNode', ...]) -> None:
        if self.fixed:
            pass
        self.fixed = True
        self.parent = parent
        self.closure = closure
        assert self not in upChain, "Circular reference in upChain"
        self.upChain = upChain

    def gotClRslt(self) -> bool:
        return False


    def __str__(self) -> str:
        raise NotImplementedError("Must be overridden")

    def pp(self, indent: int = 1) -> List[str]:
        return [(' ' * indent) + str(self)]

class AstTuple(AstNode):
    members: Tuple[AstNode, ...]
    is_associative: bool

    def __init__(self, members: Union[Tuple[AstNode, ...], AstNode], parent: Optional['AstNode'] = None, closure: Optional['AstClosure'] = None, is_associative: bool = False) -> None:
        self.members = (members,) if isinstance(members, AstNode) else members
        assert isinstance(self.members, tuple)
        self.is_associative = is_associative
        super().__init__(parent, closure)

    def __str__(self) -> str:
        if not self.members:
            return '()'
        rslt = '(' + ''.join(str(x) + ',' for x in self.members)
        return rslt[:-1] + ')'

    def gotClRslt(self) -> bool:
        return any(e.gotClRslt() for e in self.members)

    def pp(self, indent: int = 1) -> List[str]:
        if not self.members:
            return [' ' * indent + '()']
        elif len(self.members) == 1:
            return ppFix([' ' * indent + '('] + 
                         self.members[0].pp(2 + indent) + 
                         [' ' * indent + ')'], indent)
        else:
            mppl = [m.pp(indent + 1) for m in self.members]
            for i in range(len(mppl) - 1):
                mppl[i][-1] += ' ,'
            combined = functools.reduce(operator.add, mppl)
            return ppFix([' ' * indent + '('] + combined + [' ' * indent + ')'], indent)

    def fixUp(self, parent: Optional['AstNode'], closure: Optional['AstClosure'], upChain: Tuple['AstNode', ...]) -> None:
        super().fixUp(parent, closure, upChain)
        for x in self.members:
            x.fixUp(self, closure, self.upChain + (self,))

def zeroTuple() -> AstTuple:
    return AstTuple(members=())

def toClosure(exprL: List[AstNode]) -> 'AstClosure':
    if len(exprL) == 4:
        return AstClosure(expr=exprL[3], domain=exprL[0], arrow=exprL[1], codomain=exprL[2])
    if len(exprL) == 2:
        return AstClosure(expr=exprL[1], domain=exprL[0])
    assert len(exprL) == 1 and isinstance(exprL[0], AstNode)
    return AstClosure(expr=exprL[0])

class AstClosure(AstNode):
    expr: AstNode
    myIds: Dict[str, List[AstNode]]
    extIds: Dict[str, List[AstNode]]
    is_struct_scope: bool
    domain: Optional[AstNode]
    arrow: Optional[AstNode]
    codomain: Optional[AstNode]

    def __init__(self, expr: AstNode, parent: Optional['AstNode'] = None, closure: Optional['AstClosure'] = None, is_struct_scope: bool = False,
                 domain: Optional[AstNode] = None, arrow: Optional[AstNode] = None, codomain: Optional[AstNode] = None) -> None:
        super().__init__(parent, closure)
        self.expr = expr
        self.domain = domain
        self.arrow = arrow
        self.codomain = codomain
        self.myIds = {}
        self.extIds = {}
        self.is_struct_scope = is_struct_scope
        breakpoint()
        if not is_struct_scope and not self.expr.gotClRslt():
            #eqProcParam = AstTuple((AstIdentifier("equal"), AstTuple((AstClRslt(), self.expr))))
            self.expr = AstEqual(AstTuple((AstClRslt(), self.expr)))

    def __str__(self) -> str:
        if self.domain is not None:
            if self.arrow is not None:
                arrow_str = self.arrow.const.strip('"') if isinstance(self.arrow, AstLiteral) else str(self.arrow).strip()
                dom_str = str(self.domain).strip()
                codom_str = str(self.codomain).strip() if self.codomain is not None else ""
                return f'{{{dom_str} {arrow_str} {codom_str} : {self.expr}}}'
            else:
                dom_str = str(self.domain).strip()
                return f'{{{dom_str} : {self.expr}}}'
        return f'{{{str(self.expr)}}}' #AstTuple((AstClRslt(), self.expr))}}'

    def pp(self, indent: int = 1) -> List[str]:
        if self.domain is not None:
            if self.arrow is not None:
                arrow_str = self.arrow.const.strip('"') if isinstance(self.arrow, AstLiteral) else str(self.arrow).strip()
                dom_str = str(self.domain).strip()
                codom_str = str(self.codomain).strip() if self.codomain is not None else ""
                header = f"{dom_str} {arrow_str} {codom_str} :"
            else:
                dom_str = str(self.domain).strip()
                header = f"{dom_str} :"
            return ppFix([' ' * indent + '{ ' + header] + self.expr.pp(indent + 2) + [' ' * indent + '}'], indent)
        return ppFix([' ' * indent + '{'] + self.expr.pp(indent + 2) + [' ' * indent + '}'], indent)

    def fixUp(self, parent: Optional['AstNode'], closure: Optional['AstClosure'], upChain: Tuple['AstNode', ...]) -> None:
        super().fixUp(parent, closure, upChain)
        if self.domain is not None:
            self.domain.fixUp(self, self, upChain + (self,))
        if self.arrow is not None:
            self.arrow.fixUp(self, self, upChain + (self,))
        if self.codomain is not None:
            self.codomain.fixUp(self, self, upChain + (self,))
        self.expr.fixUp(self, self, upChain + (self,))

        
        if closure is not None:
            for id_name in self.extIds:
                if id_name not in closure.extIds and id_name not in closure.myIds:
                    closure.extIds[id_name] = [self]
                elif id_name in closure.extIds:
                    closure.extIds[id_name].append(self)
                else:
                    closure.myIds[id_name].append(self)

###class AstFileAsClosure(A.AstClosure):
###    def __init__(self, expr: AstNode) -> None:
###        super().__init__(expr)
###        self.myIds = {k: [] for k, v in builtins.items()}
###        self.extIds = {}

class AstClParam(AstNode):
    def __str__(self) -> str:
        return '$'

class AstClRslt(AstNode):
    def gotClRslt(self) -> bool:
        return True

    def __str__(self) -> str:
        return '`$'

class AstIdentifier(AstNode):
    identifier: str
    introduce: Tuple[AstNewIdentifier,bool]|AstNewFreeIdentifier#|AstForeach

    def __init__(self, identifier: str, parent: Optional['AstNode'] = None, closure: Optional['AstClosure'] = None) -> None:
        super().__init__(parent, closure)
        self.identifier = identifier

    def fixUp(self, parent: Optional['AstNode'], closure: Optional['AstClosure'], upChain: Tuple['AstNode', ...]) -> None:
        super().fixUp(parent, closure, upChain)
        if closure is not None:
            id_name = self.identifier
            if id_name in closure.myIds:
                closure.myIds[id_name].append(self)
            else:
                if id_name not in closure.extIds:
                    closure.extIds[id_name] = [self]
                else:
                    closure.extIds[id_name].append(self)

    def __str__(self) -> str:
        return f'{self.identifier} '

#class AstForeach(AstNode):
#    pass
class AstNewIdentifier(AstIdentifier):
    #identifier: str

    def __init__(self, identifier: str, parent: Optional['AstNode'] = None, closure: Optional['AstClosure'] = None) -> None:
        super().__init__(parent, closure)
        self.identifier = identifier

    def fixUp(self, parent: Optional['AstNode'], closure: Optional['AstClosure'], upChain: Tuple['AstNode', ...]) -> None:
        super().fixUp(parent, closure, upChain)
        if closure is not None:
            id_name = self.identifier
            if id_name in closure.myIds:
                #breakpoint()
                print(f"DUPLICATE identifier found in closure: {id_name} at {self.filename} {self.start_line}/{self.start_col}")
                closure.myIds[id_name].append(self)
            else:
                closure.myIds[id_name] = [self]

    def __str__(self) -> str:
        return f'`{self.identifier} '

###class AstFreeIdentifier(AstNode):
###    identifier: str
###
###    def __init__(self, identifier: str, parent: Optional['AstNode'] = None, closure: Optional['AstClosure'] = None) -> None:
###        super().__init__(parent, closure)
###        self.identifier = identifier
###
###    def __str__(self) -> str:
###        return f'_{self.identifier} '

class AstNewFreeIdentifier(AstIdentifier):
    #identifier: str
    uses: List[AstIdentifier]
    allFree: List[AstNewFreeIdentifier] = [] # remember all for easy fix

    def __init__(self, identifier: str, parent: Optional['AstNode'] = None, closure: Optional['AstClosure'] = None) -> None:
        super().__init__(parent, closure)
        self.identifier = identifier
        AstNewFreeIdentifier.allFree.append(self)

    def __str__(self) -> str:
        return f'`_{self.identifier} '

class AstCall(AstNode):
    procParam: AstTuple

    def __init__(self, procParam: AstTuple, parent: Optional['AstNode'] = None, closure: Optional['AstClosure'] = None) -> None:
        super().__init__(parent, closure)
        self.procParam = procParam

    def __str__(self) -> str:
        return f'CALL{self.procParam}'

    def funct(self) -> AstNode:
        return self.procParam.members[0]

    def param(self) -> AstNode:
        return self.procParam.members[1]

    def pp(self, indent: int = 1) -> List[str]:
        f = self.funct().pp(indent)
        f[-1] += '('
        return ppFix(f + self.param().pp(indent + 2) + [' ' * indent + ')'], indent)

    def fixUp(self, parent: Optional['AstNode'], closure: Optional['AstClosure'], upChain: Tuple['AstNode', ...]) -> None:
        super().fixUp(parent, closure, upChain)
        funct_node = self.funct()
        if isinstance(funct_node, AstIdentifier) and funct_node.identifier in ['StructureType', 'StructureInstance']:
            struct_closure = AstClosure(expr=self.procParam, parent=self, closure=closure, is_struct_scope=True)
            struct_closure.fixed = True
            struct_closure.upChain = self.upChain + (self,)
            self.procParam.fixUp(self, struct_closure, self.upChain + (self,))
        else:
            self.procParam.fixUp(self, closure, self.upChain + (self,))

    def gotClRslt(self) -> bool:
        return self.procParam.gotClRslt()

def callOp(procAndParam: Tuple[AstNode, AstNode]) -> AstCall:
    return AstCall(procParam=AstTuple(members=procAndParam))

class AstLiteral(AstNode):
    const: str
    constType: Optional[str]

    def __init__(self, const: str, constType: Optional[str], parent: Optional['AstNode'] = None, closure: Optional['AstClosure'] = None) -> None:
        super().__init__(parent, closure)
        self.const = const
        self.constType = constType

    def __str__(self) -> str:
        return f'{self.const} '

class AstEqual(AstNode):
    pass
###class AstPrim(AstNode):
###    primVal: Any
###
###    def __init__(self, primVal: Any, parent: Optional['AstNode'] = None, closure: Optional['AstClosure'] = None) -> None:
###        super().__init__(parent, closure)
###        self.primVal = primVal
###
###    def __str__(self) -> str:
###        return str(self.primVal)

#def first2rest(tupNodeOrList: Optional[Union[AstTuple, Tuple[AstNode, ...]]]) -> Optional[Union[AstTuple, Tuple[AstNode, ...]]]:
#    if tupNodeOrList is None:
#        return None
#    if isinstance(tupNodeOrList, AstTuple):
#        members_rest = first2rest(tupNodeOrList.members)
#        if isinstance(members_rest, tuple):
#            return AstTuple(members=members_rest)
#        return AstTuple(members=members_rest.members if members_rest else ())
#    
#    t0 = tupNodeOrList[0]
#    t1 = tupNodeOrList[1]
#    if isinstance(t1, AstTuple):
#        return (t0,) + t1.members
#    return (t0,) + tuple(t1)

###def set_parents(node, parent=None):
###    if node is None:
###        return
###    node.parent = parent
###    if isinstance(node, AstTuple):
###        for m in node.members:
###            set_parents(m, node)
###    elif isinstance(node, AstCall):
###        set_parents(node.procParam, node)
###    elif isinstance(node, AstClosure):
###        set_parents(node.expr, node)
###        set_parents(node.domain, node)
###        set_parents(node.arrow, node)
###        set_parents(node.codomain, node)
###

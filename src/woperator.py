# operator.py

# build operator datastructure from operator commands
# support getExpr with operator related code

import collections as C
import utility as U
import wast as A
import lexer
import regex as re
import decimal

from typing import NamedTuple, List, Dict, Tuple, Optional, Any, Union, Iterator, Iterable, cast
from dataclasses import dataclass, field

@dataclass
class SSparam:
    precedence: Optional[decimal.Decimal]
    pos: int
    #oneAdjust: Any
    ssParamLen: int
    subsubs: Optional[List[Any]] # List of SSsubop
    keyword: Optional[str] = None

@dataclass
class SSsubop:
    subop: List[str]
    occur: str
    #allAdjust: Any
    v: Dict[str, Any]
    prepend: bool = False
    associative: bool = False

@dataclass
class OpInfo:
    left: Optional[SSparam]
    astFun: Any
    paramLen: int
    subops: List[SSsubop]

noLeft: Dict[Any, Any] = {}
withLeft: Dict[Any, Any] = {}

def getKeyTuple(subops: List[SSsubop]) -> Tuple[Any, ...]:
    kt0: Tuple[Any, ...] = () # zero tuple
    if subops[0].occur in ["mandatory", "repeating1"]:
        if subops[0].v['param'] is not None:
            assert subops[0].v['param'].subsubs is None
        kt0 = (tuple(subops[0].subop),)
        if len(subops) > 1 and subops[0].v['param'] is None:
            kt0 = (tuple(subops[0].subop), None)
    if len(subops) == 1:
        return kt0
    else:
        return kt0 + getKeyTuple(subops[1:])

###def getZeroOpInfo(whichDict: Dict[Any, Any], partkey: Tuple[Any, ...]) -> OpInfo:
###    key_to_use = partkey[0] if len(partkey) == 1 else partkey
###    val = whichDict[key_to_use]
###    if isinstance(val, OpInfo):
###        return val
###    else:
###        return whichDict[val[0]]
###
def subsubEqual(ss1: Optional[List[SSsubop]], ss2: Optional[List[SSsubop]]) -> None:
    if ss1 == ss2: return
    assert ss1 is not None and ss2 is not None
    assert ss1[0].subop == ss2[0].subop
    assert ss1[0].occur == ss2[0].occur
    assert ss1[0].prepend == ss2[0].prepend
    if ss1[0].v['param'] is None:
        assert ss2[0].v['param'] is None
    else:
        subsubEqual(ss1[0].v['param'].subsubs, ss2[0].v['param'].subsubs)
    subsubEqual(ss1[1:], ss2[1:])

def subOpCompat(so1: List[SSsubop], so2: List[SSsubop]) -> None:
    if len(so1) == 0 and len(so2) == 0:
        return
    assert len(so1) != 0 and len(so2) != 0
    if (so1[0].occur in ["mandatory", "repeating1"]) != (so2[0].occur in ["mandatory", "repeating1"]):
        return
    if so1[0].occur in ["mandatory", "repeating1"] and so2[0].occur in ["mandatory", "repeating1"]:
        if so1[0].subop != so2[0].subop:
            return
        if so1[0].v['param'] is None and so2[0].v['param'] is not None:
            return
        if so1[0].v['param'] is not None and so2[0].v['param'] is None:
            return
    else:
        assert so1[0].occur == so2[0].occur
        assert so1[0].subop == so2[0].subop
        assert so1[0].prepend == so2[0].prepend
        assert getattr(so1[0], 'associative', False) == getattr(so2[0], 'associative', False)
        subsubEqual(so1[0].v['param'].subsubs, so2[0].v['param'].subsubs)
    subOpCompat(so1[1:], so2[1:])

def checkCompat(oi1: OpInfo, oi2: OpInfo) -> None:
    if oi1.left is not None and oi2.left is not None:
        if oi1.left.keyword == oi2.left.keyword:
            assert oi1.left.precedence == oi2.left.precedence
    else:
        assert (oi1.left is None) == (oi2.left is None)
    subOpCompat(oi1.subops, oi2.subops)

def insertOp(whichDict: Dict[Any, Any], opInfo: OpInfo) -> None:
    opKey = getKeyTuple(opInfo.subops)
    if opKey not in whichDict:
        whichDict[opKey] = []
    whichDict[opKey].append(opInfo)
    
    if len(opKey) == 1:
        for choice in opKey[0]:
            if choice not in whichDict:
                whichDict[choice] = []
            if opKey not in whichDict[choice]:
                whichDict[choice].append(opKey)
        return
    
    curKey = opKey[:-1]
    compatChecked = False
    while len(curKey) > 0:
        if curKey not in whichDict:
            whichDict[curKey] = [opKey]
        else:
            assert not isinstance(whichDict[curKey], OpInfo)
            if not compatChecked:
                first_opKey = whichDict[curKey][0]
                checkCompat(opInfo, whichDict[first_opKey][0])
                compatChecked = True
            if opKey not in whichDict[curKey]:
                whichDict[curKey].append(opKey)
        if len(curKey) == 1:
            for choice in curKey[0]:
                whichDict[choice] = whichDict[curKey] # HACK
        curKey = curKey[:-1]

def mctlEval(s: Optional[str]) -> Any:
    if s is None or s == "None": return None
    
    if s.isidentifier() or "." in s:
        if s == "ProcedureCall" or s == "A.callOp": return A.callOp
        if s == "ZeroTuple" or s == "A.zeroTuple": return lambda *args: A.zeroTuple()
        if s == "Closure": return A.toClosure
        if s == "ClosureArg": return lambda *args: A.AstClParam()
        if s == "ClosureResult": return lambda *args: A.AstClRslt()
        if s == "Tuple" or s == "OneTuple": return A.AstTuple
        return A.AstIdentifier(identifier=s)

    try:
        rslt = eval(s)
    except NameError:
        rslt = None
    return rslt

sopSpecRE = re.compile(r'''
    (?:
        \[ 
            \s* 
            (?P<subops>                     
                (?P<alt>                    
                    " (?: [^\\"] | \\. )* " 
            )                           
            (?:                         
                \s* \| \s*              
                (?P<alt>                
                    " (?: [^\\"] | \\. )* " 
                )                       
                )*                          
            )
            (?:\s*(?P<occur>mandatory|optional|repeating0|repeating1|repeating))?
            (?:\s*(?P<prepend>prepend))?
            (?:\s*(?P<associative>associative))?
            #(?:\s*(?P<allAdjust>"(?:[^\\"]|\\.)+"))?
        \s*\]
    ) |
    (?:
        \s*\( 
            (?:\s*(?P<keyword>[a-zA-Z_][a-zA-Z0-9_]*))?
            (?:\s*(?P<precedence>\d+\.?\d*))?
            #(?:\s*(?P<oneAdjust>"(?:[^\\"]|\\.)+"))?
            (?:\s*(?P<FIXME>[^\w\s()\[\]{}'"])(?P<subsubs>.+)(?P=FIXME))?
        \s*\)
    ) 
    ''', re.VERBOSE)

def genSopSpec(fromRE: Iterable[Any]) -> Iterator[Union[SSsubop, SSparam]]:
    pos = 0
    for mss in fromRE:
        if mss.group("subops"):
            assert mss[0][0] == '['
            occur = "mandatory"
            if mss.group("occur"):
                occur = mss.group("occur")
                if occur == "repeating":
                    occur = "repeating0"
            alt = mss.captures("alt")
            subop_list = list(map(U.unquote, alt))
            choicePos = pos if len(subop_list) > 1 else None
            if choicePos is not None:
                pos += 1
            yield SSsubop(
                subop=subop_list,
                occur=occur,
                #allAdjust=mctlEval(U.unquote(mss.group("allAdjust"))) if mss.group("allAdjust") else None,
                v=dict(param=None, nextMandatory=None, nextPossibles=None, choicePos=choicePos),
                prepend=True if mss.group("prepend") else False,
                associative=True if mss.group("associative") else False
            )
        else:
            assert re.match(r'\s*\(', mss[0]) is not None
            pT = mss.group("precedence")
            kW = mss.group("keyword")
            dummyLeft, subsubs, ssParamLen = getSopSpec(mss.group("subsubs"))
            yield SSparam(
                precedence=None if pT is None else decimal.Decimal(pT),
                pos=pos,
                #oneAdjust=mctlEval(U.unquote(mss.group("oneAdjust"))) if mss.group("oneAdjust") else None,
                ssParamLen=ssParamLen,
                subsubs=subsubs,
                keyword=kW
            )
            pos += 1

def ssPair(sopAndParam: Iterator[Union[SSsubop, SSparam]]) -> Iterator[SSsubop]:
    sop = next(sopAndParam, None)
    if sop is None:
        return
    assert isinstance(sop, SSsubop)
    while True:
        nxt = next(sopAndParam, None)
        if nxt is not None and isinstance(nxt, SSparam):
            sop.v['param'] = nxt
            yield sop
            sop = next(sopAndParam, None)
            if sop is None: return
        elif nxt is None:
            sop.v['param'] = None
            yield sop
            return
        else:
            sop.v['param'] = None
            yield sop
            sop = nxt

def getMandPoss(sopSpec: List[SSsubop], i: int, pLen: int) -> Tuple[Optional[List[str]], List[str], int]:
    if i == len(sopSpec):
        return None, [], pLen
    nextNextMan, nextPoss, pLen = getMandPoss(sopSpec, i + 1, pLen)
    p = sopSpec[i].v['param']
    if p is not None: pLen = max(p.pos + 1, pLen)
    choicePos = sopSpec[i].v.get('choicePos')
    if choicePos is not None: pLen = max(choicePos + 1, pLen)
    if p is not None and p.subsubs:
        subNextMan, subPoss, ssParamLen = getMandPoss(p.subsubs, 0, 0)
        sopSpec[i].v['nextMandatory'] = subNextMan if subNextMan is not None else nextNextMan
        sopSpec[i].v['nextPossibles'] = subPoss if subNextMan is not None else subPoss + nextPoss
    else:
        sopSpec[i].v['nextMandatory'] = nextNextMan
        sopSpec[i].v['nextPossibles'] = nextPoss
    if sopSpec[i].occur in ['mandatory', 'repeating1']:
        return sopSpec[i].subop, list(sopSpec[i].subop), pLen
    else:
        return sopSpec[i].v['nextMandatory'], sopSpec[i].subop + sopSpec[i].v['nextPossibles'], pLen

def getSopSpec(sopSpecText: Optional[str]) -> Tuple[Optional[SSparam], Optional[List[SSsubop]], int]:
    if sopSpecText is None: return None, None, 0
    sopSpecUnpaired = list(genSopSpec(re.finditer(sopSpecRE, sopSpecText)))
    if sopSpecText[0] == '(':
        left = cast(SSparam, sopSpecUnpaired[0])
        sopSpec = list(ssPair(iter(sopSpecUnpaired[1:])))
    else:
        left = None
        sopSpec = list(ssPair(iter(sopSpecUnpaired)))
        
    nextMandatory, possibles, pLen = getMandPoss(sopSpec, 0, (1 if left is not None else 0))
    for i in range(len(sopSpec)):
        if sopSpec[i].occur in ['repeating0', 'repeating1']:
            sopSpec[i].v['nextPossibles'].extend(sopSpec[i].subop)
    return left, sopSpec, pLen

def isDuplicateOp(oi1: OpInfo, oi2: OpInfo) -> bool:
    if (oi1.left is None) != (oi2.left is None):
        return False
    if oi1.left is not None:
        if oi1.left.precedence != oi2.left.precedence or oi1.left.keyword != oi2.left.keyword:
            return False
    if oi1.paramLen != oi2.paramLen:
        return False
    
    # compare astFun
    f1, f2 = oi1.astFun, oi2.astFun
    if type(f1) != type(f2):
        return False
    if isinstance(f1, A.AstNode):
        if str(f1) != str(f2):
            return False
    elif callable(f1):
        if hasattr(f1, '__code__') and hasattr(f2, '__code__'):
            if f1.__code__.co_code != f2.__code__.co_code:
                return False
        else:
            if f1 != f2:
                return False
    else:
        if f1 != f2:
            return False

    # compare subops
    if len(oi1.subops) != len(oi2.subops):
        return False
    for s1, s2 in zip(oi1.subops, oi2.subops):
        if s1.subop != s2.subop or s1.occur != s2.occur or s1.prepend != s2.prepend or getattr(s1, 'associative', False) != getattr(s2, 'associative', False):
            return False
        if (s1.v.get('param') is None) != (s2.v.get('param') is None):
            return False
        if s1.v.get('param') is not None:
            p1, p2 = s1.v['param'], s2.v['param']
            if p1.precedence != p2.precedence or p1.keyword != p2.keyword: # or p1.oneAdjust != p2.oneAdjust:
                return False
    return True

declared_operator_symbols: set[str] = set() #{'(', ')', '[', ']', '{', '}', ';', ':', ',', '=', '_', '$', '`$'}

def is_subop_identifier(s: str) -> bool:
    return bool(re.match(r"^[a-zA-Z\u0370-\u03ff\u1f00-\u1ffe][_a-zA-Z0-9%\u0370-\u03ff\u1f00-\u1ffe]*'*$", s))

def extract_and_register_suboperators(sopSpec: List[SSsubop]) -> None:
    changed = False
    def recurse(subops_list: List[SSsubop]):
        nonlocal changed
        for ss in subops_list:
            for item in ss.subop:
                if item and not item.isspace() and not item.startswith('!') and not is_subop_identifier(item):
                    sub_items = [item] if item != ':,' else [':', ',']
                    for si in sub_items:
                        if si not in declared_operator_symbols:
                            declared_operator_symbols.add(si)
                            changed = True
            if ss.v.get('param') is not None and ss.v['param'].subsubs is not None:
                recurse(ss.v['param'].subsubs)
    recurse(sopSpec)
    if changed:
        lexer.update_operator_only_pattern(declared_operator_symbols)

lexer.update_operator_only_pattern(declared_operator_symbols)

def doOperatorCmd(astFun: str, sopSpecText: str) -> None:
    left, sopSpec, pCnt = getSopSpec(sopSpecText)
    assert sopSpec is not None
    if sopSpec:
        extract_and_register_suboperators(sopSpec)
    evaluatedFun = mctlEval(astFun) if isinstance(astFun, str) else astFun
    
    whichDict = withLeft if left else noLeft
    opKey = getKeyTuple(sopSpec)
    new_op = OpInfo(left=left, astFun=evaluatedFun, paramLen=pCnt, subops=sopSpec)
    if opKey in whichDict:
        assert isinstance(whichDict[opKey], list)
        for existing_op in whichDict[opKey]:
            if isDuplicateOp(existing_op, new_op):
                return
        
    insertOp(whichDict, new_op)

###if __name__ == "__main__":
###    doOperatorCmd("A.callOp", '(100) [" "] (100)')
###    doOperatorCmd("A.zeroTuple", '["["] ["]"]')
###    doOperatorCmd("A.zeroTuple", '["["] () [" " repeating] () ["]"]')
###    doOperatorCmd("A.zeroTuple", '["["] () ["|"] () ["]"]')
###    breakpoint()
###    print(noLeft)

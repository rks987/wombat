import os
import utility as U
import wast as A
import lexer as L
import woperator as op
import collections as C
import re
import decimal
from typing import NamedTuple, List, Dict, Tuple, Optional, Any, Union, Iterable, Iterator, cast
from dataclasses import dataclass

class TrackingIterator:
    def __init__(self, it):
        self.it = it
        self.history = []
        self.peeked = []

    def __iter__(self):
        return self

    def __next__(self):
        if self.peeked:
            tok = self.peeked.pop(0)
        else:
            try:
                tok = next(self.it)
            except StopIteration:
                tok = None
        if tok is not None:
            self.history.append(tok)
            return tok
        raise StopIteration

    def prepend(self, tok):
        if tok is not None:
            self.peeked.insert(0, tok)
            if self.history and self.history[-1] == tok:
                self.history.pop()

    @property
    def last_tok(self):
        return self.history[-1] if self.history else None

def prepend(tok, toks):
    if hasattr(toks, 'prepend'):
        toks.prepend(tok)
    return toks

def get_real_path(filename):
    if not filename:
        return None
    path = os.path.abspath(filename)
    base = os.path.basename(path)
    if base.startswith(".lsp_temp_"):
        path = os.path.join(os.path.dirname(path), base[10:])
    return path

operatorRE = re.compile(r'\s*("(?:[^\\"]|\\.)+"|[A-Za-z0-9_.]+)\s+([^\n]+)\n?$')

def doMCTcmd(cmd: str, tok: L.Token) -> A.AstNode:
    if cmd.startswith('operator '):
        mo = operatorRE.match(cmd[9:])
        if mo:
            op.doOperatorCmd(mo.group(1), mo.group(2))
        else: 
            U.die("invalid operator decl: " + cmd, *tok.location)
    elif cmd.startswith('import '):
        raise Exception("import not implemented -- FIXME")
    elif cmd.startswith('package '):
        raise Exception("package not implemented -- FIXME")
    elif cmd.startswith('export '):
        raise Exception("export not implemented -- FIXME")
    else:
        U.die("unknown MCTcmd: " + cmd, *tok.location) 
    return A.zeroTuple()

def opFunL(fun: Any, astL: Tuple[Optional[A.AstNode], ...]) -> A.AstNode:
    astL_filtered = tuple(a for a in astL if a is not None)
    for a in astL_filtered:
        if not isinstance(a, A.AstNode):
            print(f"FAILED TYPE: {type(a)} {a} from astFun: {fun} and pAstL length {len(astL_filtered)}")
            assert False
    if callable(fun):
        return fun(astL_filtered)
    if len(astL_filtered) == 0: return fun
    return opFunAst(fun, astL_filtered[0] if len(astL_filtered) == 1 else A.AstTuple(members=astL_filtered))

# Some of the increased interaction between the levels is my fault (the lexer gets
# its list of OperatorOnly tokens from operator declarations). However this is
# AI slop, implementing the intention of my request while ignoring the way I requested.
# FIXME
def opFunAst(fun: Any, pAst: A.AstNode) -> A.AstNode:
    assert isinstance(pAst, A.AstNode)
    if fun is None: 
        return pAst
    if isinstance(fun, A.AstIdentifier) and fun.identifier == "Semicolon" and isinstance(pAst, A.AstTuple):
        pAst.is_associative = True
    return A.AstCall(procParam=A.AstTuple(members=(fun, pAst)))

def is_registered_operator_name(name: str) -> bool:
    for dict_obj in [op.noLeft, op.withLeft]:
        for key, val in dict_obj.items():
            if isinstance(val, list):
                for item in val:
                    if isinstance(item, op.OpInfo):
                        fun = item.astFun
                        if isinstance(fun, A.AstIdentifier) and fun.identifier == name:
                            return True
    return False

def astMatchesKeyword(node: Any, keyword: str) -> bool:
    if keyword == "identifier":
        return isinstance(node, A.AstIdentifier)
    is_registered = is_registered_operator_name(keyword)
    if not is_registered:
        raise Exception(f"Undefined keyword/operator: '{keyword}'")
    if isinstance(node, A.AstCall):
        func = node.funct()
        if isinstance(func, A.AstIdentifier) and func.identifier == keyword:
            return True
    return False

def getNextNonComment(toks: Iterator[L.Token]) -> Tuple[Optional[L.Token], Iterator[L.Token]]:
    tok = next(toks, None)
    while tok is not None and (tok.tT.tType == 'Comment' or tok.tT.tType == 'MCTcmd' or tok.tT.tType == 'Pragma'):
        if tok.tT.tType == 'MCTcmd':
            doMCTcmd(tok.tT.text, tok)
        tok = next(toks, None)
    return tok, toks

def getMatchingOpInfos(opDict: Dict[Any, Any], token_text: str) -> List[op.OpInfo]:
    token_text = token_text.rstrip("'")
    if token_text not in opDict:
        return []
    val = opDict[token_text]
    if isinstance(val, op.OpInfo):
        oiL = [val]
    else:
        oiL = []
        for item in val:
            if isinstance(item, op.OpInfo):
                oiL.append(item)
            elif item in opDict:
                target = opDict[item]
                if isinstance(target, op.OpInfo):
                    oiL.append(target)
                elif isinstance(target, list):
                    for subitem in target:
                        if isinstance(subitem, op.OpInfo):
                            oiL.append(subitem)
    
    def countKeywords(oi: op.OpInfo) -> int:
        cnt = 0
        if oi.left is not None and oi.left.keyword is not None:
            cnt += 1
        for sop in oi.subops:
            param = sop.v.get('param')
            if param is not None and param.keyword is not None:
                cnt += 1
        return cnt
    
    oiL.sort(key=countKeywords, reverse=True)
    return oiL

class ScopeTracker:
    def __init__(self):
        self.scopes = [set()]
        # AI decided that things mentioned in docs bettter get declared somewhere. Slop FIXME
        self.scopes[0].update([
            '$builtin'])#, 'Optional', 'print', 'unit', 'Unit', 'Type', 'Empty', 'Any', 'Atom',
            #'List', 'Set', 'Tuple', 'Prop', 'Name', 'DisjointUnion', 'Total', 'Totalise',
            #'Monad', 'Behaviour', 'Union', 'Intersection', 'NamedValue', 'firstCase',
            #'totalise', 'forall%', '∀%', 'Nat', 'Int', 'Real', 'String', 'Bool',
            #'toImplies%', 'fromImplies%', 'toIff%', 'fromIff%', 'toAnd%', 'fromAnd%',
            #'toOr%', 'fromOr%', 'toUnion%', 'fromUnion%', 'toIntersection%', 'fromIntersection%',
            #'forall', 'exists', 'foreach'
        #])

    def push_scope(self):
        self.scopes.append(set())

    def pop_scope(self):
        if len(self.scopes) > 1:
            self.scopes.pop()

    def add_new_id(self, name: str):
        self.scopes[-1].add(name)

    def is_known(self, name: str) -> bool:
        if name.startswith('$builtin') or name.startswith('$'):
            return True
        for s in reversed(self.scopes):
            if name in s:
                return True
        return False

global_scope_tracker = ScopeTracker()

@dataclass
class OpCtx:
    upOpCtx: Optional['OpCtx']
    indx: int
    altOpInfos: List[op.OpInfo]
    token: Optional[L.Token] = None

def posSubop(tokTT: L.TokTT, opCtx: Optional[OpCtx]) -> bool:
    if tokTT.tType not in ['Identifier', 'OperatorOnly']: return False
    if opCtx is None or len(opCtx.altOpInfos) == 0: return False
    
    res = False
    # identifiers and OperatorOnly are allowed to have trailing primes (aka
    # single quotes). So Why is AI removing them??. I'll comment out the rstrip
    text = tokTT.text#.rstrip("'") # ??? what is this? FIXME
    for i in range(len(opCtx.altOpInfos)):
        if text in opCtx.altOpInfos[i].subops[opCtx.indx].v['nextPossibles']:
            res = True
            break
            
    if not res:
        for oi in opCtx.altOpInfos:
            next_man = oi.subops[opCtx.indx].v['nextMandatory']
            if next_man is not None and text in next_man:
                res = True
                break
            
    if not res:
        for oi in opCtx.altOpInfos:
            if oi.subops[opCtx.indx].v['nextMandatory'] is None:
                res = posSubop(tokTT, opCtx.upOpCtx)
                break
    return res

def needNoLeft(tok: L.Token, toks: Iterator[L.Token], opCtx: Optional[OpCtx], noneOK: bool) -> Tuple[Optional[L.Token], Iterator[L.Token]]:
    text = tok.tT.text#.rstrip("'") # more rstrip slop ???
    if tok.tT.tType in ['Identifier', 'OperatorOnly'] and (posSubop(tok.tT, opCtx) or \
                         (text not in op.noLeft and text in op.withLeft)):
        if noneOK:
            return None, prepend(tok, toks)
        #breakpoint()
        defOperandTok = L.Token(tT=L.TokTT(text='!!defaultOperand', tType='OperatorOnly'),
                                indent=None, whiteB4=False, location=tok.location)
        return defOperandTok, prepend(tok, toks)
    return tok, toks

def needLeft(tok: L.Token, toks: Iterator[L.Token]) -> Tuple[L.Token, Iterator[L.Token]]:
    text = tok.tT.text#.rstrip("'")
    if tok.tT.tType not in ['Identifier', 'OperatorOnly'] or text not in op.withLeft:
        return L.Token(tT=L.TokTT(text=(" " if tok.whiteB4 else ""), tType='OperatorOnly'),
                          indent=-1, whiteB4=False, location=tok.location), \
               prepend(tok, toks)
    return tok, toks

# The structure type stuff is all AI, and at least partly wrong (since it thought that @<
# was a new operator rather than an @ operator applied to a structure type with 1 value)
def is_in_structure_type(opCtx: Optional[OpCtx]) -> bool:
    cur = opCtx
    while cur is not None:
        if cur.altOpInfos:
            for oi in cur.altOpInfos:
                if isinstance(oi.astFun, A.AstIdentifier) and oi.astFun.identifier in ['StructureType', 'StructureInstance']:
                    return True
        cur = cur.upOpCtx
    return False

# ???
def is_id_param_slot(opCtx: Optional[OpCtx]) -> bool:
    cur = opCtx
    while cur is not None:
        if cur.altOpInfos:
            for oi in cur.altOpInfos:
                ast_id = oi.astFun.identifier if isinstance(oi.astFun, A.AstIdentifier) else getattr(oi.astFun, '__name__', '')
                if ast_id in ['SpecifyType', 'IdTypeList', 'identifierList', 'identifier', 'forall', 'exists', 'foreach', 'forall%', 'exists%', '∀%', '∃%']:
                    return True
                if cur.indx < len(oi.subops):
                    param = oi.subops[cur.indx].v.get('param')
                    if param is not None and param.keyword in ["identifier", "IdTypeList", "identifierList"]:
                        return True
        cur = cur.upOpCtx
    return False

def getExpr(toks: Iterator[L.Token], left: Optional[A.AstNode], prio: Optional[decimal.Decimal], opCtx: Optional[OpCtx], noneOK: bool) -> Tuple[Optional[A.AstNode], Iterator[L.Token]]:
    tok = next(toks, None)
    while tok is not None and (tok.tT.tType == 'Comment' or tok.tT.tType == 'MCTcmd' or tok.tT.tType == 'Pragma'):
        if tok.tT.tType == 'MCTcmd':
            doMCTcmd(tok.tT.text, tok)
        tok = next(toks, None)

    if tok is None:
        return None, toks

    if tok.tT.tType == 'OperatorOnly' and tok.tT.text.startswith(',') and len(tok.tT.text) > 1:
        print(f"tok.tT.text={tok.tT.text}") and breakpoint() # can an OperatorOnly start with a comma? -- AI slop???
        rem = tok.tT.text[1:]
        rem_type = 'Identifier' if rem.isidentifier() else 'OperatorOnly'
        toks = prepend(L.Token(tT=L.TokTT(text=rem, tType=rem_type), indent=tok.indent, whiteB4=False, location=tok.location), toks)
        tok = L.Token(tT=L.TokTT(text=',', tType='OperatorOnly'), indent=tok.indent, whiteB4=tok.whiteB4, location=tok.location)

    if left is None:
        start_pos = (tok.location[1], tok.location[2], tok.location[0])
    else:
        start_pos = (left.start_line, left.start_col, left.filename) if getattr(left, 'start_line', None) is not None else None

    opDict = op.withLeft if left is not None else op.noLeft
    oiL = None
    if left is None:
        tok_opt, toks = needNoLeft(tok, toks, opCtx, noneOK)
        if tok_opt is None: return None, toks
        tok = tok_opt
    else:
        tok, toks = needLeft(tok, toks)
        if posSubop(tok.tT, opCtx):
            return left, prepend(tok, toks)
        text = tok.tT.text#.rstrip("'")
        if not (tok.tT.tType in ["Identifier", "OperatorOnly"] and text in op.withLeft):
            if tok.tT.tType == 'OperatorOnly' and not posSubop(tok.tT, opCtx):
                U.die(f"Token '{tok.tT.text}' marked OperatorOnly is not a possible suboperator", *tok.location)
            print(f"FAILED ASSERTION: {tok.tT.tType} {repr(tok.tT.text)}")
            assert False
        oiL = getMatchingOpInfos(op.withLeft, tok.tT.text)
        oiL = [oi for oi in oiL if oi.left is None or oi.left.keyword is None or astMatchesKeyword(left, oi.left.keyword)]
        if not oiL:
            return left, prepend(tok, toks)
        if isinstance(left, A.AstIdentifier):
            if any(oi.left is not None and oi.left.keyword in ["identifier", "IdTypeList", "identifierList"] for oi in oiL):
                global_scope_tracker.add_new_id(left.identifier)
            ###elif tok.tT.text in ['=', ':']:
            ###    print("AI hack checking for = or :") and breakpoint()
            ###    global_scope_tracker.scopes[0].add(left.identifier)
        zopInfo = oiL[0]
        assert zopInfo.left is not None
        if prio is not None and zopInfo.left.precedence is not None and zopInfo.left.precedence < prio:
            return left, prepend(tok, toks)

    text = tok.tT.text#.rstrip("'")
    if text not in opDict:
        assert left is None and text not in op.noLeft
        opDict = None
        if tok.tT.tType == 'Literal':
            ast = A.AstLiteral(const=tok.tT.text, constType=None)
        elif tok.tT.tType in ['NewOperator', 'Operator', 'ValueOperator']:
            internal_id = f"{{{tok.tT.text}}}"
            if tok.tT.tType in ['NewOperator', 'ValueOperator']:
                ast = A.AstNewIdentifier(identifier=internal_id)
                op.doOperatorCmd(astFun=A.AstIdentifier(identifier=internal_id), sopSpecText=tok.tT.text)
            else:
                ast = A.AstIdentifier(identifier=internal_id)
        else:
            next_tok = next(toks, None)
            #is_followed_by_colon_or_eq = (next_tok is not None and next_tok.tT.text in [':', '='])
            if next_tok is not None:
                toks = prepend(next_tok, toks)

            if tok.tT.tType in ['NewIdentifier', 'NewFreeIdentifier', 'NewFreeIdentifier'] or is_id_param_slot(opCtx) or is_in_structure_type(opCtx):# or is_followed_by_colon_or_eq:
                clean_name = tok.tT.text#.lstrip('`')
                global_scope_tracker.scopes[0].add(clean_name)
                global_scope_tracker.add_new_id(clean_name)
            elif tok.tT.tType == 'OperatorOnly' and tok.tT.text.startswith('`'):
                clean_name = tok.tT.text#.lstrip('`')
                global_scope_tracker.scopes[0].add(clean_name)
                global_scope_tracker.add_new_id(clean_name)
            elif tok.tT.tType == 'Identifier' or (tok.tT.tType == 'OperatorOnly' and (global_scope_tracker.is_known(tok.tT.text) or global_scope_tracker.is_known(tok.tT.text))):#.lstrip('`')))):
                clean_text = tok.tT.text#.lstrip('`')
                if not posSubop(tok.tT, opCtx) and not global_scope_tracker.is_known(clean_text):
                    U.die(f"Identifier '{clean_text}' hasn't previously been seen marked NewIdentifier", *tok.location)
            elif tok.tT.tType == 'OperatorOnly':
                if not posSubop(tok.tT, opCtx):
                    U.die(f"Token '{tok.tT.text}' marked OperatorOnly is not a possible suboperator", *tok.location)

            IdClasses = {'Identifier': A.AstIdentifier, 'NewIdentifier': A.AstNewIdentifier,
                     'NewFreeIdentifier': A.AstNewFreeIdentifier, 'OperatorOnly': A.AstIdentifier}
            ast = IdClasses[tok.tT.tType](identifier=tok.tT.text)
    else:
        if oiL is None:
            oiL = getMatchingOpInfos(opDict, tok.tT.text)
        opInfo, pAsts, toks = getSubops(toks=prepend(tok, toks), opCtx=OpCtx(upOpCtx=opCtx, indx=0, altOpInfos=oiL, token=tok), left=left)
        ast = opFunL(opInfo.astFun, tuple(p for p in pAsts if p is not None))

    if ast is not None and start_pos is not None:
        ast.start_line = start_pos[0]
        ast.start_col = start_pos[1]
        ast.filename = get_real_path(start_pos[2])
        if hasattr(toks, 'last_tok') and toks.last_tok is not None:
            ast.end_line = toks.last_tok.location[1]
            ast.end_col = toks.last_tok.location[2] + len(toks.last_tok.tT.text)

    tok = next(toks, None)
    if tok is None or posSubop(tok.tT, opCtx):
        return ast, prepend(tok, toks) if tok is not None else toks
    
    expr, toks = getExpr(toks=prepend(tok, toks), left=ast, prio=prio, opCtx=opCtx, noneOK=False)
    return expr, toks

def getSubops(toks: Iterator[L.Token], opCtx: OpCtx, left: Optional[A.AstNode] = None) -> Tuple[op.OpInfo, List[Any], Iterator[L.Token]]:
    is_new_scope = False
    if opCtx is not None and opCtx.altOpInfos:
        for oi in opCtx.altOpInfos:
            if oi.astFun == A.toClosure or getattr(oi.astFun, '__name__', '') == 'toClosure':
                is_new_scope = True
                break
            if isinstance(oi.astFun, A.AstIdentifier) and oi.astFun.identifier == 'StructureType':
                is_new_scope = True
                break

    if is_new_scope:
        global_scope_tracker.push_scope()

    try:
        tok = next(toks, None)
        if tok is None:
            raise Exception("Unexpected EOF in getSubops")
        oiL = opCtx.altOpInfos[:]
        if left is not None:
            oiL = [oi for oi in oiL if oi.left is None or oi.left.keyword is None or astMatchesKeyword(left, oi.left.keyword)]
        maxPL = max((oi.paramLen for oi in oiL))
        pAstL = [None] * maxPL
        if left is not None:
            pAstL[0] = left
        indx = 0
        while True:
            if tok is None:
                cur = opCtx
                while cur is not None:
                    loc = f"{cur.token.location[0]}:{cur.token.location[1]}:{cur.token.location[2]}" if cur.token else "None"
                    print(f"DEBUG OpCtx: indx={cur.indx}, loc={loc}, altOpInfos={[getattr(oi.astFun, '__name__', str(oi.astFun)) for oi in cur.altOpInfos]}")
                    cur = cur.upOpCtx
                raise Exception(f"Unexpected EOF in getSubops (oiL={oiL}, indx={indx})")
            orig_oiL = list(oiL)
            text = tok.tT.text.rstrip("'")
            oiL = [oi for oi in oiL if text in oi.subops[indx].subop or \
                                       (oi.subops[indx].occur not in ['mandatory', 'repeating1'] and \
                                        (len(oi.subops) - 1 == indx or \
                                         (oi.subops[indx].v['nextPossibles'] is not None and \
                                          text in oi.subops[indx].v['nextPossibles'])))]
            if not oiL:
                print(f"FAILED TO MATCH: tok={repr(tok.tT.text)} (type={tok.tT.tType}) indx={indx}")
                print(f"Candidates:")
                for oi in orig_oiL:
                    print(f"  Op: {oi.astFun} subops={[s.subop for s in oi.subops]} occurs={[s.occur for s in oi.subops]} nextPoss={oi.subops[indx].v['nextPossibles']}")
            assert oiL != []
            if len(oiL[0].subops) - 1 == indx and oiL[0].subops[indx].v['param'] is None:
                choicePos = oiL[0].subops[indx].v.get('choicePos')
                if choicePos is not None:
                    lit = A.AstLiteral(const=f'"{tok.tT.text}"', constType=None)
                    lit.start_line = tok.location[1]
                    lit.start_col = tok.location[2]
                    lit.end_line = tok.location[1]
                    lit.end_col = tok.location[2] + len(tok.tT.text)
                    lit.filename = get_real_path(tok.location[0])
                    pAstL[choicePos] = lit
                assert oiL[0].subops[indx].occur in ['mandatory', 'repeating1']
                return oiL[0], pAstL[:oiL[0].paramLen], toks
                
            numMandatory = sum((1 for i in range(len(oiL)) if oiL[i].subops[indx].occur in ['mandatory', 'repeating1']))
            assert numMandatory == 0 or numMandatory == len(oiL)
            
            sopPs = []
            while True:
                text = tok.tT.text.rstrip("'") if tok is not None else ""
                nextSopText = oiL[0].subops[indx].subop
                nextSopOccurs = [oiL[i].subops[indx].occur for i in range(len(oiL))]
                nextSopvparams = [oiL[i].subops[indx].v['param'] for i in range(len(oiL))]
                
                is_repeating = any(oc in ['repeating0', 'repeating1'] for oc in nextSopOccurs)
                if text not in nextSopText or (len(sopPs) == 1 and not is_repeating):
                    compatible_oiL = []
                    for oi in oiL:
                        occur = oi.subops[indx].occur
                        has_param = (oi.subops[indx].v['param'] is not None)
                        if has_param:
                            if occur == 'mandatory' and len(sopPs) != 1:
                                continue
                            if occur == 'repeating1' and len(sopPs) < 1:
                                continue
                            if occur == 'optional' and len(sopPs) > 1:
                                continue
                        else:
                            if len(sopPs) != 0:
                                continue
                        compatible_oiL.append(oi)
                    
                    if compatible_oiL:
                        first_occur = compatible_oiL[0].subops[indx].occur
                        compatible_oiL = [oi for oi in compatible_oiL if oi.subops[indx].occur == first_occur]
                    
                    oiL = compatible_oiL
                    nextSopOccurs = [oiL[i].subops[indx].occur for i in range(len(oiL))]
                    nextSopvparams = [oiL[i].subops[indx].v['param'] for i in range(len(oiL))]

                    if len(sopPs) == 0 and None in nextSopvparams:
                        oiL = [oiL[i] for i in range(len(oiL)) if oiL[i].subops[indx].v['param'] is None]
                        break
                    elif 'mandatory' in nextSopOccurs:
                        assert len(sopPs) == 1 and all(oc == 'mandatory' for oc in nextSopOccurs)
                        pAstL[oiL[0].subops[indx].v['param'].pos] = sopPs[0]
                    else: 
                        if not is_repeating:
                            assert len(sopPs) < 2 and all(nso == 'optional' for nso in nextSopOccurs)
                            pAstL[oiL[0].subops[indx].v['param'].pos] = sopPs[0] if len(sopPs) > 0 else None
                        else:
                            sopPs_final = list(sopPs)
                            if oiL[0].subops[indx].prepend:
                                if indx == 0:
                                    pos_prev = 0
                                else:
                                    pos_prev = oiL[0].subops[indx - 1].v['param'].pos
                                prev_val = pAstL[pos_prev]
                                pAstL[pos_prev] = None
                                sopPs_final.insert(0, prev_val)
                            pAstL[oiL[0].subops[indx].v['param'].pos] = A.AstTuple(
                                members=tuple(sopPs_final),
                                is_associative=getattr(oiL[0].subops[indx], 'associative', False)
                            )
                    break
                    
                choicePos = oiL[0].subops[indx].v.get('choicePos')
                if choicePos is not None:
                    lit = A.AstLiteral(const=f'"{tok.tT.text}"', constType=None)
                    lit.start_line = tok.location[1]
                    lit.start_col = tok.location[2]
                    lit.end_line = tok.location[1]
                    lit.end_col = tok.location[2] + len(tok.tT.text)
                    lit.filename = get_real_path(tok.location[0])
                    if is_repeating:
                        if pAstL[choicePos] is None:
                            pAstL[choicePos] = [lit]
                        else:
                            pAstL[choicePos].append(lit)
                    else:
                        pAstL[choicePos] = lit

                numWithoutParam = sum((1 for i in range(len(oiL)) if oiL[i].subops[indx].v['param'] is None))
                noneOK = numWithoutParam > 0
                precedence = None if noneOK else oiL[0].subops[indx].v['param'].precedence
                p = None
                curOpCtx = OpCtx(upOpCtx=opCtx.upOpCtx, indx=indx, altOpInfos=oiL, token=opCtx.token)
                
                if noneOK or (oiL[0].subops[indx].v['param'].subsubs is None):
                    assert all(oiL[i].subops[indx].v['param'] is None or \
                            oiL[i].subops[indx].v['param'].subsubs is None for i in range(len(oiL)))
                    param = oiL[0].subops[indx].v['param']
                    has_id_keyword = any(oi.subops[indx].v['param'] is not None and oi.subops[indx].v['param'].keyword == "identifier" for oi in oiL)
                    
                    p = None
                    if has_id_keyword:
                        tok_opt, toks = getNextNonComment(toks)
                        if tok_opt is not None and tok_opt.tT.tType in ['Identifier', 'NewIdentifier']:
                            global_scope_tracker.add_new_id(tok_opt.tT.text)
                            p = A.AstIdentifier(identifier=tok_opt.tT.text)
                            p.start_line = tok_opt.location[1]
                            p.start_col = tok_opt.location[2]
                            p.end_line = tok_opt.location[1]
                            p.end_col = tok_opt.location[2] + len(tok_opt.tT.text)
                            p.filename = get_real_path(tok_opt.location[0])
                            oiL = [oi for oi in oiL if oi.subops[indx].v['param'] is not None and oi.subops[indx].v['param'].keyword == "identifier"]
                        else:
                            oiL = [oi for oi in oiL if oi.subops[indx].v['param'] is None or oi.subops[indx].v['param'].keyword != "identifier"]
                            if not oiL:
                                if noneOK:
                                    if tok_opt is not None:
                                        toks = prepend(tok_opt, toks)
                                    p = None
                                else:
                                    U.die("Expected identifier", *(tok_opt.location if tok_opt else tok.location))
                            else:
                                if tok_opt is not None:
                                    toks = prepend(tok_opt, toks)
                    
                    if p is None:
                        has_param = any(oi.subops[indx].v['param'] is not None for oi in oiL)
                        if has_param:
                            p, toks = getExpr(toks=toks, left=None, prio=precedence, opCtx=curOpCtx, noneOK=noneOK)
                            if p is not None:
                                kw = oiL[0].subops[indx].v['param'].keyword if (oiL and oiL[0].subops[indx].v['param']) else None
                                oiL = [oi for oi in oiL if oi.subops[indx].v['param'] is not None and \
                                       (oi.subops[indx].v['param'].keyword is None or astMatchesKeyword(p, oi.subops[indx].v['param'].keyword))]
                                if not oiL:
                                    U.die("Expected operand matching keyword constraints", *tok.location)
                            else:
                                oiL = [oi for oi in oiL if oi.subops[indx].v['param'] is None]

                    if p is not None:
                        oiL = [oiL[i] for i in range(len(oiL)) if oiL[i].subops[indx].v['param'] is not None]
                        #p = opFunAst(oiL[0].subops[indx].v['param'].oneAdjust, p)
                    else:
                        oiL = [oiL[i] for i in range(len(oiL)) if oiL[i].subops[indx].v['param'] is None]
                else:
                    assert len(oiL) == 1 or all(oiL[0].subops[indx].v['param'].subsubs == \
                            oiL[i].subops[indx].v['param'].subsubs for i in range(1, len(oiL)))
                    ssOpInfo = op.OpInfo(p, oiL[0].subops[indx].v['allAdjust'], \
                                         oiL[0].subops[indx].v['param'].ssParamLen, \
                                         oiL[0].subops[indx].v['param'].subsubs)
                    ssOpCtx = OpCtx(upOpCtx=opCtx, indx=0, altOpInfos=[ssOpInfo], token=opCtx.token)
                    oi, pl, toks = getSubops(toks, ssOpCtx, left=None)
                    assert oi == ssOpInfo
                    p = opFunAst(oiL[0].subops[indx].v['allAdjust'], A.AstTuple(members=pl))
                if p is not None: 
                    sopPs.append(p)
                tok = next(toks, None)
                if tok is None: break
                
            choicePos = oiL[0].subops[indx].v.get('choicePos')
            if choicePos is not None and isinstance(pAstL[choicePos], list):
                pAstL[choicePos] = A.AstTuple(members=tuple(pAstL[choicePos]))
                
            indx = indx + 1
            if indx == len(oiL[0].subops):
                if tok is not None:
                    toks = prepend(tok, toks)
                return oiL[0], pAstL[:oiL[0].paramLen], toks
    finally:
        if is_new_scope:
            global_scope_tracker.pop_scope()


# compiler.py should be really simple. It needs to coordinate with wombat.wh on the names
# of operators, and with wast.py. So if there is an operator Xyz then it generates
# and ast node AstXyz, and it passes the python tuple/list of operands as the parameter
# to AstXyz to sort out. Carry overs from the old version combined with misguided
# gemini activities have confused the code a lot.
def compiler(toks: Iterator[L.Token]) -> A.AstClosure:
    global global_scope_tracker
    global_scope_tracker = ScopeTracker()
    if not isinstance(toks, TrackingIterator):
        toks = TrackingIterator(toks)
    doMCTcmd('operator "ZeroTuple" ["!!defaultOperand"]', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0))) # dummy token
    doMCTcmd('operator "None" ["!!SOF"] ["!!EOF"]', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    doMCTcmd('operator "None" ["!!SOF"] () ["!!EOF"]', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "OneTuple" [","] (50)', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "NTuple" (50) ["," repeating1 prepend] (50)', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "OperatorPartialProcedure" (70) ["=>"] (69)', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "OperatorTotalProcedure" (70) ["=>>"] (69)', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "OperatorEmbedding" (70) ["<=>>"] (69)', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "Product" (80) ["*"] (80)', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "StructureInstance" ["@<"] () [">"]', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "FirstCase" (999) ["firstCase"] () ["of"] (999)', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "SubsetType" (90) ["//"] (91)', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "In" (85) ["in"] (85)', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "TypeCheck" (90) [":%"] (91)', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    #doMCTcmd('operator "PropCheck" (90) ["%"] (91)', L.Token(L.TokTT('', ''), -1, False, ('', 0, 0)))
    e, toks = getExpr(toks=toks, left=None, prio=None, opCtx=None, noneOK=False)
    assert e is not None
    c = A.AstClosure(e)
    #A.convert_free_variables(c)
    c.fixUp(parent=None, closure=None, upChain=())
    return c

import sys

class TraceIterator:
    def __init__(self, it):
        self.it = it
        self.history = []
    def __iter__(self):
        return self
    def __next__(self):
        try:
            val = next(self.it)
        except StopIteration:
            raise
        if val is not None:
            self.history.append(val)
        return val

if __name__ == "__main__":
    import lexer
    debug = len(sys.argv) > 2
    traced_toks = TraceIterator(lexer.lexer(sys.argv[1]))
    try:
        breakpoint()
        ast = compiler(traced_toks)
        for l in ast.pp(1): print(l)
    except Exception as e:
        print("CRASH HISTORY (last 30 tokens):")
        for t in traced_toks.history[-30:]:
            print(f"  {t.location}: {repr(t.tT.text)} (type={t.tT.tType})")
        raise e

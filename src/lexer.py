# lexer.py -- turn file into iterator of tokens

import collections as C
from collections.abc import Iterable
from typing import NamedTuple, Generator, Tuple, List, Dict, Optional, Pattern, Callable, Any, Union
import decimal
import re
import os
import utility as U

class TokTT(NamedTuple):
    text: str
    tType: str

class Token(NamedTuple):
    tT: TokTT
    indent: int
    whiteB4: bool
    location: Tuple[str, int, int]

class TokenClass(NamedTuple):
    tokRE: Pattern[str]
    #adjust: Optional[Callable[[str], str]]
    tType: str

class Found(NamedTuple):
    tokTT: TokTT
    length: int

white: Pattern[str] = re.compile(r"\s*") # always matches
upSlash: Pattern[str] = re.compile(r"\%\/")

tokenClassByPrio: Dict[decimal.Decimal, List[TokenClass]] = {}  # value for each TokenClass: list of (pattern,adjustment,tType)
tokenClassPrios: List[decimal.Decimal] = []   # keep sorted list of Prios, 

def insertTokenClass(prio: decimal.Decimal, tokenClass: TokenClass) -> None:
    global tokenClassPrios
    if prio in tokenClassByPrio:
        tokenClassByPrio[prio].append(tokenClass)
    else:
        tokenClassByPrio[prio] = [tokenClass]
        tokenClassPrios = sorted(list(tokenClassByPrio.keys()), reverse=True)

# We are going to put every subop in the operator-only pattern, but since it will
# have a lower priority it won't match identifiers anyway. This is a hack FIXME
def update_operator_only_pattern(symbols: Iterable[str], prio: decimal.Decimal = decimal.Decimal('10')) -> None:
    global tokenClassPrios
    #clean_symbols = [s for s in symbols if s and not s.isspace() and not re.match(r"^[a-zA-Z\u0370-\u03ff\u1f00-\u1ffe][_a-zA-Z0-9%\u0370-\u03ff\u1f00-\u1ffe]*'*$", s)]
    #if not clean_symbols:
    #    return
    #sorted_symbols = sorted(clean_symbols, key=len, reverse=True)
    sorted_symbols = sorted(symbols, key=len, reverse=True)
    pattern_str = r"(?P<token>`*(?:" + "|".join(re.escape(s) for s in sorted_symbols) + r")'*)"
    tc = TokenClass(tType="OperatorOnly", tokRE=re.compile(pattern_str))#, adjust=None)
    tokenClassByPrio[prio] = [tc]
    tokenClassPrios = sorted(list(tokenClassByPrio.keys()), reverse=True)

def lexer(fileName: str) -> Generator[Token, None, None]:
    lineNum = 0
    yield Token(tT=TokTT(text="!!SOF", tType="OperatorOnly"), indent=0, whiteB4=False,
               location=(fileName, 0, 0))
    # should allow %\ at end of line to split long lines (or %+ at start of next ?)
    with open(fileName, "r", encoding="utf-8") as f:
        for line in f:
            whiteB4 = True # at a new line
            lineNum += 1
            indentM = white.match(line)
            if indentM is None:
                continue # Should not happen with \s*
            indent = len(indentM[0]) # set to -1 after 1st token
            pos = indent
            if upSlash.match(line, indent):
                # lex command
                m = re.compile(r"include\s+(\S+)\n?").fullmatch(line, indent+2)
                if m:
                    include_path = os.path.join(os.path.dirname(fileName), m[1])
                    yield from lexer(include_path)  # recurse
                    breakpoint()
                else:
                    #e.g. %/token String 100 "U.unquote" (?P<token>"(\\"|\\\\|[^"\\])*")
                    n = re.compile(r'token\s+(\w+)\s+(\d+\.?\d*)\s+("(?:[^\\"]|\\.)*")?\s*([^\n]+)')\
                          .match(line, indent+2)
                    if n:
                        #print(n[4])
                        tokenClass = TokenClass(tType=n[1], tokRE=re.compile(n[4]))#,
                                                #adjust=U.evalCallable(U.unquote(n[3])))
                        insertTokenClass(decimal.Decimal(n[2]), tokenClass)
                    else:
                        raise Exception("unknown %/ cmd:"+line)
            else: # multiple ordinary tokens
                while pos != len(line):
                    found: Optional[Found] = None
                    for p in tokenClassPrios:
                        if found is not None:
                            break # must have found one at higher priority
                        for tc in tokenClassByPrio[p]:
                            tm = tc.tokRE.match(line, pos)
                            if tm:
                                tt = tm['token'] #if tc.adjust is None else tc.adjust(tm['token'])
                                tokTT = TokTT(text=tt, tType=tc.tType)
                                if found is not None:
                                    if found != Found(tokTT=tokTT, length=len(tm[0])):
                                        print("DEBUG CONFLICT: found =", found, "new =", tokTT, "len =", len(tm[0]), flush=True); U.die("conflicting tokens: " + found.tokTT.text + " " + tm['token'],
                                            fileName, lineNum, pos)
                                else:
                                    found = Found(tokTT=tokTT, length=len(tm[0]))
                    if found:
                        wm = white.match(line, pos + found.length)
                        gotWhite = (wm is not None) and (pos + found.length + len(wm[0]) == len(line) or len(wm[0]) > 0)
                        if found.tokTT.tType != 'Comment':
                            yield Token(tT=found.tokTT, indent=indent,
                                        whiteB4=whiteB4, location=(fileName, lineNum, pos))
                        whiteB4 = gotWhite
                        indent = -1
                        pos += found.length + (len(wm[0]) if wm else 0)
                    else:
                        # No token found, could be at end of line or error
                        if pos < len(line) and not line[pos:].isspace():
                             U.die("unrecognized token: " + line[pos:], fileName, lineNum, pos)
                             # Since die currently does nothing, we should probably break or raise
                             raise Exception(f"Unrecognized token at {fileName}:{lineNum}:{pos}")
                        pos = len(line)
    yield Token(tT=TokTT(text="!!EOF", tType="OperatorOnly"), indent=0, whiteB4=True,
               location=(fileName, lineNum + 1, 0))

###if __name__ == "__main__":
###    print("This test no longer works because operator declarations build the OperatorOnly RE\n")
###    # execute only if run as a script
###    import sys
###    if len(sys.argv) > 1:
###        for tok in lexer(sys.argv[1]):
###            print(tok)
###

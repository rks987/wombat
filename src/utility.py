from typing import Any, Callable, Generator, Iterable, Optional, TypeVar, Union
import re

T = TypeVar('T')

def die(s: str, fn: str, lineNum: int, pos: int) -> None:
    raise Exception(s + " in " + fn + "(" + str(lineNum) + "/" + str(pos) + ")")

def unquote(s: Optional[str]) -> Optional[str]: # remove leading/trailing " and convert \\ to \ and \" to "
    if s is None:
        return None
    if not s.startswith('"'):
        return s
    if s == '""':
        return '' # special case doesn't match following sanity check
    assert s[0] == '"' and s[-1] == '"' and s[1] != '"' and s[-2] != '\\' and re.search(r'[^\\]"', s[1:-1]) is None
    return re.sub(r'\\(.)', r'\1', s[1:-1])

###def findDeep(x: Any, it: Any) -> bool:
###    if x == it: 
###        return True
###    else:
###        try:
###            for lower in it:
###                if findDeep(x, lower):
###                    return True
###            return False
###        except TypeError: # should check for TypeError only? FIXME
###            return False
###
def evalCallable(s: Optional[str]) -> Optional[Callable[..., Any]]: # string s should give a callable, for None return None
    if s is None:
        return None
    rslt = eval(s)
    assert callable(rslt)
    return rslt


###class PushbackIterator:
###    def __init__(self, iterable):
###        self.underlying = iter(iterable)
###        self.buffer = []
###
###    def pushback(self, item):
###        self.buffer.append(item)
###
###    def __next__(self):
###        if self.buffer:
###            return self.buffer.pop()
###        return next(self.underlying)
###
###    def __iter__(self):
###        return self
###
###def prependGen(hd: T, tl: Iterable[T]) -> PushbackIterator:
###    if isinstance(tl, PushbackIterator):
###        tl.pushback(hd)
###        return tl
###    else:
###        p = PushbackIterator(tl)
###        p.pushback(hd)
###        return p
###
###if __name__=="__main__":
###    h = (x for x in range(1,3))
###    h = prependGen(0, h)
###    print(*h)

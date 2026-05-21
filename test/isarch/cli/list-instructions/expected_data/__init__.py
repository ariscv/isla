from .a import INSTRUCTIONS as a
from .b import INSTRUCTIONS as b
from .c import INSTRUCTIONS as c
from .fd import INSTRUCTIONS as fd
from .i import INSTRUCTIONS as i
from .k import INSTRUCTIONS as k
from .m import INSTRUCTIONS as m
from .svinval import INSTRUCTIONS as svinval
from .v import INSTRUCTIONS as v
from .zawrs import INSTRUCTIONS as zawrs
from .zcmop import INSTRUCTIONS as zcmop
from .zibi import INSTRUCTIONS as zibi
from .zicbom import INSTRUCTIONS as zicbom
from .zicbop import INSTRUCTIONS as zicbop
from .zicboz import INSTRUCTIONS as zicboz
from .zicond import INSTRUCTIONS as zicond
from .zicsr import INSTRUCTIONS as zicsr
from .zifencei import INSTRUCTIONS as zifencei
from .zihintntl import INSTRUCTIONS as zihintntl
from .zihintpause import INSTRUCTIONS as zihintpause
from .zimop import INSTRUCTIONS as zimop
from .zvabd import INSTRUCTIONS as zvabd
from .bfloat16 import INSTRUCTIONS as bfloat16
from .cfi import INSTRUCTIONS as cfi
from .sys import INSTRUCTIONS as sys
from .vector_crypto import INSTRUCTIONS as vector_crypto


_ALL_MODULES = [
    a,
    b,
    c,
    fd,
    i,
    k,
    m,
    svinval,
    v,
    zawrs,
    zcmop,
    zibi,
    zicbom,
    zicbop,
    zicboz,
    zicond,
    zicsr,
    zifencei,
    zihintntl,
    zihintpause,
    zimop,
    zvabd,
    bfloat16,
    cfi,
    sys,
    vector_crypto,
]


def get_all_instructions():
    result = {}
    for mod in _ALL_MODULES:
        result.update(mod)
    return result

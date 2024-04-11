from enum import Enum


class TypeInferenceMode(Enum):
    Z3 = 'z3'
    SIMPLESUB = 'simplesub'
    CHECKED = 'checked'
    DEFAULT = 'default'

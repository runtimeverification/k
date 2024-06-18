#!/usr/bin/env python

from pyk.kast.inner import KVariable
from pyk.konvert import _kast_to_kore
from pyk.prelude.kint import INT, intToken
from pyk.kore.parser import KoreParser
from pyk.kore.syntax import App, LeftAssoc
from pyk.kast.inner import KSort
from pathlib import Path
from pyk.ktool.krun import fuzz, kintegers

var_x = _kast_to_kore(KVariable('X', INT))
var_y = _kast_to_kore(KVariable('Y', INT))

init = KoreParser(Path('init_var.kore').read_text()).pattern()

lbl = "Lbl'UndsPipe'-'-GT-Unds'"

def check_output(p):
    def findres(p):
        if isinstance(p, App):
            if p.symbol == lbl:
                left = p.args[0]
                right = p.args[1]
                if left.args[0].value.value == 'res':
                    val = int(right.args[0].value.value)
                    assert val == 0
        return p

    p.args[0].args[1].args[0].pattern.top_down(findres)

def_dir = Path('imp-kompiled').resolve()
template = init
substs = {var_x: kintegers(with_inj=KSort('AExp')), var_y: kintegers(with_inj=KSort('AExp'))}
check_func = check_output

fuzz(def_dir, template, substs, check_func, max_examples=1000)

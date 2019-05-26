#!/usr/bin/env python3

import os.path as path
import sys
import re
import configparser

def write_spec_file(output_dir, spec_name, spec_defn):
    output_file = output_dir + '/' + spec_name + '-spec.k'
    with open(output_file, 'w') as spec_out:
        spec_out.write(spec_defn)
        print('Spec file: ' + output_file)

# TODO: for Python 3.5 or higher: z = {**x, **y}
def merge_two_dicts(x, y):
    z = dict(x)
    z.update(y)
    return z

def subst(text, key, val):
    return text.replace('{' + key.upper() + '}', val)

def subst_all(init_rule_spec, config):
    rule_spec = init_rule_spec
    for key in config:
        rule_spec = subst(rule_spec, key, config[key].strip())
    if rule_spec != init_rule_spec:
        return subst_all(rule_spec, config)
    else:
        return rule_spec

def safe_get(config, section):
    if section in config:
        return config[section]
    else:
        return {}

def inherit_get(config, section):
    if not section:
        return safe_get(config, 'root')
    else:
        parent = inherit_get(config, '-'.join(section.split('-')[:-1]))
        current = safe_get(config, section)
        merged = merge_two_dicts(parent, current) # TODO: for Python 3.5 or higher: {**parent, **current}
        for key in list(merged.keys()):
            if key.startswith('+'):
                merged[key[1:]] += merged[key]
                del merged[key]
        return merged

def gen_spec_rule(rule_template, pgm_config, rule_config, rule_name, trusted = False):
    rule_spec = rule_template
    for config in [ rule_config , pgm_config ]:
        rule_spec = subst_all(rule_spec, config)
    rule_spec = subst(rule_spec, 'rulename', rule_name)
    if trusted:
        rule_spec += '    [trusted]\n'
    return rule_spec

def gen_spec_rules(rule_template, spec_config, rule_name_list, trusted = False):
    pgm_config = spec_config['pgm']
    rule_spec_list = []
    lemma_names = set([])
    for rname in rule_name_list:
        rule_config = inherit_get(spec_config, rname)
        rule_spec = gen_spec_rule(rule_template, pgm_config, rule_config, rname, trusted = trusted)
        rule_spec_list.append(rule_spec)
        if not trusted and '_lemmas' in rule_config:
            lemma_names = lemma_names.union(set(rule_config['_lemmas'].split()))
    if len(lemma_names) > 0:
        rule_spec_list += gen_spec_rules(rule_template, spec_config, list(lemma_names), trusted = True)
    return rule_spec_list

def gen_spec_defn(spec_template, rule_template, spec_config, spec_name, output_dir):
    case_name_list_all = list(filter(lambda sec: sec.startswith(spec_name + '-'), spec_config.sections()))
    case_name_list = []

    for rname in case_name_list_all:
        if not any(sec_name.startswith(rname + '-') for sec_name in spec_config.sections()):
            case_name_list.append(rname)

    rules = '\n'.join( gen_spec_rules(rule_template, spec_config, [spec_name])
                     + gen_spec_rules(rule_template, spec_config, case_name_list, trusted = True)
                     )

    spec_defn_tmpl = subst(spec_template, 'module', spec_name.upper())
    spec_defn      = subst(spec_defn_tmpl, 'rules', rules)

    write_spec_file(output_dir, spec_name, spec_defn)

    if len(case_name_list) > 0:
        case_rules = '\n'.join(gen_spec_rules(rule_template, spec_config, case_name_list))

        spec_case_name      = spec_name + '_cases'
        spec_case_defn_tmpl = subst(spec_template, 'module', spec_case_name.upper())
        spec_case_defn      = subst(spec_case_defn_tmpl, 'rules', case_rules)

        write_spec_file(output_dir, spec_case_name, spec_case_defn)

def usage():
    exec_name = path.basename(sys.argv[0])
    usage_strs = [ 'usage: ' + sys.argv[0]
                 , ''
                 , '    ' + exec_name + ' <spec_defn_tmpl> <spec_rule_tmp> <spec_ini> <spec_name>*'
                 , ''
                 , '        <spec_defn_tmpl>: template K definition to use.'
                 , '        <spec_rule_tmpl>: template K rule specification to use.'
                 , '        <spec_ini>:       ini format file describing tree of K proofs.'
                 , '        <spec_name>:      name of specification to generate (defaults to pgm.specs).'
                 ]
    print('\n'.join(usage_strs))

if __name__ == '__main__':
    if len(sys.argv) < 4:
        usage()
        sys.exit(1)

    spec_defn_tmpl = open(sys.argv[1], 'r').read()
    spec_rule_tmpl = open(sys.argv[2], 'r').read()
    spec_ini_file  = sys.argv[3]
    output_dir     = path.abspath(path.dirname(spec_ini_file))

    spec_config = configparser.ConfigParser(comment_prefixes=(';'))
    spec_config.read(spec_ini_file)

    if 'pgm' not in spec_config.sections():
        print('File ' + spec_ini_file + ' must have a `pgm` section!')
        sys.exit(1)

    spec_names = sys.argv[4:]
    if len(spec_names) == 0:
        spec_names = spec_config['pgm']['specs'].split()

    for spec_name in spec_names:
        gen_spec_defn(spec_defn_tmpl, spec_rule_tmpl, spec_config, spec_name, output_dir)

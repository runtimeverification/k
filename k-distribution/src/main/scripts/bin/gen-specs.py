#!/usr/bin/env python3

import os.path as path
import sys
import re
import configparser

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

def gen_spec_rules(rule_template, spec_config, rule_name_list):
    if 'pgm' not in spec_config:
        print('''Must specify a "pgm" section in the .ini file.''')
        sys.exit(1)
    pgm_config = spec_config['pgm']
    rule_spec_list = []
    for name in rule_name_list:
        rule_spec = rule_template
        for config in [ inherit_get(spec_config, name) , pgm_config ]:
            rule_spec = subst_all(rule_spec, config)
        rule_spec = subst(rule_spec, "rulename", name)
        rule_spec_list.append(rule_spec)
    return "\n".join(rule_spec_list)

def gen_spec_defn(spec_template, rule_template, spec_config, spec_tree):
    rule_name_list_all = list(filter(lambda sec: sec.startswith(spec_tree + "-"), spec_config.sections()))
    rule_name_list = []

    for rname in rule_name_list_all:
        if not any(sec_name.startswith(sec + "-") for sec_name in secs):
            rule_name_list.append(rname)

    if len(rule_name_list) == 0:
        rule_name_list = [spec_tree]

    rules = gen_spec_rules(rule_template, spec_config, rule_name_list)

    spec_defn_tmpl = subst(spec_template, 'module', spec_tree.upper())
    spec_defn      = subst(spec_defn_tmpl, 'rules', rules)

    return spec_defn

def usage():
    usage_strs = [ "usage: " + sys.argv[0]
                 , ""
                 , "    " + sys.argv[0] + " <spec_defn_tmpl> <spec_rule_tmp> <spec_ini> <output_dir> <spec_tree_name>+"
                 , ""
                 , "        <spec_defn_tmpl>: template K definition to use."
                 , "        <spec_rule_tmpl>: template K rule specification to use."
                 , "        <spec_ini>:       ini format file describing tree of K proofs."
                 , "        <output_dir>:     directory to write K specs out to."
                 , "        <spec_tree_name>: subtree of specification names to generate."
                 ]
    print("\n".join(usage_strs))

if __name__ == '__main__':
    if len(sys.argv) < 6:
        usage()
        sys.exit(1)

    spec_defn_tmpl = open(sys.argv[1], "r").read()
    spec_rule_tmpl = open(sys.argv[2], "r").read()
    spec_ini_file  = sys.argv[3]
    spec_ini       = open(spec_ini_file, "r").read()
    output_dir     = sys.argv[4]

    spec_config = configparser.ConfigParser(comment_prefixes=(';'))
    spec_config.read(spec_ini)

    for spec_tree in sys.argv[5:]:
        spec_defn_str = gen_spec_defn(module_template, spec_template, spec_config, spec_tree)
        with open(output_dir + "/" + spec_tree + "-spec.k", "w") as spec_out:
            spec_out.write(spec_defn_str)

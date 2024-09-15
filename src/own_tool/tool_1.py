import sys
import z3
sys.path.append("/home/ekvashyn/Code/spacer-on-jupyter/src")

from spacer_tutorial import *
from chctools import chcmodel, horndb

# proof mode must be enabled before any expressions are created
z3.set_param(proof=True)
z3.set_param(model=True)

with open('prblm.smt2', 'r') as file:
    code = file.read()

ascii_art = r"""
███╗░░░███╗░█████╗░░██████╗░██╗░█████╗░██╗░░██╗███████╗░█████╗░██████╗░███╗░░░███╗
████╗░████║██╔══██╗██╔════╝░██║██╔══██╗╚██╗██╔╝██╔════╝██╔══██╗██╔══██╗████╗░████║
██╔████╔██║███████║██║░░██╗░██║██║░░╚═╝░╚███╔╝░█████╗░░██║░░██║██████╔╝██╔████╔██║
██║╚██╔╝██║██╔══██║██║░░╚██╗██║██║░░██╗░██╔██╗░██╔══╝░░██║░░██║██╔══██╗██║╚██╔╝██║
██║░╚═╝░██║██║░░██║╚██████╔╝██║╚█████╔╝██╔╝╚██╗██║░░░░░╚█████╔╝██║░░██║██║░╚═╝░██║
╚═╝░░░░░╚═╝╚═╝░░╚═╝░╚═════╝░╚═╝░╚════╝░╚═╝░░╚═╝╚═╝░░░░░░╚════╝░╚═╝░░╚═╝╚═╝░░░░░╚═╝
"""
print(ascii_art)

with open('prblm.smt2', 'r') as file:
    code = file.read()

#-----------------------------
Z = z3.IntSort()
B = z3.BoolSort()

def expand_quant(fml):
    """Expand quantifier into Quantifier, Variables, and Body."""
    if z3.is_quantifier(fml):
        gnd_vars = [z3.Const(fml.var_name(i), fml.var_sort(i)) for i in range(fml.num_vars())]
        gnd_body = z3.substitute_vars(fml.body(), *reversed(gnd_vars))
        quant = z3.Exists if fml.is_exists() else z3.ForAll
        return quant, gnd_vars, gnd_body
    else:
        return (lambda x, y: y), [], fml
    
def apply_to_each_expr(fml, fn, *args, **kwargs):
    """Apply given function to every sub-expression of a formula."""
    if fn(fml, *args, **kwargs):
        for child in fml.children():
            apply_to_each_expr(child, fn, *args, **kwargs)

#-----------------------------

def setup_fixedpoint():
    fp = z3.Fixedpoint()
    fp.set('spacer.max_level', 40)
    return fp

def parse_queries(fp, code):
    queries = fp.parse_string(code)
    assert len(queries) == 1
    fp.query(queries[0])
    return queries

def extract_rules(fp):
    return fp.get_rules()

#-----------------------------

def is_magic_num(v):
    return z3.is_int_value(v) and v.as_long() != 0

def has_comparison_operator(expr):
    comparison_ops = [z3.is_lt, z3.is_le, z3.is_gt, z3.is_ge, z3.is_eq, z3.is_distinct]
    return any(op(expr) for op in comparison_ops)

def find_magic_in_gnd_rule(rule):
    myset = set()

    def find_magic(x, found):
        if has_comparison_operator(x): 
            for arg in [x.arg(0), x.arg(1)]:
                if is_magic_num(arg):
                    found.add(arg)
            return False
        else:
            return True
        
    apply_to_each_expr(rule, find_magic, found=myset)
    return myset

def find_magic_in_rule(rule):
    _, _, b = expand_quant(rule)
    return find_magic_in_gnd_rule(b)

def find_magic_values(rules):
    return list(set().union(*map(find_magic_in_rule, rules)))

#-----------------------

def prepare_substitution(values):
    values_consts = [z3.IntVal(val) for val in values]
    values_vars = [z3.Int(f"K{val}") for val in values]
    values_vars = list(reversed(values_vars))
    return values_vars, [*zip(values_consts, values_vars)]

def apply_substitution(rules, substitutions):
    return [z3.substitute(rule, substitutions) for rule in rules]

def generate_additional_conditions(substitutions):
    return [(sub_var == sub_val) for sub_val, sub_var in substitutions]

#-----------------------

def process_first_rule(rules, substitutions):
    _, _, rule_body = expand_quant(rules[0])
    assert(z3.is_implies(rule_body))
    assert(z3.is_and(rule_body.arg(0)))
   
    additional_conditions = generate_additional_conditions(substitutions)
    upd_first_rule_tail = z3.And(*rule_body.arg(0).children(), *additional_conditions)
    rules[0] = z3.Implies(upd_first_rule_tail, rule_body.arg(1))
    return rules

def process_rules_and_queries(code):
    fp_rules, queries = setup_fixedpoint(code)
    magic_values = find_magic_values(fp_rules)
    print(f"magic_values={magic_values}")
    magic_values_vars, substitutions = prepare_substitution(magic_values)
    
    print(f"magic_values_vars={magic_values_vars}\n")
    print(f"substitutions={substitutions}")

    rules = process_first_rule(fp_rules, substitutions)
    print(f"magic_rules={rules}")
    return rules, queries, magic_values_vars

#-----------------------

def find_invs(gnd_rule_body, inv_name='inv'):
    found = set()

    def _is_inv_term(e, found):
        if e.decl().name() == inv_name:
            found.add(e)
            return False
        return True

    apply_to_each_expr(gnd_rule_body, _is_inv_term, found=found)
    return found

def append_sorts(inv_term, new_vars):
    inv2_sorts = [inv_term.decl().domain(i) for i in range(inv_term.decl().arity())]
    for v in new_vars:
        inv2_sorts.append(v.sort())
    inv2_sorts.append(B)
    return inv2_sorts

def mk_inv2_term(inv_term, new_vars):
    inv2_sorts = append_sorts(inv_term, new_vars)
    inv2_fdecl = z3.Function("inv2", *inv2_sorts)
    inv2_args = inv_term.children() + new_vars
    inv2_term = inv2_fdecl(*inv2_args)
    return inv2_term

def mk_rule_vars(rule):
    _, rule_vars, _ = expand_quant(rule)
    return rule_vars



def mk_new_rule(rule):
    def generate_rule_substitutions(rule_body, new_vars):
        subs = list()
        inv_terms = find_invs(rule_body)
        for inv_term in inv_terms:
            inv2_term = mk_inv2_term(inv_term, new_vars)
            subs.append((inv_term, inv2_term))
        return subs
    
    _, _, rule_body = expand_quant(rule)
    subs = generate_rule_substitutions(rule_body, magic_values_vars)
    new_body = z3.substitute(rule_body, subs)
    return new_body

#--------------------

def set_fixedpoint(new_rules, new_vars, additional_vars):
    fp_new = z3.Fixedpoint()
    inv2 = z3.Function('inv2', Z, Z, Z, Z, B)
    fp_new.register_relation(inv2)
    fp_new.register_relation(z3.Function('fail', B))
    fp_new.declare_var(*new_vars)
    fp_new.declare_var(*additional_vars)
    for new_rule in new_rules:
        fp_new.add_rule(new_rule)
    return fp_new

def write_to_file(fp_new, queries):
    with open('res1.smt2', 'w') as f:
        print(fp_new.to_string(queries), file=f)

def process_horn(sh_db, fp_rules):
    res, answer = solve_horn(fp_rules, max_unfold=40)
    if res == z3.sat:
        print(f"Is model valid? = {chcmodel.ModelValidator(sh_db, answer).validate()}")
        print(f"Answer = \n {answer.sexpr()}")
    elif res == z3.unsat:
        print(f"res = {res}")

fp = setup_fixedpoint()
queries = parse_queries(fp, code)
rules = extract_rules(fp)
magic_values = find_magic_values(rules)
magic_values_vars, substitutions = prepare_substitution(magic_values)

def main():
    raw_rules = apply_substitution(rules, substitutions)
    raw_rules = process_first_rule(raw_rules, substitutions)
    new_rules = [*map(mk_new_rule ,raw_rules)]
    new_vars = list(set().union(*map(mk_rule_vars ,raw_rules)))
    
    fp_new = set_fixedpoint(new_rules, new_vars, magic_values_vars)

    fp_rules = fp_new.get_rules()
    fp_rules.push(z3.Implies(queries[0], z3.BoolVal(False)))

    sh_db = horndb.HornClauseDb("prblm")
    sh_db.load_from_fp(fp_new, queries)

    process_horn(sh_db, fp_rules)

    write_to_file(fp_new, queries)
    # print(fp_new.to_string(queries))

if __name__ == '__main__':
    main()
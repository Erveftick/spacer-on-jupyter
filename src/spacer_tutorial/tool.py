import sys
sys.path.insert(0, "/home/ekvashyn/Code/z3/build/python")

import z3
from spacer_tutorial import *

# proof mode must be enabled before any expressions are created
z3.set_param(proof=True)
z3.set_param(model=True)
# print expressions with HTML
z3.set_html_mode(True)

with open('prblm.smt2', 'r') as file:
    code = file.read()

# Type of code that usually locates in prblm.smt2 file
#  
# code = """
# (declare-rel inv (Int Int ))
# (declare-var x0 Int)
# (declare-var x1 Int)
# (declare-var y0 Int)
# (declare-var y1 Int)
# (declare-var z1 Int)

# (declare-rel fail ())

# (rule (=> (and (= x0 0) (= y0 5000))
#     (inv x0 y0)))

# (rule (=> (and
#         (inv x0 y0)
#         (= x1 (+ x0 1))
#         (= y1 (ite (>= x0 5000) (+ y0 1) y0)))
#     (inv x1 y1)))

# (rule (=> (and (inv x0 y0) (= x0 10000)
#     (not (= y0 x0))) fail))

# (query fail)
# """
def expand_quant(fml):
    """ Expands quantifier into Quantifier, Variables, and Body
    
        The result is a triple (Q, vars, body), such that Q(vars, body) is equivalent to fml
        All variables in body are ground (i.e., regular constants)
    """
    if z3.is_quantifier(fml):
        gnd_vars = [z3.Const(fml.var_name(i), fml.var_sort(i)) for i in range(fml.num_vars())]
        gnd_body = z3.substitute_vars(fml.body(), *reversed(gnd_vars))
        quant = z3.Lambda
        if fml.is_exists():
            quant = z3.Exists
        elif fml.is_forall():
            quant = z3.ForAll
        return quant, gnd_vars, gnd_body
    else:
        return (lambda x, y : y), [], fml
def for_each_expr(fml, fn, *args, **kwargs):
    """ Execute given function fn on every sub-expression 
    
        The return value of fn is used to decided whether children should be explored

        Additional arguments are passed to fn and can be used to maintain state
    """

    do_kids = fn(fml, *args, **kwargs)

    if not do_kids: return
    for k in fml.children():
        for_each_expr(k, fn, *args, **kwargs)
fp = z3.Fixedpoint()
queries = fp.parse_string(code)
fp.set('spacer.max_level', 40)
fp.query(queries[0])
rules = fp.get_rules()
def is_magic_num(v):
    return z3.is_int_value(v) and v.as_long() != 0

def has_comparison_operator(expr):
    comparison_ops = [
        z3.is_lt,
        z3.is_le,
        z3.is_gt,
        z3.is_ge,
        z3.is_eq,
        z3.is_distinct]

    if any(op(expr) for op in comparison_ops):
        return True

    return False
def find_magic_in_rule(rule):
    q, v, b = expand_quant(rule)
    return find_magic_in_gnd_rule(b)

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
        
    for_each_expr(rule, find_magic, found=myset)
    return myset
# Find the magic values to substitute
magic_values = list(set().union(*map(find_magic_in_rule, rules)))

# Z3 constants for values
const_values = [z3.IntVal(val) for val in magic_values]

# Create a variable for each magic value for substitution
magic_values_vars = [z3.Int(f"K{val}") for val in magic_values]

# Create a dictionary for substitutions
substitutions = [*zip(const_values, magic_values_vars)]

# Substitute variables in parsed rules and queries
ugly_rules = [z3.substitute(rule, substitutions) for rule in fp.get_rules()]
def find_invs(gnd_rule_body):
    found = set()
    def is_inv_term(e, found):
        if e.decl().name() == 'inv':
            found.add(e)
            return False
        return True
    
    for_each_expr(gnd_rule_body, is_inv_term, found=found)
    return found
Z = z3.IntSort()
B = z3.BoolSort()

def mk_inv2_term(inv_term, new_vars):
    inv2_sorts = [inv_term.decl().domain(i) for i in range(inv_term.decl().arity())]
    vrev = list(reversed(new_vars))
    for v in vrev:
        inv2_sorts.append(v.sort())
    inv2_sorts.append(B)
    inv2_fdecl = z3.Function("inv2", *inv2_sorts)
    inv2_args = inv_term.children() + vrev
    inv2_term = inv2_fdecl(*inv2_args)
    return inv2_term

def mk_new_rule_vars(rule):
    q, rule_vars, rule_body = expand_quant(rule)
    return rule_vars

def mk_new_rule(rule):
    subs = list()
    q, rule_vars, rule_body = expand_quant(rule)
    inv_terms = find_invs(rule_body)
    for inv_term in inv_terms:
        inv2_term = mk_inv2_term(inv_term, magic_values_vars)
        subs.append((inv_term, inv2_term))

    new_body = z3.substitute(rule_body, subs)
    # for every ground body, apply z3.substitute with the above subs
    return new_body

new_ugly_rules = [*map(mk_new_rule ,ugly_rules)]
new_ugly_vars = list(set().union(*map(mk_new_rule_vars ,ugly_rules)))

fp_new = z3.Fixedpoint()
fp_new.register_relation(z3.Function('inv2', Z, Z, Z, Z, B))
fp_new.register_relation(z3.Function('fail', B))
fp_new.declare_var(*new_ugly_vars)
fp_new.declare_var(*magic_values_vars)
for new_ugly_rule in new_ugly_rules:
    fp_new.add_rule(new_ugly_rule)
# print(fp_new.to_string(queries))

with open('res.smt2', 'w') as f:
    print(fp_new.to_string(queries), file=f)
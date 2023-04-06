import sage.all
import functools
from sage.calculus.var import var, function
from sage.calculus.functional import diff
from sage.symbolic.operators import FDerivativeOperator
from functools import reduce
from operator import __mul__
import more_itertools
import re
from sage.misc.html import html
from IPython.core.debugger import set_trace
import sage.symbolic.operators
from sage.graphs.graph import Graph
from anytree import Node, RenderTree, AnyNode, NodeMixin, PreOrderIter


@functools.cache
def eq(d1, d2):
    '''This cheap trick gives as a lot of performance gain (> 80%!)
    because maxima comparisons are expensive,and we can expect
    a lot of the same comparisons over and over again.
    All other caching is neglegible compared to this here
    70 % of the time is spent here!
    '''
    return bool(d1 == d2)


def tangent_vector(f):
    # https://doc.sagemath.org/html/en/reference/manifolds/sage/manifolds/differentiable/tangent_vector.html?highlight=partial%20differential
    # XXX:  There is TangentVector in Sage but a little bit more complicated.
    # Does it pay to use that one ?
    r"""
    Do a tangent vector

    DEFINITION:

    missing

    INPUT:

    - ``f`` - symbolic expression of type 'function'

    OUTPUT:

    the tangent vector

    .. NOTE::

    none so far

    ..

    EXAMPLES: compute the tangent vector of

    ::
    sage: from delierium.helpers import tangent_vector
    sage: x,y,z = var ("x y z")
    sage: tangent_vector (x**2 - 3*y**4 - z*x*y + z - x)
    [-y*z + 2*x - 1, -12*y^3 - x*z, -x*y + 1]
    sage: tangent_vector (x**2 + 2*y**3 - 3*z**4)
    [2*x, 6*y^2, -12*z^3]
    sage: tangent_vector (x**2)
    [2*x]
    """
    t = var("t")
    newvars = [var("x%s" % i) for i in f.variables()]
    for o, n in zip(f.variables(), newvars):
        f = f.subs({o: o+t*n})
    d = diff(f, t).limit(t=0)
    return [d.coefficient(_) for _ in newvars]


@functools.cache
def order_of_derivative(e, required_len=0):
    '''Returns the vector of the orders of a derivative respect to its variables

    >>> x,y,z = var ("x,y,z")
    >>> f = function("f")(x,y,z)
    >>> d = diff(f, x,x,y,z,z,z)
    >>> from delierium.helpers import order_of_derivative
    >>> order_of_derivative (d)
    [2, 1, 3]
    '''
    opr = e.operator()
    opd = e.operands()
    if not isinstance(opr, sage.symbolic.operators.FDerivativeOperator):
        return [0] * max((len(e.variables()), required_len))
    res = [opr.parameter_set().count(i) for i in range(len(opd))]
    return res


def is_derivative(e):
    '''checks whether an expression 'e' is a pure derivative

    >>> from delierium.helpers import is_derivative
    >>> x = var('x')
    >>> f = function ('f')(x)
    >>> is_derivative (f)
    False
    >>> is_derivative (diff(f,x))
    True
    >>> is_derivative (diff(f,x)*x)
    False
    '''
    try:
        return isinstance(e.operator(), FDerivativeOperator)
    except AttributeError:
        return False

def is_function(e):
    '''checks whether an expression 'e' is a pure function without any
    derivative as a factor

    >>> x = var('x')
    >>> f = function ('f')(x)
    >>> is_function (f)
    True
    >>> is_function (diff(f,x))
    False
    >>> is_function (x*diff(f,x))
    False
    >>> is_function (x*f)
    False
    '''
    if hasattr(e, "operator"):
        return "NewSymbolicFunction" in e.operator().__class__.__name__ and \
            e.operands() != []
    return False


def compactify(*vars):
    pairs = list(more_itertools.pairwise(vars))
    if not pairs:
        return [vars[0]]
    result = []
    for pair in pairs:
        if isinstance(pair[0], Integer):
            continue
        elif isinstance(pair[1], Integer):
            result.extend([pair[0]] * pair[1])
        else:
            result.append(pair[0])
    return result


@functools.cache
def adiff(f, context, *vars):
    use_func_diff = any("NewSymbolicFunction" in v.__class__.__name__ for v in vars)
    for op in f.operands():
        if "NewSymbolicFunction" in op.operator().__class__.__name__ :
            use_func_diff = True
    if use_func_diff:
        for v in vars:
            if "NewSymbolicFunction" in v.__class__.__name__:
                f = func_diff(f,  v(context._independent[1]))
            else:
                xx = SR.var("xx")
                gg = f.subs({context._independent[0](context._independent[1]):xx})
                gg = diff(gg, v)
                f=gg.subs({xx:context._independent[0](context._independent[1])})
    else:
        f = f.diff(*vars)
    return f


def is_op_du(expr_op, u):
    is_derivative = isinstance(
        expr_op,
        sage.symbolic.operators.FDerivativeOperator
    )
    if is_derivative:
        # Returns True if the differentiated function is `u`.
        return expr_op.function() == u.operator()
    else:
        return False


def iter_du_orders(expr, u):
    for sub_expr in expr.operands():
        if sub_expr == []:
            # hit end of tree
            continue
        elif is_op_du(sub_expr.operator(), u):
            # yield order of differentiation
            yield len(sub_expr.operator().parameter_set())
        else:
            # iterate into sub expression
            for order in iter_du_orders(sub_expr, u):
                yield order


def func_diff(L, u_in):
    """ `u` must be a callable symbolic expression
    """
#    https://ask.sagemath.org/question/7929/computing-variational-derivatives/
    x = u_in.variables()[0]
    u = u_in.function(x)

    # This variable name must not collide
    # with an existing one.
    # who will call a variable "tapir"
    # nobody else does this...
    t = SR.var('tapir')
    result = SR(0)

    # `orders` is the set of all
    # orders of differentiation of `u`
    orders = set(iter_du_orders(L, u)).union((0,))

    for c in orders:
        du = u(x).diff(x, c)
        sign = Integer(-1)**c

        # Temporarily replace all `c`th derivatives of `u` with `t`;
        # differentiate; then substitute back.
        dL_du = L.subs({du: t}).diff(t).subs({t: du})

        # Append intermediate term to `result`
        result += sign * dL_du.diff(x, c)

    return result


class ExpressionGraph:
    '''simple internal helper class
    analyzes the expression as a tree and stores the latex expression
    for each subexpression
    stolen from https://ask.sagemath.org/question/58145/tree-representing-an-expression/
    and adapted accordingly, quick 'n dirty
    '''
    def __init__(self, expr):
        self.G = Graph()
        self.i = 0
        self.expr = expr
        self.root = None
        self.latex_names = {}
        self.funcs_found = set()
        self.graph_expr(self.expr)
    def plot(self, *args, **kwds):
        #print ("root is {0}".format(self.root))
        return self.G.plot(*args, layout='tree', tree_root=self.root, **kwds)
    def graph_expr(self, expr):
        #print("."*80)
        #print (expr, expr.__class__)
        #set_trace()
        self.latex_names[str(expr)] = expr._latex_()
        try:
            operator = expr.operator()
        except AttributeError:  # e.g. if expr is an integer
            operator = None
        #print(f"{operator=} {operator.__class__=}")
        if operator is None:
            name = "[{0}] {1}".format(self.i, expr)
            #print(f"{self.i=}")
            #print(f"(leaf) {expr=} {expr.__class__=}")
            self.latex_names[str(expr)] = expr._latex_()
            self.i += 1
            self.G.add_vertex(name)
            return name
        else:
            try:
                name = "[{0}] {1}".format(self.i, operator.__name__)
                #print(f"named {self.i=} {name=}")
            except AttributeError:
                if "FDerivativeOperator" in operator.__class__.__name__:
                    self.latex_names[str(operator.function())] = operator.function()._latex_()
                    name = "FDerivativeOperator"
                    #print(f"unnamed {self.i=} {name=}")
                elif "NewSymbolicFunction" in operator.__class__.__name__:
                    name = "[{0}] {1}".format(self.i, str(operator))
                    #print(f"unnamed {self.i=} {name=}")
                    self.funcs_found.add(expr)
                    #print("AAA")
                else:
                    name = "[{0}] {1}".format(self.i, str(operator))
                   # print(f"unnamed {self.i=} {name=}")
            try:
                self.latex_names[str(operator)] = operator._latex_()
            except AttributeError:
                self.latex_names[str(expr)] = expr._latex_()
            if self.i == 0:
                self.root = name
                #print("  ** root is '{0}' **".format(self.root))
            self.i += 1
            new_nodes = []
            #print(f"{expr.operands()=}")
            for opnd in expr.operands():
                new_nodes += [self.graph_expr(opnd)]
            self.G.add_vertex(name)
            self.G.add_edges([(name, node) for node in new_nodes])
            return name


def latexer(e):
    re_diff1 = re.compile(r".*(?P<D>D\[)(?P<vars>.+)\]\((?P<f1>[^\)]+)\)\((?P<args>\S*\), [^)]\)).*")
    nakedf   = re.compile(r"^(?P<fname>\w+)\(.*$")
    pat = r".*(diff\((?P<funcname>\w+)(?P<vars>\([a-zA-Z ,]+\)), (?P<diffs>[a-zA-Z ,]+)\))"
    r=re.compile(r"%s" % pat)
    teststring=str(e.expand())

    graph       = ExpressionGraph(e)
    latexdict   = graph.latex_names
    funcs_found = graph.funcs_found
    funcabbrevs = set()
    while match := r.match(teststring):
        # check 'diff'
        res = "%s_{%s}" % (match.groupdict()["funcname"], ",".join (match.groupdict()["diffs"].split(",")))
        funcabbrevs.add((match.groupdict()["funcname"] + ",".join(match.groupdict()["vars"]) , match.groupdict()["funcname"]))
        teststring = teststring.replace(match.groups(0)[0], res)
    while match := re_diff1.match(teststring):
        # check 'D[...]'
        #set_trace()
        params  = match.groupdict()["args"].split(",")
        params  = [_.strip() for _ in params]
        # XXX not sure this will work properly. What if params is ['y(x)']
        # and not ['y(x)','x)'] ? in that case we will fail ...
        params[-1] = params[-1].replace(")", "")
        fu      = params[0]
        vv      = [int(_) for _ in match.groupdict()["vars"].split(",")]

        f1 = match.groupdict()["f1"]
        to_replace = "".join(("D[", match.groupdict()["vars"],"]",
                             "(",  f1, ")(",
                             match.groupdict()["args"]))
        vars = [_.replace(")","") for _ in params][1:]
        downvar = ""
        for _v in vv:
            if m := nakedf.match(params[_v]):
                downvar += ",".join(m.groupdict()["fname"])
            else:
                downvar += params[_v]
        teststring = teststring.replace(to_replace,
                                        r" %s_{%s}" % (f1, downvar)
                                       )
        teststring = teststring.replace(f1, latexdict.get(f1, f1))
        args = match.groupdict()["args"][:-1] # remove trailing ")"
        args = args.split(",")
        funcabbrevs.add((args[0], nakedf.match(args[0]).groupdict()["fname"]))

    for f in funcs_found:
        # matches phi(y(x), x) with:
        # outer = phi
        # inner = y
        # innervars = x
        # outervars = x
        #set_trace()
        nested_function = re.compile(r"^(?P<outer>\w+)\((?P<inner>\w+)\((?P<innervars>[\w+ ,]+)\), (?P<outervars>[\w ,]+)\)$")
        if match := nested_function.match(str(f)):
            res = "%s(%s(%s), %s)" % (
                match.groupdict()["outer"],
                match.groupdict()["inner"],
                match.groupdict()["innervars"],
                match.groupdict()["outervars"])
            teststring = teststring.replace(res, match.groupdict()["outer"])

    for f in funcs_found:
        simple_function = re.compile(r"^(?P<outer>\w+)\((?P<args>[\w ,]+)\)$")
        # matches y(x, z) with:
        # outer = y
        # args = x, z
        # matches  y(x) with:
        # outer = y
        # args = x
        if match := simple_function.match(str(f)):
            res = "%s(%s)" % (match.groupdict()["outer"], match.groupdict()["args"])
            teststring = teststring.replace(res, match.groupdict()["outer"])
    for fu in funcabbrevs:
        teststring = teststring.replace(fu[0], fu[1])
    return teststring.replace("*", " ")


class ExpressionTree:
    '''simple internal helper class
    analyzes the expression as a tree and stores the latex expression
    for each subexpression
    stolen from https://ask.sagemath.org/question/58145/tree-representing-an-expression/
    and adapted accordingly, quick 'n dirty
    '''
    def __init__(self, expr):
        self.root = None
        self.latex_names = {}        
        self.gschisti = set()
        self._expand(expr, self.root)
        self.diffs  = set([node.value for node in PreOrderIter(self.root) if node.value.operator().__class__ == FDerivativeOperator])
        self.funcs  = set([node.value for node in PreOrderIter(self.root) if node.value.operator().__class__.__name__ == 'NewSymbolicFunction'])
        self.powers = set([node.value for node in PreOrderIter(self.root) if str(node.value.operator()) == '<built-in function pow>'])            
        self.latex  = set([(node.value, node.latex) for node in PreOrderIter(self.root)])
    
    def _expand(self, e, parent):            
        try:
            opr = e.operator()
        except AttributeError:  # e.g. if expr is an integer
            opr = None       
        l = ""
        if opr:                
            if "FDerivativeOperator" in opr.__class__.__name__:
                l = "%s_{%s}" % (opr.function()._latex_(), ",".join([str(_) for _ in e.operands()]))
            elif "NewSymbolicFunction" in opr.__class__.__name__:
                l = opr._latex_()
            else:
                try:
                    l = e._latex_()
                except AttributeError:
                    l = ""
        try:
            self.latex_names[str(opr)] = opr._latex_()
        except AttributeError:
            self.latex_names[str(e)] = e._latex_()
            
        n = Node(str(e), value = e, operator = opr, parent = parent, latex = l)
        self.root = n if self.root is None else self.root
        if opr is not None:
            try:
                ops = e.operands()
            except AttributeError:  # can that really happen?
                ops = []
            for o in ops:
                if "FDerivativeOperator" in o.operator().__class__.__name__:
                    self.gschisti.add(o)
                if hasattr(o.operator(), "__name__") and o.operator().__name__ == "pow":
                    for _o in o.operands():
                        if "FDerivativeOperator" in _o.operator().__class__.__name__:
                            self.gschisti.add(o)
                            self.gschisti.add(e)
                self._expand(o, n)

# ToDo (from AllTypes.de
#    cfdgfdgfd
# CommutatorTable
# DterminingSystem
# Free Resolution
# Gcd
# Groebner Basis
# In?
# Intersection
# JanetBasis
# Lcm
# LöwDecomposioipn
# Primary Decomposition
# Product
# Qutiont
# Radical
# Random
# Saturation
# Sum
# Symmetric Power
# # Syzygys


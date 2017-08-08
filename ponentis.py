from itertools import chain
import heapq
from functools import reduce
import collections
import sys
# An expression is just a tuple. We don't have to worry about that.

EXTRA_VARIABLE_PENALTY = 5
EXTRA_TERM_PENALTY = 0
SIZE_PENALTY = 0.1
BACKWARD_EXPANSION_REDUCTION = .3

def size_estimate(expression):
    if isinstance(expression, collections.Iterable):
        return sum(size_estimate(x) for x in expression)
    else:
        return 1

# There are two types of atoms. Variables, and Globals.
class Variable:
    _id = 0
    def __init__(self, name):
        Variable._id += 1
        self.id = Variable._id
        self.name = name

    def __hash__(self):
        return hash(self.id)

    def __eq__(self, other):
        if not isinstance(other, Variable):
            return False

        return other.id == self.id

DEFAULT = 0
BINARY_INFIX = 1
class Global:
    _id = 0
    def __init__(self, name, print_style = DEFAULT):
        Variable._id += 1
        self.id = Variable._id
        self.name = name
        self.print_style = print_style

    def __hash__(self):
        return hash(self.id)

    def __eq__(self, other):
        if not isinstance(other, Global):
            return False

        return other.id == self.id

# Utility functions
def get_variables(expression):
    if isinstance(expression, Variable):
        return frozenset((expression,))
    elif isinstance(expression, collections.Iterable):
        return reduce((lambda x, y: x | y), (get_variables(x) for x in expression), frozenset())
    else:
        return frozenset()

def substitute(expression, mapping):
    if expression in mapping:
        return mapping[expression]
    elif isinstance(expression, tuple):
        return tuple(substitute(x, mapping) for x in expression)
    else:
        return expression

# An Axiom relates a collection of inputs to an output.
class Axiom:
    standard_variables = []

    def __init__(self, inputs, output, name, cost = 1.0):
        self.cost = cost
        self.name = name
        all_vars = reduce((lambda x, y: x | y), (get_variables(x) for x in inputs), frozenset())

        while len(all_vars) > len(Axiom.standard_variables):
            Axiom.standard_variables.append(Variable(chr(ord('a') + len(Axiom.standard_variables))))

        mapping = {v: Axiom.standard_variables[i] for i, v in enumerate(all_vars)}

        self.inputs = frozenset(substitute(x, mapping) for x in inputs)
        self.output = substitute(output, mapping)
        self.required_bindings = frozenset(Axiom.standard_variables[:len(all_vars)])

    def print(self):
        '''
        r = []
        for expr in self.inputs:
            r.append(expr)
            r.append(',')
        r = r[:-1]

        r.append('=>')
        r.append(self.output)

        #return '%s => %s' % (' && '.join(print_expr(x) for x in self.inputs), print_expr(self.output))
        return print_expr(r)
        '''
        return self.name

    def is_strictly_worse_than(self, other):
        return self.output == other.output and self.inputs >= other.inputs

    def __hash__(self):
        return hash((self.inputs, self.output))

    def __eq__(self, other):
        return (self.inputs == other.inputs) and self.output == other.output

class NodeReader:
    def __init__(self, node, expressions = None):
        if expressions is not None:
            self.expressions = expressions
        else:
            self.expressions = node.expressions

    def __hash__(self):
        return hash(self.expressions)

    def __eq__(self, other):
        if isinstance(other, NodeReader):
            return self.expressions == other.expressions
        else:
            return False

class ExistsNodeReader:
    standard_vars = []

    def depth(self):
        return self.subnode.depth() + 1

    def __init__(self, node, var = None, subnode = None):
        # Change all of the variables to standard variables
        # so that equality can be compared.
        if node is None:
            self.var = var
            self.subnode = subnode

        else:
            node_chain = [node]
            while isinstance(node_chain[-1], ExistsNode):
                if len(node_chain) > len(ExistsNodeReader.standard_vars):
                    ExistsNodeReader.standard_vars.append(
                        Variable(chr(ord('A')+len(ExistsNodeReader.standard_vars)))
                    )
                node_chain.append(node_chain[-1].subnode)

            expressions = node_chain[-1].expressions

            # Determine which standard variable to take
            node = NodeReader(
                None,
                expressions = frozenset(substitute(x,
                    {n.var: ExistsNodeReader.standard_vars[i] for i, n in enumerate(node_chain[:-1])}
                ) for x in expressions)
            )

            for i in range(len(node_chain) - 2):
                node = ExistsNodeReader(
                    None,
                    var = ExistsNodeReader.standard_vars[i],
                    subnode = node
                )

            self.var = ExistsNodeReader.standard_vars[len(node_chain) - 2]
            self.subnode = node

    def __hash__(self):
        return hash((self.var, self.subnode))

    def __eq__(self, other):
        if isinstance(other, ExistsNodeReader):
            return other.var == self.var and other.subnode == self.subnode
        else:
            return False

def print_expr(expr, vnames = None, vcounters = None):
    if vnames is None:
        vnames = {}
    if vcounters is None:
        vcounters = {}

    if expr is None:
        return 'None'

    if isinstance(expr, Variable):
        if expr in vnames:
            return vnames[expr]
        elif expr.name in vcounters:
            vcounters[expr.name] += 1
            vnames[expr] = '%s%d' % (expr.name, vcounters[expr.name])
            return vnames[expr]
        else:
            vcounters[expr.name] = 0
            vnames[expr] = expr.name
            return expr.name

    elif isinstance(expr, Global):
        return expr.name

    elif expr[0] == 'exists':
        return '\u2203%s.%s' % (print_expr(expr[1], vnames, vcounters), print_expr(expr[3], vnames, vcounters))

    elif expr[0] == 'conjunction':
        return ' \u2227 '.join(print_expr(x, vnames, vcounters) for x in expr[1])

    elif isinstance(expr, str):
        return expr

    elif isinstance(expr[0], Global) and expr[0].print_style == BINARY_INFIX:
        return '(%s %s %s)' % (print_expr(expr[1]), expr[0].name, print_expr(expr[2]))

    elif len(expr) == 1:
        return print_expr(expr[0], vnames, vcounters)

    else:
        return '(%s)' % (' '.join(print_expr(x, vnames, vcounters) for x in expr))

# A Node in the search graph. (expressions) is a tuple of tuples,
# where each tuple is an expression, and the Node represents their conjunction.
# It knows how to FORWARD expand.
class Node:
    _id = 0
    def depth(self):
        return 0

    def __init__(self, expressions, prev = None, cost = 0):
        Node._id += 1
        self.id = Node._id

        self.expressions = expressions
        self.prev = prev
        self.cost = cost

    def read(self):
        return NodeReader(self)

    # FORWARD EXPANSION using AXIOM and statement INDEX
    def forward_expand_axiom_index(self, axiom, expression):
        #print('Trying forward expansion', axiom.print(), 'with', print_expr(expression))
        # FORWARD PASS
        # ============
        bindings = {}

        def check_validity(axiom_output, my_expression):
            if not isinstance(axiom_output, tuple):
                if isinstance(axiom_output, Variable):
                    if axiom_output in bindings:
                        return bindings[axiom_output] == my_expression
                    else:
                        bindings[axiom_output] = my_expression
                        return True
                else:
                    return axiom_output == my_expression

            # If we're a variable and they're not, ho boy wuh oh
            if not isinstance(my_expression, tuple):
                return False

            # If we're different lengths something's wrong.
            if len(axiom_output) != len(my_expression):
                return False

            # Check every child.
            return all(check_validity(a, m) for a, m in zip(axiom_output, my_expression))

        # Check validity and generate bindings
        if not check_validity(axiom.output, expression):
            #print('failed.')
            return None

        # Hey, we're valid! Bindings have been generated, too.
        # Substitute them into the axiom inputs.
        new_expressions = (substitute(x, bindings) for x in axiom.inputs)

        # LEFTOVERS PROCEDURE
        # ===================

        # See if there were any leftover variables that need to be turned into Exists.
        leftovers = axiom.required_bindings - frozenset(bindings.keys())

        # Create Exists variables for each of the leftover bindings
        leftover_bindings = {x: Variable(x.name) for x in leftovers}

        new_expressions = frozenset(substitute(x, leftover_bindings) for x in new_expressions)

        # Concatenate together the new expressions.
        result = Node(self.expressions - frozenset((expression,)) | new_expressions, prev = (axiom, self),
                cost = (
                    self.cost + axiom.cost + EXTRA_VARIABLE_PENALTY * len(leftovers) +
                    EXTRA_TERM_PENALTY * (len(new_expressions) - 1) + SIZE_PENALTY * (size_estimate(new_expressions) - size_estimate({expression}))
                )
        )

        # And exists nodes
        for var in leftover_bindings.values():
            result = ExistsNode(var, result, prev = (axiom, self))
        #print('success! as %d' % (result.id,))

        # Return.
        return result

    def forward_expand_axiom(self, axiom):
        return (x for x in (self.forward_expand_axiom_index(axiom, expr) for expr in self.expressions) if x is not None)

    def forward_expand(self, axiom_list):
        return (x for axiom in axiom_list for x in self.forward_expand_axiom(axiom))

    def expand(self, axiom_list):
        return self.forward_expand(axiom_list)

    def replace_innermost_node(self, node):
        return node

    def expr_for_printing(self):
        return ('conjunction', self.expressions)

    def print(self):
        return print_expr(self.expr_for_printing())

    def innermost_expressions(self):
        return self.expressions

    def __le__(self, other):
        return self.cost <= other.cost

    def __ge__(self, other):
        return self.cost >= other.cost

    def __lt__(self, other):
        return self.cost < other.cost

    def __gt__(self, other):
        return self.cost > other.cost
    '''

    def __le__(self, other):
        return self.depth() <= other.depth() or self.depth() == other.depth() and self.cost <= other.cost

    def __ge__(self, other):
        return self.depth() >= other.depth() or self.depth() == other.depth() and self.cost >= other.cost

    def __lt__(self, other):
        return self.depth() < other.depth() or self.depth() == other.depth() and self.cost < other.cost

    def __gt__(self, other):
        return self.depth() > other.depth() or self.depth() == other.depth() and self.cost > other.cost
    '''

# An ExistsNode is a wrapper for an expression where a variable is unbound
# and possibilities for it need to be explored.

# ExistsNodes expand *both* forward and backward.
# In a FORWARD expansion, it simply FORWARD expands its subnode, keeping the wrapper.
# In a BACKWARD expansion, it looks at the first expression of its innermost subnode. It may look like (= (* 2 b) 3)
#   This first expression must be the output of some axiom, if it is to be true.
#   So the BACKWARD expansion looks for axioms that match its pattern in the backward sense, substitutes it everywhere else, and lets it sit there.
#   In the backward sense, like (= (* a (/ b a)) b)
#   matches in the backward sense. You do a forward application.
class ExistsNode(Node):
    def __init__(self, var, subnode, prev = None):
        self.var = var
        self.subnode = subnode
        self.cost = self.subnode.cost
        self.prev = prev

        Node._id += 1
        self.id = Node._id

    def wrap_if_necessary(self, subnode):
        varset = get_variables(subnode.innermost_expressions())
        if self.var in varset:
            return ExistsNode(self.var, subnode, prev = (subnode.prev[0], self))
        else:
            return subnode

    def read(self):
        return ExistsNodeReader(self)

    def forward_expand(self, axiom_list):
        return (
            self.wrap_if_necessary(x)
            for x in self.subnode.forward_expand(axiom_list)
        )

    def replace_innermost_node(self, new_node):
        return self.wrap_if_necessary(self.subnode.replace_innermost_node(new_node))

    def backward_expand_axiom_expr(self, axiom, innermost_expression):
        # If the innermost expression doesn't contain our variable, we
        # can't do a binding.
        if self.var not in get_variables(innermost_expression):
            return None

        # Get the expression we're going to want to match against.
        innermost_node = self
        while isinstance(innermost_node, ExistsNode):
            innermost_node = innermost_node.subnode

        # Bindings for a BACKWARDS step need to happen in two stages.

        # FORWARD PASS
        # =============

        # The first stage is a forward pass, like an ordinary forward pass.
        forward_bindings = {}

        def forward_check(axiom_output, my_expression):
            # Pass through whenever the target is the variable that needs to be
            # expanded in the backward pass.
            if my_expression == self.var:
                return True

            if not isinstance(axiom_output, tuple):
                if isinstance(axiom_output, Variable):
                    if axiom_output in forward_bindings:
                        return forward_bindings[axiom_output] == my_expression
                    else:
                        forward_bindings[axiom_output] = my_expression
                        return True
                else:
                    return axiom_output == my_expression

            # If we're a variable and they're not, ho boy wuh oh
            if not isinstance(my_expression, tuple):
                return False

            # If we're different lengths something's wrong.
            if len(axiom_output) != len(my_expression):
                return False

            # Check every child.
            return all(forward_check(a, m) for a, m in zip(axiom_output, my_expression))

        # Check validity and generate bindings
        if not forward_check(axiom.output, innermost_expression):
            return None

        # Substitute into the output
        modified_axiom_output = substitute(axiom.output, forward_bindings)

        # BACKWARD PASS
        # =============

        # Then, we do a backward pass where we figure out what to bind to the exists variable.
        backward_binding = None

        def backward_check(axiom_output, my_expression):
            nonlocal backward_binding

            if my_expression == self.var:
                if backward_binding is not None:
                    return backward_binding == axiom_output
                else:
                    backward_binding = axiom_output
                    return True

            elif isinstance(axiom_output, tuple):
                return all(backward_check(a, m) for a, m in zip(axiom_output, my_expression))

            else:
                return True

        if not backward_check(modified_axiom_output, innermost_expression):
            return None

        # Substitute into the output again.
        modified_axiom_output = substitute(modified_axiom_output, {self.var: backward_binding})

        # Substitute into all the inputs
        new_expressions = frozenset(substitute(substitute(x, forward_bindings), {self.var: backward_binding}) for x in axiom.inputs)

        # Substitute the same into all other variable instances
        new_others = frozenset(substitute(x, {self.var: backward_binding}) for x in innermost_node.expressions - frozenset((innermost_expression,)))

        # Final set;
        final_set = new_others | new_expressions

        # LEFTOVERS PROCEDURE
        # ===================
        leftovers = axiom.required_bindings - frozenset(forward_bindings.keys())

        # Replace leftovers with exists variables
        leftover_bindings = {x: Variable(x.name) for x in leftovers}

        # New final set
        final_set = frozenset(substitute(x, leftover_bindings) for x in final_set)

        # Wrap in exists as far as necessary
        node = Node(final_set, prev = (axiom, self), cost = (
                innermost_node.cost + (axiom.cost + EXTRA_VARIABLE_PENALTY * len(leftovers) +
                EXTRA_TERM_PENALTY * len(new_expressions) +
                SIZE_PENALTY * size_estimate(new_expressions)) * BACKWARD_EXPANSION_REDUCTION
            )
        )

        for var in leftover_bindings.values():
            node = ExistsNode(var, node, prev = (axiom, self))

        # Replace innermost node with the new one
        return self.replace_innermost_node(node)

    def innermost_expressions(self):
        node = self
        while isinstance(node, ExistsNode):
            node = node.subnode
        return node.expressions

    def backward_expand_only_me(self, axiom_list):
        return (x for x in (self.backward_expand_axiom_expr(axiom, expr) for expr in self.innermost_expressions() for axiom in axiom_list) if x is not None)

    def backward_expand(self, axiom_list):
        if isinstance(self.subnode, ExistsNode):
            return chain(
                (self.wrap_if_necessary(x) for x in self.subnode.backward_expand(axiom_list)),
                self.backward_expand_only_me(axiom_list))
        else:
            return self.backward_expand_only_me(axiom_list)

    def expand(self, axiom_list):
        return chain(self.forward_expand(axiom_list), self.backward_expand(axiom_list))

    def expr_for_printing(self):
        return ('exists', self.var, '.', self.subnode.expr_for_printing())

    def print(self):
        return print_expr(self.expr_for_printing())

# The GOAL NODE
GOAL = Node(frozenset()).read()

def history_length(x):
    if x.prev is None:
        return 1
    else:
        return 1 + history_length(x.prev[1])

# Engage in some kinda graph search!
def try_proving(statement, axiom_list, max_cost = 1e6):
    # Dijkstra's algorithm.
    frontier = [
        Node(frozenset((statement,)))
    ]

    visited = {
        frontier[0].read(): frontier[0]
    }

    while GOAL not in visited:
        removed = heapq.heappop(frontier)

        '''
        if not isinstance(removed, ExistsNode):
            print('CANDIDATE NODE (cost %f, length %d): %s' % (removed.cost, history_length(removed), removed.print()))
            sys.stdout.flush()

        '''
        #print('------')
        #print('EXPANDING NODE (cost %f, length %d, id %d, from %d): %s' % (removed.cost, history_length(removed), removed.id, removed.prev[1].id if removed.prev is not None else -1, removed.print()))

        if removed.cost > max_cost:
            return None

        for new_pair in removed.expand(axiom_list):
            #print('considering inserting', new_pair.id)
            if new_pair.read() not in visited:
                #print('Adding (cost %f): %s by axiom %s' % (new_pair.cost, new_pair.print(), new_pair.prev[0].print()))
                heapq.heappush(frontier, new_pair)
                visited[new_pair.read()] = new_pair
            else:
                #print('I already have a node like this:', visited[new_pair.read()].id)
                pass

    # Chain of reasoning:
    goal_node = visited[GOAL]

    reasoning = []
    while goal_node.prev is not None:
        reasoning.append(goal_node.prev)
        goal_node = goal_node.prev[1]

    return reasoning

def forward_extend_axiom_list(axiom_list, layers):
    for i in range(layers):
        new_axioms = []
        flagged = set()
        for axiom in axiom_list:
            init_mapping = {v: Variable(v.name) for v in axiom.required_bindings}
            begin = Node(frozenset(substitute(x, init_mapping) for x in axiom.inputs))
            out_exprs = substitute(axiom.output, init_mapping)

            results = begin.expand(axiom_list)

            for result in results:
                in_exprs = result.innermost_expressions()

                if len(in_exprs) == 0:
                    continue

                new_axiom = Axiom(in_exprs, out_exprs)

                # Make sure this new axiom is not strictly worse than
                # some other axiom in the axiom list.
                is_bad = False
                for test_axiom in chain(axiom_list, new_axioms):
                    if new_axiom.is_strictly_worse_than(test_axiom):
                        is_bad = True
                        break
                    elif test_axiom.is_strictly_worse_than(new_axiom):
                        flagged.add(test_axiom)

                if is_bad:
                    continue
                else:
                    '''
                    print('NEW AXIOM:')
                    print('  %s' % (new_axiom.print(),))
                    print('  This comes from:')
                    print('    %s' % (axiom.print(),))
                    print('    %s' % (result.prev[0].print(),))
                    '''
                    new_axioms.append(new_axiom)

        axiom_list.extend(new_axioms)
        axiom_list = [axiom for axiom in axiom_list if axiom not in flagged]

        print('layer', i, 'length', len(axiom_list))

    return axiom_list

# TESTS
def main():
    globs = {
        '=': Global('=', print_style = BINARY_INFIX),
        '+': Global('+', print_style = BINARY_INFIX),
        '*': Global('*', print_style = BINARY_INFIX),
        '0': Global('0')
    }

    axiom_list = [
        # EQUALITY
        ((), ('=', 'a', 'a'), 'the reflexive property of equality'), # Reflexivity
        ((('=', 'b', 'a'),), ('=', 'a', 'b'), 'the commutative property of equality'), # Commutativity
        ((('=', 'a', 'b'), ('=', 'b', 'c')), ('=', 'a', 'c'), 'the transitive property of equality'), # Transitivity

        # ADDITION
        ((), ('=', ('+', 'a', 'b'), ('+', 'b', 'a')), 'the commutative property of addition'), # Commutativity
        ((), ('=', ('+', ('+', 'a', 'b'), 'c'), ('+', 'a', ('+', 'b', 'c'))), 'the associative property of addition'), # Associativity
        ((), ('=', ('+', 'a', '0'), 'a'), 'the definition of the additive identity'), # Definition of 0
        ((('=', 'a', 'b'),), ('=', ('+', 'c', 'a'), ('+', 'c', 'b')), 'the substitution law for addition'), # Substitution law
        ((('=', ('+', 'c', 'a'), ('+', 'c', 'b')),), ('=', 'a', 'b'), 'the cancellation law for addition'), # Cancellation law

        # MULTIPLICATION
        ((), ('=', ('*', 'a', 'b'), ('*', 'b', 'a')), 'the commutative property of multiplication'), # Commutativity
        ((), ('=', ('*', ('*', 'a', 'b'), 'c'), ('*', 'a', ('*', 'b', 'c'))), 'the associative property of multiplication'), # Associativity
        ((), ('=', ('*', ('+', 'a', 'b'), 'c'), ('+', ('*', 'a', 'b'), ('*', 'a', 'c'))), 'the distributive law for multiplication over addition'), # Distributivity
        ((('=', 'a', 'b'),), ('=', ('*', 'c', 'a'), ('*', 'c', 'b')), 'the substitution law for multiplication'), # Substitution law
        ((('=', ('*', 'c', 'a'), ('*', 'c', 'b')),), ('=', 'a', 'b'), 'the cancellation law for multiplication'), # Cancellation law
    ]

    def extract_var_names(tpl):
        if isinstance(tpl, str):
            if tpl in globs:
                return set()
            else:
                return {tpl}

        return reduce((lambda x, y: x | y), (extract_var_names(x) for x in tpl), set())

    def make_axiom_out_of(tpl):
        a, b, c = tpl
        tpl = (a, b)
        vnames = extract_var_names(tpl)
        vs = {name: Variable(name) for name in vnames}
        tpl = substitute(tpl, globs)
        tpl = substitute(tpl, vs)

        return Axiom(tpl[0], tpl[1], c)

    axiom_list = [make_axiom_out_of(x) for x in axiom_list]

    # Do 4 layers of forward inferential conclusions
    # forward_extend_axiom_list(axiom_list, 4)

    # Let's construct the proof goal. Right now I just want to use
    # the distributive property to say a * (b + a) = a * b + a * a

    a = Variable('a')
    times = globs['*']
    plus = globs['+']
    eq = globs['=']
    zero = globs['0']

    proof_lines = [
        (eq, (times, a, (plus, a, zero)), (plus, zero, (times, a, (plus, a, zero)))), # a * (a + 0) = 0 + a * (a + 0)
        (eq, (times, a, (plus, a, zero)), (plus, zero, (times, a, a))), # a * (a + 0) = 0 + a * a
        (eq, (times, a, (plus, a, zero)), (plus, (times, a, zero), (times, a, a))), # a * (a + 0) = a * 0 + a * a
        (eq, (plus, zero, (times, a, a)), (plus, (times, a, zero), (times, a, a))), # 0 + a * a = a * 0 + a * a
        (eq, zero, (times, a, zero)) # QED
    ]

    for i, line in enumerate(proof_lines):
        result = try_proving(line, axiom_list)

        for j, piece in enumerate(result):
            if j == 0:
                print('\nBy %s we have:' % (piece[0].print(),))
            else:
                print('Then by %s we have:' % (piece[0].print(),))

            if j == len(result) - 1:
                print('  %s [%d]' % (piece[1].print(), i))
            else:
                print('  %s' % (piece[1].print(),))

        axiom_list += (Axiom((), substitute(line, {a: Variable('a')}), '[%d]' % (i,)),)

    print('QED')

    return

if __name__ == '__main__':
    main()

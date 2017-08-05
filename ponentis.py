from itertools import chain
import heapq
from functools import reduce
# An expression is just a tuple. We don't have to worry about that.

EXTRA_VARIABLE_PENALTY = 1000

# There are two types of atoms. Variables, and Globals.
class Variable:
    _id = 0
    def __init__(self, name):
        Variable._id += 1
        self._id = Variable._id
        self.name = name

    def __hash__(self):
        return hash(self._id)

    def __eq__(self, other):
        if not isinstance(other, Variable):
            return False

        return other._id == self._id

class Global:
    _id = 0
    def __init__(self, name):
        Variable._id += 1
        self._id = Variable._id
        self.name = name

    def __hash__(self):
        return hash(self._id)

    def __eq__(self, other):
        if not isinstance(other, Global):
            return False

        return other._id == self._id

# Utility functions
def get_variables(expression):
    if isinstance(expression, Variable):
        return frozenset((expression,))
    elif isinstance(expression, tuple):
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
    def __init__(self, inputs, output, cost = 1.0):
        self.inputs = inputs
        self.output = output
        self.cost = cost
        self.required_bindings = reduce((lambda x, y: x | y), (get_variables(x) for x in self.inputs), frozenset())

    def print(self):
        return '%s => %s' % (' ^ '.join(print_expr(x) for x in self.inputs), print_expr(self.output))

class NodeReader:
    def __init__(self, node):
        self.expressions = node.expressions

    def __hash__(self):
        return hash(self.expressions)

    def __eq__(self, other):
        if isinstance(other, NodeReader):
            return self.expressions == other.expressions
        else:
            return False

class ExistsNodeReader:
    def __init__(self, node):
        self.var = node.var
        self.subnode = node.subnode.read()

    def __hash__(self):
        return hash((self.var, self.subnode))

    def __eq__(self, other):
        if isinstance(other, ExistsNodeReader):
            return other.var == self.var and other.subnode == self.subnode
        else:
            return False

def print_expr(expr):
    if isinstance(expr, Variable) or isinstance(expr, Global):
        return expr.name
    else:
        return '(%s)' % (' '.join(print_expr(x) for x in expr))

# A Node in the search graph. (expressions) is a tuple of tuples,
# where each tuple is an expression, and the Node represents their conjunction.
# It knows how to FORWARD expand.
class Node:
    _id = 0
    def __init__(self, expressions, prev = None):
        Node._id += 1
        self.id = Node._id

        self.expressions = expressions
        self.prev = prev

    def read(self):
        return NodeReader(self)

    # FORWARD EXPANSION using AXIOM and statement INDEX
    def forward_expand_axiom_index(self, axiom, expression):
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
            return None

        # Hey, we're valid! Bindings have been generated, too.
        # Substitute them into the axiom inputs.
        new_expressions = frozenset(substitute(x, bindings) for x in axiom.inputs)

        # Concatenate together the new expressions.
        result = Node(self.expressions - frozenset((expression,)) | new_expressions, prev = (axiom, self))

        # LEFTOVERS PROCEDURE
        # ===================

        # See if there were any leftover variables that need to be turned into Exists.
        leftovers = axiom.required_bindings - frozenset(bindings.keys())

        # Create Exists variables for each of the leftover bindings
        leftover_bindings = {x: Variable(x.name) for x in leftovers}

        # And exists nodes
        for var in leftover_bindings.values():
            result = ExistsNode(var, result, prev = (axiom, self), cost = result.cost + VCOST)

        # Return.
        return result

    def forward_expand_axiom(self, axiom):
        return (x for x in (self.forward_expand_axiom_index(axiom, expr) for expr in self.expressions) if x is not None)

    def forward_expand(self, axiom_list, cost):
        return ((cost + axiom.cost, x) for axiom in axiom_list for x in self.forward_expand_axiom(axiom))

    def expand(self, axiom_list, cost):
        return self.forward_expand(axiom_list, cost)

    def replace_innermost_node(self, node):
        return node

    def print(self):
        return ' && '.join(print_expr(expr) for expr in self.expressions)

    def __lt__(self, other):
        return self.id < other.id

    def __gt__(self, other):
        return self.id > other.id

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
        self.prev = prev

        Node._id += 1
        self.id = Node._id

    def read(self):
        return ExistsNodeReader(self)

    def forward_expand(self, axiom_list, cost):
        return ((y, ExistsNode(self.var, x, prev = (x.prev[0], self))) for y, x in self.subnode.forward_expand(axiom_list, cost))

    def replace_innermost_node(self, new_node):
        return ExistsNode(self.var, self.subnode.replace_innermost_node(new_node), prev = (new_node.prev[0], self))

    def backward_expand_axiom(self, axiom):
        # Get the expression we're going to want to match against.
        innermost_node = self
        while isinstance(innermost_node, ExistsNode):
            innermost_node = innermost_node.subnode
        innermost_expression = next(iter(innermost_node.expressions))


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
        node = Node(final_set, prev = (axiom, self))

        for var in leftover_bindings.values():
            node = ExistsNode(var, node, prev = (axiom, self))

        # Replace innermost node with the new one
        return self.replace_innermost_node(node)

    def backward_expand(self, axiom_list, cost):
        return ((cost + axiom.cost, x) for axiom, x in ((axiom, self.backward_expand_axiom(axiom)) for axiom in axiom_list) if x is not None)

    def expand(self, axiom_list, cost):
        return chain(self.forward_expand(axiom_list, cost), self.backward_expand(axiom_list, cost))

    def print(self):
        return 'exists %s. %s' % (self.var.name, self.subnode.print())

# The GOAL NODE
GOAL = Node(frozenset())

# Engage in some kinda graph search!
def try_proving(statement, axiom_list, max_cost = 1e6):
    # Dijkstra's algorithm.
    frontier = [
        (0, Node(frozenset((statement,))))
    ]

    visited = {
        frontier[0][1].read(): frontier[0][1]
    }

    while GOAL not in visited:
        cost, removed = heapq.heappop(frontier)

        print('------')
        print('EXPANDING NODE: %s' % (removed.print(),))

        if cost > max_cost:
            return None

        for new_pair in removed.expand(axiom_list, cost):
            if new_pair[1].read() not in visited:
                print('Adding: %s' % (new_pair[1].print(),))
                heapq.heappush(frontier, new_pair)
                visited[new_pair[1].read()] = new_pair[1]

    # Chain of reasoning:
    goal_node = visited[GOAL]

    reasoning = []
    while goal_node.prev is not None:
        reasoning.append(goal_node.prev)
        goal_node = goal_node.prev[1]

    return reasoning

# TESTS
def main():
    globs = {
        '=': Global('='),
        '+': Global('+'),
        '*': Global('*'),
        '0': Global('0')
    }

    axiom_list = [
        # EQUALITY
        ((), ('=', 'a', 'a')), # Reflexivity
        ((('=', 'b', 'a'),), ('=', 'a', 'b')), # Commutativity
        ((('=', 'a', 'b'), ('=', 'b', 'c')), ('=', 'a', 'c')), # Transitivity

        # ADDITION
        ((), ('=', ('+', 'a', 'b'), ('+', 'b', 'a'))), # Commutativity
        ((), ('=', ('+', ('+', 'a', 'b'), 'c'), ('+', 'a', ('+', 'b', 'c')))), # Associativity
        ((), ('=', ('+', 'a', '0'), 'a')), # Definition of 0

        # MULTIPLICATION
        ((), ('=', ('*', 'a', 'b'), ('*', 'b', 'a'))), # Commutativity
        ((), ('=', ('*', ('*', 'a', 'b'), 'c'), ('*', 'a', ('*', 'b', 'c')))), # Associativity
        ((), ('=', ('*', ('+', 'a', 'b'), 'c'), ('+', ('*', 'a', 'b'), ('*', 'a', 'c')))) # Distributivity
    ]

    def extract_var_names(tpl):
        if isinstance(tpl, str):
            if tpl in globs:
                return set()
            else:
                return {tpl}

        return reduce((lambda x, y: x | y), (extract_var_names(x) for x in tpl), set())

    def make_axiom_out_of(tpl):
        vnames = extract_var_names(tpl)
        vs = {name: Variable(name) for name in vnames}
        tpl = substitute(tpl, globs)
        tpl = substitute(tpl, vs)

        return Axiom(tpl[0], tpl[1])

    axiom_list = tuple(make_axiom_out_of(x) for x in axiom_list)

    # Let's construct the proof goal. Right now I just want to use
    # the distributive property to say a * (b + a) = a * b + a * a

    a = Variable('a')
    b = Variable('b')
    times = globs['*']
    plus = globs['+']
    eq = globs['=']

    goal = (eq, (times, a, (plus, a, b)), (plus, (times, a, b), (times, a, a)))

    result = try_proving(goal, axiom_list)

    print(result)

    return

if __name__ == '__main__':
    main()

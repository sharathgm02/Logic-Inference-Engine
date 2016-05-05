import re
import copy
import sys

counter = 0
visited_facts = []
final_goal = None
flag = False
LOGGER = ""
hack_print = False
proved_facts_list = []


def is_arg_constant(word):
    return word[0].isupper()


def is_variable(x):
    return x == x.lower()


def append_all(var, val, theta):
    new_theta = theta.copy()
    new_theta[var] = val
    return new_theta


def unify_var(x, y, theta, goal=None):
    global hack_print
    # if bool(hack_print and goal is not None):
    #     print_ask(goal)
    #     hack_print = False
    if x in theta:
        return unify(theta[x], y, theta, goal)
    elif y in theta:
        return unify(x, theta[y], theta, goal)
    else:
        return append_all(x, y, theta)


def is_list(x):
    return hasattr(x, '__len__')


def unify(x, y, theta={}, goal=None):

    global hack_print
    if theta is not None:
        for key in theta.keys():
            if theta.get(key) in theta.keys():
                theta[key] = theta.get(theta.get(key))

    if theta is None:
        return None
    elif x == y:
        return theta

    elif isinstance(x, str) and is_variable(x):
        return unify_var(x, y, theta, goal)
    elif isinstance(y, str) and is_variable(y):
        return unify_var(y, x, theta, goal)
    elif isinstance(x, str) or isinstance(y, str) or not x or not y:
        if bool(hack_print):
            hack_print = False
        return theta if x == y else None
    elif is_list(x) and is_list(y) and len(x) == len(y):
        return unify(x[1:], y[1:], unify(x[0], y[0], theta, goal), goal)
    else:
        return None


class Predicate:
    def __copy__(self):
        return Predicate(self.name, self.arguments)

    def __hash__(self):
        return hash((self.name, tuple(self.arguments)))

    def __eq__(self, other):
        return self.name == other.name and self.arguments == other.arguments

    def __init__(self, name, arguments):
        self.name = name
        self.arguments = arguments


def create_predicate(x):
    operand_name = ''.join(re.findall(r'(\W?\w+)\(',x))
    arg_terms = ''.join(re.findall(r'\(([\w+]|[\w+, \w+]*)\)',x)).split(', ')
    return Predicate(operand_name,arg_terms)


def create_predicate_conjuncts(x):
    return [create_predicate(y) for y in x.split(' && ')] if x else []


def get_lhs(x):
    if "=>" in x:
        return x.split(" => ")[0]
    else:
        return None


def get_rhs(x):
    return x.split(" => ")[-1]


def replace_in_list(theta, pred_args):
    new_list = list(pred_args)
    for var in theta:
        if var in pred_args:
            indices = [i for (i,j) in enumerate(pred_args) if j == var]
            for k in indices:
                new_list[k] = theta[var]
    return new_list


def standardize(lhs, rhs, theta=None):
    global counter
    if theta is None:
        theta = {}
    args = []
    for i in lhs:
        for j in i.arguments:
            args.append(j)

    args = args + rhs.arguments

    for term in args:
        if is_variable(term):
            if term not in theta:
                counter += 1
                theta[term] = "v_%d" % counter

    for i in lhs:
        i.arguments = replace_in_list(theta, i.arguments)
    rhs.arguments = replace_in_list(theta, rhs.arguments)

    return lhs, rhs


def is_fact(term):
    for i in term.arguments:
        if is_variable(i):
            return False
    return True


def substitute(theta, term):
    temp_term = copy.deepcopy(term)
    for var in theta:
        if var in term.arguments:
            temp_term.arguments[temp_term.arguments.index(var)] = theta[var]
    return temp_term


def print_in_format(goal, dictionary):
    global LOGGER
    global proved_facts_list
    my_str = "("
    for statement in goal.arguments:
        if len(my_str) > 1:
            my_str += ", "
        if is_arg_constant(statement):
            my_str += statement
        elif bool(dictionary) and dictionary.get(statement) is not None:
            if is_variable(dictionary.get(statement)):
                my_str += "_"
            else:
                my_str += dictionary.get(statement)
        else:
            my_str += "_"
    my_str += ")"
    print "True:", goal.name, my_str
    LOGGER += "True: " + goal.name + my_str + "\n"
    proved_facts_list.append(goal)


def print_for_false(goal, dictionary):
    global LOGGER
    global proved_facts_list
    if goal in proved_facts_list:
        return
    my_str = "("
    for statement in goal.arguments:
        if len(my_str) > 1:
            my_str += ', '
        if is_arg_constant(statement):
            my_str += statement
        elif bool(dictionary) and dictionary.get(statement) is not None:
            if is_variable(dictionary.get(statement)):
                my_str += "_"
            else:
                my_str += dictionary.get(statement)
        else:
            my_str += "_"
    my_str += ")"
    print "False:", goal.name, my_str
    LOGGER += "False: " + goal.name + my_str + "\n"


def print_ask(goal):
    global LOGGER
    my_str = "("
    for statement in goal.arguments:
        if len(my_str) > 1:
                my_str += ', '
        if is_arg_constant(statement):
            my_str += statement
        else:
            my_str += '_'
    my_str += ")"
    print "Ask:", goal.name, my_str
    LOGGER += "Ask: " + goal.name + my_str + "\n"


def fol_bc_and(knowledge_base, goals, theta, and_visited_facts):
    global hack_print

    if theta is None:
        #hack_print = True
        return

    elif len(goals) == 0:
        yield theta
    else:
        first = goals[0]
        rest = goals[1:]

        for theta_dash in fol_bc_or(knowledge_base, substitute(theta, first), and_visited_facts, theta):
            for theta_double_dash in fol_bc_and(knowledge_base, rest, theta_dash, and_visited_facts):
                yield theta_double_dash


def fol_bc_or(knowledge_base, goal, visited_facts, theta={}):
    global flag
    global LOGGER
    global hack_print
    if isinstance(goal, Predicate):
        print_ask(goal)

    for rule in knowledge_base:

        lhs = create_predicate_conjuncts(get_lhs(rule))
        rhs = create_predicate(get_rhs(rule))

        if rhs.name == goal.name:
            # if bool(hack_print):
            #     print_ask(goal)
            #     hack_print = False
            if is_fact(rhs):
                if is_fact(goal):
                    if not rhs == goal:
                        continue
                if rhs not in visited_facts:
                    visited_facts.append(rhs)

            lhs, rhs = standardize(lhs, rhs)

            dicto = {}
            dicto = unify(rhs.arguments, goal.arguments, theta, goal)
            if dicto == {}:
                hack_print = False
            else:
                if bool(hack_print and goal is not None):
                    print_ask(goal)
                    hack_print = False

            for theta_dash in fol_bc_and(knowledge_base, lhs, unify(rhs.arguments, goal.arguments, theta, goal), visited_facts):
                print_in_format(goal, theta_dash)
                if not goal == final_goal:
                    yield theta_dash
                else:
                    flag = True
                    return

    print_for_false(goal, theta)
    hack_print = True
    yield


def fol_bc_ask(knowledge_base, query):
    global flag
    flag = False
    query = create_predicate(query)
    visited_facts.append(query)
    return fol_bc_or(knowledge_base, query, visited_facts, {})


def read_file_data(f):
    query_str = str(f.readline().rstrip())
    queries = query_str.split(" && ")
    num_kb_facts = int(f.readline().rstrip('\r\n'))
    knowledge_base = []
    for i in range(num_kb_facts):
        knowledge_base.append(str(f.readline().rstrip()))

    return queries, knowledge_base


def main():
    global visited_facts
    global counter
    global final_goal
    global flag
    global LOGGER
    input_file_handler = open(str(sys.argv[2]), 'r')
    output_file_handler = open("output.txt", 'w')
    queries, knowledge_base = read_file_data(input_file_handler)

    for query in queries:
        try:
            final_goal = create_predicate(query)
            bc_length = len(list(fol_bc_ask(knowledge_base, query)))
            if not bool(flag):
                break
        except RuntimeError:
            break

        visited_facts = []
        counter = 0
    if flag is True:
        LOGGER += "True"
    else:
        LOGGER += "False"
    output_file_handler.write(LOGGER)
    output_file_handler.close()
    input_file_handler.close()

if __name__ == '__main__':
    main()

__author__ = 'Sharath_GM'
import copy

VISITED_DICT = {}

class Predicate:

    def __init__(self, name=None, args=None):
        if name is None and args is None:
            self.name = ""
            self.numArgs = 0
            self.argArr = []

        elif args is None:
            self.name = name.name
            self.numArgs = name.numArgs
            self.argArr = name.argArr

        else:
            self.name = name
            self.argArr = args.split(", ")
            self.numArgs = len(self.argArr)
            print self.name, "-----", self.argArr

    def get_name(self):
        return self.name

    def get_arg_arr(self):
        return self.argArr

    def get_num_args(self):
        return self.numArgs

    def is_same(self, obj):
        if obj is None or not isinstance(self, obj):
            return False
        term = Predicate(obj)
        if not self.name == term.get_name():
            return False
        if not self.numArgs == term.get_num_args():
            return False
        for i in range(0, term.get_num_args()):
            if is_arg_constant(self.get_arg_arr()[i]) or is_arg_constant(term.get_arg_arr()[i]):
                if not self.get_arg_arr()[i] == term.get_arg_arr()[i]:
                    return False
        return True


class ImplicationMapping:
    def __init__(self, obj=None):
        if obj is None:
            self.consequent = Predicate()
            self.antecedents = []
        else:
            self.consequent = obj.consquent
            self.antecedents = obj.antecedents

    def add_antecedent(self, sentence):
        self.antecedents.append(sentence)

    def is_mapping_same(self, obj):
        if obj is None or not isinstance(self, obj):
            return False
        mapping_obj = ImplicationMapping(obj)
        if not mapping_obj.consequent.is_same(self.consequent) or not mapping_obj.consequent.get_arg_arr() == self.consequent.get_arg_arr():
            return False
        if not len(mapping_obj.antecedents) == len(self.antecedents):
            return False
        for pred in mapping_obj.antecedents:
            if pred not in self.antecedents:
                return False
            for another_pred in self.antecedents:
                if pred.is_same(another_pred):
                    if not pred.get_arg_arr() == another_pred.get_arg_arr():
                        return False
        return True


class KnowledgeBase:

    def __init__(self):
        self.factsMap = {}
        self.clausesMap = {}

    def add_fact(self, name, loc_fact):
        fmap = self.factsMap

        if name in fmap:
            if loc_fact not in fmap.get(name):
                fmap.get(name).append(loc_fact)
        else:
            sentences = []
            sentences.append(loc_fact)
            fmap[name] = sentences

    def add_clause(self, name, mapping_to_add):
        cmap = self.clausesMap

        if name in cmap:
            sentences = cmap.get(name)
            flag = False
            for kb_term in sentences:
                if kb_term.is_mapping_same(mapping_to_add):
                    flag = True
                    break
            if not flag:
                sentences.append(mapping_to_add)
        else:
            sentences = []
            sentences.append(mapping_to_add)
            cmap[name] = sentences

    def print_kb(self):
        for key in self.factsMap:
            print key
            print self.factsMap.get(key)
            print "____________________"
        for key in self.clausesMap:
            print key
            print self.clausesMap.get(key)
            print "____________________"


def is_arg_constant(word):
    return word[0].isupper()


def is_fact_unifiable(left, right):
    left = Predicate(left)
    right = Predicate(right)
    match = False
    args = right.get_arg_arr()
    index = 0
    for element in args:
        match = False
        if is_arg_constant(args[index]):
            if args[index] == left.get_arg_arr()[index]:
                match = True
        else:
            match = True
        if not match:
            break
        index+=1
    return match


def is_consequent_unifiable(consequent, goal):
    goal = Predicate(goal)
    consequent = Predicate(consequent)
    for i in range(0, consequent.get_num_args()):
        if is_arg_constant(consequent.get_arg_arr()[i]) and is_arg_constant(goal.get_arg_arr()[i]):
            if not consequent.get_arg_arr()[i] == goal.get_arg_arr()[i]:
                return False
    return True


def is_visited(goal_term):
    goal_term = Predicate(goal_term)
    if goal_term.get_name() in VISITED_DICT.keys():
        for term in VISITED_DICT.get(goal_term.get_name()):
            term = Predicate(term)
            if term.is_same(goal_term):
                return True
    return False


def add_to_visited(goal_term):
    goal_term = Predicate(goal_term)
    if goal_term.get_name() in VISITED_DICT.keys():
        VISITED_DICT.get(goal_term.get_name()).append(goal_term)
    else:
        term_list = []
        term_list.append(goal_term)
        VISITED_DICT[goal_term.get_name()] = term_list


def bc_fol_or(goal):
    global VISITED_DICT
    goal = Predicate(goal)
    print "Ask: ", goal
    unified = []
    if goal.get_name() in kb.factsMap:
        facts = kb.factsMap.get(goal.get_name())
        for lhs in facts:
            if is_fact_unifiable(lhs, goal):
                unified.append(lhs)

    if is_visited(goal):
        if not len(unified) == 0:
            print "truee"
            return unified
        print "falsee"
        return None

    local_visited_map = copy.deepcopy(VISITED_DICT)
    add_to_visited(goal)

    if not goal.get_name() in kb.clausesMap.keys():
        if not len(unified) == 0:
            print "truee"
            return unified
        print "falsee"
        return None

    sentences = kb.clausesMap.get(goal.get_name())
    for rule in sentences:
        rule = ImplicationMapping(rule)
        consequent = Predicate(rule.consequent)
        if not is_consequent_unifiable(consequent, goal):
            continue
        mapping = ImplicationMapping()
        mapping.consequent = consequent
        for term in rule.antecedents:
            mapping.add_antecedent(Predicate(term))

        and_result = bc_fol_and(mapping)
        if and_result is not None:
            unified.extend(and_result)
        VISITED_DICT = copy.deepcopy(local_visited_map)
        if not len(unified) == 0:
            print "truee"
            return unified
        print "falsee"
        return None


def bc_ask(query):
        return bc_fol_or(query) is not None




def create_predicate(term_str):
    open_index = term_str.index("(")
    close_index = term_str.index(")")
    arguments = term_str[open_index + 1:close_index]
    name = term_str[0:open_index]
    return Predicate(name, arguments)


#################
# MAIN FUNCTION #
#################

f = open('sample01.txt', 'r')

given_query = f.readline().rstrip()

num_kb_clauses = int(f.readline().rstrip())
kb = KnowledgeBase()

for i in range(num_kb_clauses):
    clause = f.readline().rstrip()
    terms = clause.split("=>")

    if len(terms) == 1:
        fact = create_predicate(terms[0])
        kb.add_fact(fact.get_name(), fact)

    if len(terms) == 2:
        consequent_term = create_predicate(terms[1])
        conjuncts = terms[0].split("&&")
        impl_mapping = ImplicationMapping()
        impl_mapping.consequent = consequent_term
        for statement in conjuncts:
            impl_mapping.add_antecedent(create_predicate(statement))
        kb.add_clause(consequent_term.get_name(), impl_mapping)

kb.print_kb()

final_result = bc_ask(given_query)
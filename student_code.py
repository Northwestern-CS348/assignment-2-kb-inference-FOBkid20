import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here
        if not isinstance(fact, Fact):  # ignore retractions that are not facts as specified on Piazza
            return

        if fact not in self.facts:  # ignore if fact to be retracted is not in kb
            return
        fact = self._get_fact(fact)  # make sure you have kb's fact

        # Don't remove if supported
        if fact.supported_by:
            if fact.asserted:
                fact.asserted = False  # unassert asserted facts as specified on Piazza
            return

        for otherFact in fact.supports_facts:
            for factRule in otherFact.supported_by:
                if fact in factRule:
                    otherFact.supported_by.remove(factRule)
            # otherFact.supported_by = otherFact.supported_by.remove(fact)
            if len(otherFact.supported_by) == 0:
                self.kb_retract(otherFact)
        for rule in fact.supports_rules:
            for factRule in rule.supported_by:
                if fact in factRule:
                    rule.supported_by.remove(factRule)
            # rule.supported_by = rule.supported_by.remove(fact)
            if len(rule.supported_by) == 0:
                self.kb_retract_rule(rule)
        self.facts.remove(fact)


    def kb_retract_rule(self, rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [rule])
        ####################################################
        # Student code goes here
        if not isinstance(rule, Rule):  # ignore retractions that are not facts as specified on Piazza
            return

        if rule not in self.rules:  # ignore if fact to be retracted is not in kb
            return
        rule = self._get_rule(rule)  # make sure you have kb's fact

        # Don't remove if supported
        if rule.supported_by:
            return
        # Don't remove if asserted
        if rule.asserted:
            return

        for otherFact in rule.supports_facts:
            for factRule in otherFact.supported_by:
                if rule in factRule:
                    otherFact.supported_by.remove(factRule)
            # otherFact.supported_by = otherFact.supported_by.remove(fact)
            if len(otherFact.supported_by) == 0:
                self.kb_retract(otherFact)
        for otherRule in rule.supports_rules:
            for factRule in otherRule.supported_by:
                if rule in factRule:
                    otherRule.supported_by.remove(factRule)
            # rule.supported_by = rule.supported_by.remove(fact)
            if len(otherRule.supported_by) == 0:
                self.kb_retract_rule(otherRule)
        self.rules.remove(rule)

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        if len(rule.lhs) > 0:
            # check if first element of LHS matches
            if match(rule.lhs[0], fact.statement):
                # If there are multiple elements to the LHS, create a new rule
                if len(rule.lhs) > 1:
                    builtLHS = []
                    for i in range(1, len(rule.lhs)):  # ignoring the first element, build the rest of the LHS
                        builtLHS.append(instantiate(rule.lhs[i], match(fact.statement, rule.lhs[0])))
                    builtRHS = instantiate(rule.rhs, match(rule.lhs[0], fact.statement))
                    addedRule = Rule(rule=[builtLHS, builtRHS], supported_by=[[fact, rule]])
                    fact.supports_rules.append(addedRule)
                    rule.supports_rules.append(addedRule)
                    kb.kb_add(addedRule)
            # If there's only one element, create a new fact
                else:
                    addedFact = Fact(statement=instantiate(rule.rhs, match(fact.statement, rule.lhs[0])), supported_by=[[fact, rule]])
                    fact.supports_facts.append(addedFact)
                    rule.supports_facts.append(addedFact)
                    kb.kb_add(addedFact)

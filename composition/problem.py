# the file to define the class for each inequality problem

class IneqProblem:
    def __init__(self, name=None, variables=None, condition=None, statement_lhs=None, statement_rhs=None):
        """
        name: str
            the name of the problem
        variables : List
            example : ["a", "b", "c"]
        condition : string template
            in this project, we restrict the inequality problem to have at most 1 condition
            example : "{a} + {b} + {c} = 1"
        statement_lhs, statement_rhs : string template
            statement_lhs \ge statement_rhs
            example : "(1:ℝ)/{a} + (1:ℝ)/{b} + (1:ℝ)/{c} ≥ (9 : "
            statement_lhs : "(1:ℝ)/{a} + (1:ℝ)/{b} + (1:ℝ)/{c}"
            statement_rhs : "(9:ℝ)"
        """
        if name is not None:
            self.name = name
        else:
            self.name = "thm_temp"
        self.variables = variables
        self.condition = condition
        self.statement_lhs = statement_lhs
        self.statement_rhs = statement_rhs
    
    def set_name(self, name):
        self.name = name

    def set_variables(self, variables):
        self.variables = variables
    
    def set_condition(self, condition):
        self.condition = condition

    def set_statement_lhs(self, statement_lhs):
        self.statement_lhs = statement_lhs
    
    def set_statement_rhs(self, statement_rhs):
        self.statement_rhs = statement_rhs
    
    def to_lean(self):
        statement_template = "theorem {name} ({vars} : ℝ) {trivial_conditions} {condition}: {statement_lhs} ≥ {statement_rhs} := by\n"

        # deal with variables
        self.variables.sort()
        var_str = ' '.join(self.variables)

        # deal with the trivial conditions (ha : a > 0)
        trivial_condition_template = "( h{v} : {v} > 0 )"
        trivial_condition_list = [trivial_condition_template.format(v=a) for a in self.variables]
        trivial_condition_str = ' '.join(trivial_condition_list)

        variable_dict = dict()
        for v in self.variables:
            variable_dict[v] = v

        # deal with the conditions (if exists)
        if self.condition == None:
            condition_str = ""
        else:
            condition_str = self.condition.format(**variable_dict)
            condition_str = f"( hcond : {condition_str} )"
        
        statement_str = statement_template.format(
            name=self.name,
            vars=var_str,
            trivial_conditions=trivial_condition_str,
            condition=condition_str,
            statement_lhs=self.statement_lhs.format(**variable_dict),
            statement_rhs=self.statement_rhs.format(**variable_dict),
        )

        return statement_str

if __name__ == '__main__':
    P = IneqProblem()
    P.set_name("test")
    P.set_variables(["a", "b", "c"])
    P.set_condition("{a} + {b} + {c} = 1")
    P.set_statement_lhs("(1:ℝ)/{a} + (1:ℝ)/{b} + (1:ℝ)/{c}")
    P.set_statement_rhs("(9:ℝ)")
    print(P.to_lean())
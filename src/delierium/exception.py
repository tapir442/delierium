class DelieriumNotALinearPDE(TypeError):
    def __init__ (self, expression):
        super().__init__(f"{expression=} is not a valid term in linear PDE")

class DelieriumInconsistentVariableOrder(ValueError):
    def __init__(self, functions):
        txt = "Functions with different variable ordering:\n"
        for _ in functions:
            txt += f"{_}: {_.operands()}\n"
        super().__init__(txt)
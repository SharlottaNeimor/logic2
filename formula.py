import re

IMPLICATION = '>'
NEGATION = '!'
CONJUNCTION = '&'
DISJUNCTION = '|'
EQUIVALANCE = '@'

class Formula:
    def __init__(self,string):
        self.string = string
    def adoptate(self):
        sF = self.sub_formulas()
        if sF == False:
            return self
        if sF[1] == IMPLICATION: return sF[0][0].adoptate().implic(sF[0][1].adoptate())
        elif sF[1] == NEGATION: return sF[0][0].adoptate().neg()
        elif sF[1] == CONJUNCTION: return sF[0][0].adoptate().implic(sF[0][1].adoptate().neg()).neg()
        elif sF[1] == DISJUNCTION: return sF[0][0].adoptate().neg().implic(sF[0][0].adoptate())
        elif sF[1] == EQUIVALANCE: return sF[0][0].implic(sF[0][1]).con(sF[0][1].implic(sF[0][0])).adoptate()
    def __call__(self,x=None):
        if x == None: return self.string
        i = 0
        formated = re.sub(r'(\d+)', (lambda m: '['+m.group(1)+']'), self())
        sub_F = self.sub_formulas()
        if sub_F:
            if sub_F[1] == NEGATION: return not sub_F[0][0](x)
            elif sub_F[1] == CONJUNCTION: return sub_F[0][0](x) and sub_F[0][1](x)
            elif sub_F[1] == DISJUNCTION: return sub_F[0][0](x) or sub_F[0][1](x)
            elif sub_F[1] == IMPLICATION:
                if sub_F[0][0](x) == False: return True
                if sub_F[0][1](x) == True: return True
                else: return False
            elif sub_F[1] == EQUIVALANCE: return sub_F[0][0](x) == sub_F[0][1](x)
        else:
            return eval(formated)%2
    def isTautology(self):
        alphas = []
        arity = self.arity()
        for i in range(2**(arity)):
            alpha = [0]*arity
            v = str(bin(i))[2:]
            for l in range(len(v)):
                alpha[l] = int(v[len(v)-l-1])
            alpha = list(reversed(alpha))
            alphas.append(alpha)
        for alpha in alphas:
            if self(alpha) == False: return False
        return True
    def __eq__(self,o): 
        if o == None: return False
        return self.string == o.string
    def arity(self): return len(self.variables())
    def implic(self,G): return Formula('('+self()+IMPLICATION+G()+')')
    def neg(self): return Formula('('+NEGATION+self()+')')
    def con(self,G): return Formula('('+self()+CONJUNCTION+G()+')')
    def dis(self,G): return Formula('('+self()+DISJUNCTION+G()+')')
    def eqv(self,G): return Formula('('+self()+EQUIVALANCE+G()+')')
    def variables(self):
        L = list(set(map(lambda x: 'x'+x,re.findall(r'\d+',self()))))
        L.sort(key = lambda x: int(x[1:]))
        return L
    def semantic(self):
        semantic_string = []
        semantic = []
        for i in self():
            if i == '(' or i == ')': semantic_string.append(i)
        for i in range(len(semantic_string)):
            if semantic_string[i] == ')':
                for j in range(i):
                    if semantic_string[j] == '(': m = j
                semantic.append([m,i])
                semantic_string[i] = " "
                semantic_string[m] = " "
        return semantic
    def sub_formulas(self):
        if self()[2:-1].isdigit(): return False
        if self()[:3] == '('+NEGATION+'(':
            return [[Formula(self()[2:-1])],NEGATION]
        else:
            F = self()
            F1 = Formula(self()[1:len(self())-1])
            out = []
            start = None
            for pair in F1.semantic():
                if 0 in pair: start = pair
                elif start and start[1]+1 in pair: end = pair
            count = -3
            for i in range(len(F[1:len(F)-1])):
                if F[i] == ')' or F[i] == '(': count += 1
                if count == start[1]:
                    start[1] = 0
                    out.append(Formula(F[1:i-1]))
            out.append(Formula(F[len(out[0]())+2:len(F)-1]))
            return [out,F[len(out[0]())+1]]
    def pow_alpha(self,alpha):
        if self(alpha) == 0: return self.neg()
        return self
    @staticmethod
    def formulate(string): return Formula('('+string+')')
if __name__ == '__main__':
    x1 = Formula('(x1)')
    x2 = Formula('(x0)')
    A = x1.con(x2)
    print(A.adoptate()())
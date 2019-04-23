from formula import *
from logger import Loger

log = Loger('./out.txt')

def modus_ponens(F:Formula,G:Formula):
    sub_G = G.sub_formulas()
    if sub_G and sub_G[0][0] == F and sub_G[1] == IMPLICATION:
        log.write(sub_G[0][1], 'from modus_ponens for {0} and {1}\n'.format(F(),G()))
        return sub_G[0][1]

def is_modus_ponens(F:Formula,G:Formula,H:Formula):
    return F == modus_ponens(G,H)

def _A1(A:Formula,B:Formula):
    log.write( A.implic(B.implic(A)), 'from A1 to {0} and {1}\n'.format(A(),B()))
    return A.implic(B.implic(A))

def _A2(A:Formula,B:Formula,C:Formula):
    log.write(A.implic(B.implic(C)).implic(A.implic(B).implic(A.implic(C))) , 'from A2 to {0} and {1} and {2}\n'.format(A(),B(),C()))
    return A.implic(B.implic(C)).implic(A.implic(B).implic(A.implic(C)))
    
def _A3(A:Formula,B:Formula):
    log.write( A.implic(A.dis(B)), 'from A3 to {0} and {1}\n'.format(A(),B()))
    return A.implic(A.dis(B))

def _A4(A:Formula,B:Formula):
    log.write( A.implic(A.dis(B)), 'from A4 to {0} and {1}\n'.format(A(),B()))
    return B.implic(A.dis(B))

def _A5(A:Formula,B:Formula,C:Formula):
    log.write(A.implic(C).implic(B.implic(C).implic(A.dis(B).implic(C))) , 'from A5 to {0} and {1} and {2}\n'.format(A(),B(),C()))
    return A.implic(C).implic(B.implic(C).implic(A.dis(B).implic(C)))
    
def _A6(A:Formula,B:Formula):
    log.write( A.con(B).implic(A), 'from A6 to {0} and {1}\n'.format(A(),B()))
    return A.con(B).implic(A)

def _A7(A:Formula,B:Formula):
    log.write( A.con(B).implic(B), 'from A7 to {0} and {1}\n'.format(A(),B()))
    return A.con(B).implic(B)
    
def _A8(A:Formula,B:Formula,C:Formula):
    log.write(A.implic(B).implic(A.implic(C).implic(A.implic(B.con(C)))) , 'from A8 to {0} and {1} and {2}\n'.format(A(),B(),C()))
    return A.implic(B).implic(A.implic(C).implic(A.implic(B.con(C))))
    
def _A9(A:Formula,B:Formula):
    if A.sub_formulas()[1] != NEGATION and B.sub_formulas()[1] != NEGATION:
        log.write( A.implic(B).implic(A.implic(B.neg()).implic(A.neg())), 'from A9 to {0} and {1}\n'.format(A(),B()))
        return A.implic(B).implic(A.implic(B.neg()).implic(A.neg()))
    elif A.sub_formulas()[1] == NEGATION and B.sub_formulas()[1] != NEGATION:
        _A10(A)
        A = A.sub_formulas()[0][0]
        log.write( A.neg().implic(B).implic(A.neg().implic(B.neg()).implic(A)), 'from A9 to {0} and {1}\n'.format(A(),B()))
        return A.neg().implic(B).implic(A.neg().implic(B.neg()).implic(A))
    elif A.sub_formulas()[1] != NEGATION and B.sub_formulas()[1] == NEGATION:
        _A10(B)
        B = B.sub_formulas()[0][0]
        log.write( A.implic(B.neg()).implic(A.implic(B).implic(A.neg())), 'from A9 to {0} and {1}\n'.format(A(),B()))
        return A.implic(B.neg()).implic(A.implic(B).implic(A.neg()))
    elif A.sub_formulas()[1] == NEGATION and B.sub_formulas()[1] == NEGATION:
        _A10(A)
        _A10(B)
        B = B.sub_formulas()[0][0]
        A = A.sub_formulas()[0][0]
        log.write( A.neg().implic(B.neg()).implic(A.neg().implic(B).implic(A)), 'from A9 to {0} and {1}\n'.format(A(),B()))
        return A.neg().implic(B.neg()).implic(A.neg().implic(B).implic(A))

def _A10(A:Formula):
    log.write( A.neg().neg().implic(A), 'from A10 to {0}\n'.format(A()))
    return A.neg().neg().implic(A)

def A1(F:Formula,G:Formula): return _A1(F,G)
def A2(F:Formula,G:Formula,H:Formula): return _A2(F,G,H)
def A3(F:Formula,G:Formula): return _A9(G.neg(),F.neg())

def deduction_theorem(Hypothesys,F,G,Conclusion):
    _Conclusion = []
    for i in range(len(Conclusion)):
        if i == 0:
            if Conclusion[0] == F:
                D = TL(F)
                _Conclusion.append(D)
            else:
                F11 = A1(Conclusion[i],F)
                D = modus_ponens(Conclusion[i],F11)
                _Conclusion.append(F11)
                _Conclusion.append(D)
        else:
            T = True
            for p in range(i):
                for q in range(i):
                    if is_modus_ponens(Conclusion[i],Conclusion[p],Conclusion[q]):
                        F12 = A2(F,Conclusion[p],Conclusion[i])
                        F22 = modus_ponens(F.implic(Conclusion[q]),F12)
                        D = modus_ponens(F.implic(Conclusion[p]),F22)
                        _Conclusion.append(F12)
                        _Conclusion.append(F22)
                        _Conclusion.append(D)
                        T = False
            if T and Conclusion[i] == F:
                D = TL(F)
                _Conclusion.append(D)
            elif T:
                F11 = A1(Conclusion[i],F)
                D = modus_ponens(Conclusion[i],F11)
                _Conclusion.append(F11)
                _Conclusion.append(D)
    return [Hypothesys,D,_Conclusion]
    
def S1(F:Formula,G:Formula,H:Formula):
    Hypothesys = [F.implic(G),G.implic(H)]
    Conclusion = [F.implic(G),G.implic(H),F]
    P = modus_ponens(Conclusion[2],Conclusion[0])
    Conclusion.append(P)
    Q = modus_ponens(Conclusion[3],Conclusion[1])
    Conclusion.append(Q)
    return deduction_theorem(Hypothesys,F,H,Conclusion)

def S2(F:Formula,G:Formula,H:Formula):
    Hypothesys = [F.implic(G.implic(H)),G]
    Conclusion = [F.implic(G.implic(H)),G,F]
    P = modus_ponens(Conclusion[2],Conclusion[0])
    Conclusion.append(P)
    Q = modus_ponens(Conclusion[1],Conclusion[3])
    Conclusion.append(Q)
    return deduction_theorem(Hypothesys,F,G,Conclusion)

def T2(F:Formula):
    F1 = A3(F,F.neg().neg())
    F2 = _A10(F.neg())
    F3 = modus_ponens(F2,F1)
    F4 = A1(F2,F1)
    F5 = S1(F,F.neg().neg().neg().implic(F),F.neg().neg())[1]
    return F5
def T3(F:Formula,G:Formula):
    F1 = F.neg()
    F2 = A1(F,G.neg())
    F3 = modus_ponens(F,F2)
    F4 = A1(F1,G.neg())
    F5 = modus_ponens(F1,F4)
    F6 = A3(F,G)
    F7 = modus_ponens(F5,F6)
    F8 = modus_ponens(F3,F7)
    out = deduction_theorem([F1],F,F8,[F1,F2,F3,F4,F5,F6,F7,F8])
    out = deduction_theorem([],F1,out[1],out[2])
    return out[1]
def T4(F:Formula,G:Formula):
    F1 = A3(F,G)
    F2 = G.neg().implic(F.neg())
    F3 = modus_ponens(F2,F1)
    F4 = A1(F,G.neg())
    F5 = S1(F,G.neg().implic(F),G)[1]
    out0 = S1(F,G.neg().implic(F),G)[2]
    out = [F1,F2,F3,F4]
    out.extend(out0)
    out = deduction_theorem([],F2,F5,out)
    return out[1]
def T5(F:Formula,G:Formula):
    F1 = A3(G.neg(),F.neg())
    F2 = F.implic(G)
    F3 = T2(G)
    F4 = S1(F,G,G.neg().neg())[1]
    out = S1(F,G,G.neg().neg())[2]
    F5 = _A10(F)
    F6 = S1(F.neg().neg(),F,G.neg().neg())[1]
    out.extend(S1(F.neg().neg(),F,G.neg().neg())[2])
    F7 = modus_ponens(F6,F1)
    F8 = A1(G.neg(),F.neg().neg())
    F9 = S1(G.neg(),F.neg().neg().implic(G.neg()),F.neg())[1]
    out.extend(S1(G.neg(),F.neg().neg().implic(G.neg()),F.neg())[2])
    out = deduction_theorem([],F2,F9,out)
    return out[1]
def T6(F:Formula,G:Formula):
    out = []
    F1 = T5(F.implic(G),G)
    F2 = deduction_theorem([],F.implic(G),G,[F,F.implic(G),modus_ponens(F,F.implic(G))])[1]
    out.extend(deduction_theorem([],F,F.implic(G),[F,F.implic(G),modus_ponens(F,F.implic(G))])[2])
    F3 = modus_ponens(F2,F1)
    out.append(F3)
    out = deduction_theorem([],F,F3,out)
    return out[1]
def T7(F:Formula,G:Formula):
    F1 = F.implic(G)
    F2 = T5(F,G)
    F3 = A3(F,G)
    F4 = S1(F1,G.neg().implic(F.neg()),G.neg().implic(F).implic(G))[1]
    out = S1(F1,G.neg().implic(F.neg()),G.neg().implic(F).implic(G))[2]
    F5 = modus_ponens(F1,F4)
    F6 = T4(G.neg(),F)
    F7 = Sub_Lemma_For_T7(F,G)
    F8 = S1(F.neg().implic(G),F.neg().implic(G.neg().neg()),G.neg().implic(F))[1]
    out.extend(S1(F.neg().implic(G),F.neg().implic(G.neg().neg()),G.neg().implic(F))[2])
    F9 = S1(F.neg().implic(G),G.neg().implic(F),G)[1]
    out.extend(S1(F.neg().implic(G),G.neg().implic(F),G)[2])
    out = deduction_theorem([],F1,F9,out)
    return out[1]
def Sub_Lemma_For_T7(F:Formula,G:Formula):
    F1 = F.neg()
    F2 = F.neg().implic(G)
    F3 = modus_ponens(F1,F2)
    F4 = T2(G)
    F5 = modus_ponens(F3,F4)
    T = deduction_theorem([F2,F3,F4],F1,G.neg().neg(),[F1,F2,F3,F4,F5])
    F6 = T[1]
    out = T[2]
    out = deduction_theorem([],F2,F6,out)
    return out[1]

def TL(F:Formula):
    F1 = A2(F,F.implic(F),F)
    F2 = A1(F,F.implic(F))
    F3 = modus_ponens(F2,F1)
    F4 = A1(F,F)
    F5 = modus_ponens(F4,F3)
    return F5
    
def kalmar_lemma(F,alpha):
    out = []
    if F.sub_formulas() == False:
        out.extend([F.pow_alpha(alpha)])
    else:
        if F.sub_formulas()[1] == NEGATION:
            if F(alpha) == 1:
                out.extend(kalmar_lemma(F.sub_formulas()[0][0],alpha))
            else:
                out.extend(kalmar_lemma(F.sub_formulas()[0][0],alpha))
                out.append(T2(out[len(out)-1]))
        elif F.sub_formulas()[1] == IMPLICATION:
            sF = F.sub_formulas()[0]
            if sF[0](alpha) == 0:
                out.extend(kalmar_lemma(sF[0],alpha))
                F1 = out[len(out)-1]
                out.append(T3(sF[0],sF[1]))
                F2 = out[len(out)-1]
                F3 = modus_ponens(F1,F2)
                out.append(F3)
            elif sF[1](alpha) == 1:
                out.extend(kalmar_lemma(sF[1],alpha))
                F1 = out[len(out)-1]
                F2 = A1(F1,sF[0])
                out.append(F2)
                F3 = modus_ponens(F1,F2)
                out.append(F3)
            else:
                out.extend(kalmar_lemma(sF[0],alpha))
                F1 = out[len(out)-1]
                out.extend(kalmar_lemma(sF[1],alpha))
                F2 = out[len(out)-1]
                out.append(T6(sF[0],sF[1]))
                F3 = out[len(out)-1]
                F4 = modus_ponens(F1,F3)
                F5 = modus_ponens(F2,F4)
                out.append(F4)
                out.append(F5)
        elif F.sub_formulas()[1] == CONJUNCTION:
            sF = F.sub_formulas()[0]
        elif F.sub_formulas()[1] == DISJUNCTION:
            sF = F.sub_formulas()[0]
    return out

def gen_alphas(arity):
    alphas = []
    for i in range(2**(arity)):
        alpha = [0]*arity
        v = str(bin(i))[2:]
        for l in range(len(v)):
            alpha[l] = int(v[len(v)-l-1])
        alpha = list(reversed(alpha))
        alphas.append(alpha)
    return alphas

def adequacy_theorem(F:Formula):
    if not F.isTautology(): return None
    _arity = F.arity()
    out = [None]*_arity
    vars = F.variables()
    ALPHAS = gen_alphas(_arity) #!
    for i in range(_arity):
        out[i] = kalmar_lemma(F,ALPHAS[i])
    while _arity != 0:
        ALPHAS = gen_alphas(_arity)
        for i in range(_arity):
            ALPHAS[i][len(ALPHAS[i])-1] = 1
            Hypothesys = []
            for j in range(_arity-2):
                Hypothesys.append(Formula('('+vars[j]+')').pow_alpha(ALPHAS[i]))
            T = deduction_theorem(Hypothesys,Formula('('+vars[_arity-1]+')').pow_alpha(ALPHAS[i]),F,out[i])
            F1 = T[1]
            F1_ = T[2]

            ALPHAS[i][len(ALPHAS[i])-1] = 0
            T = deduction_theorem(Hypothesys,Formula('('+vars[_arity-1]+')').pow_alpha(ALPHAS[i]),F,out[i])
            F2 = T[1]
            F2_ = T[2]
            
            F3 = T7(Formula('('+vars[_arity-1]+')'),F)
            F4 = modus_ponens(F1,F3)
            F5 = modus_ponens(F2,F4)

            res = F1_
            res.extend(F2_)
            res.append(F4)
            res.append(F5)
            out[i] = res
        _arity = _arity-1
    return res
    
if __name__ == '__main__':
    x1 = Formula('(x1)')
    x2 = Formula('(x0)')
    stri = '-'*(len(x1.implic(x2).implic(x1).implic(x1)())+4)
    print(stri)
    print('|',x1.implic(x2).implic(x1).implic(x1)(),'|')
    print(stri)
    adequacy_theorem(x1.implic(x2).implic(x1).implic(x1))
    print('---------------------------')
    print('|','DONE','|','CHECK IN OUT.TXT','|')
    print('---------------------------')
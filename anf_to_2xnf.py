#!/usr/bin/env python3

# tool for computing 2-XNF representations of polynomial systems
# type python3 anf_to_2xnf.py -h for more information

import sys, os, time
from xnf import *
from anf import *
import random
import itertools
import subprocess

# field with two elements for galois package
F2 = None

# set storing all substitutions
subs = set()


# number of indeterminates in the original polynomial system
# needed for Xnf.deleteVars(...)
origNumIndets = 0


# -------------------------------------------------------
# functions for finding good substitution
# -------------------------------------------------------

def findSub_singleterm(anf):
    """
    Returns a substitution that substitutes the leading term of anf.
    Input has to be a quadratic Anf.
    """
    global args
    assert(anf.deg() == 2)
    t = next(s for s in anf.support if s.deg() >= 2)
    return Sub([frozenset({max(t.indets)}),frozenset({min(t.indets)})])


def findSub_bracket(anf):
    """
    Returns a substitution supported by anf using factorization.
    Input has to be a quadratic Anf.
    """
    global args
    assert(anf.deg() == 2)
    S = []
    inds = set().union(*[t.getIndets() for t in anf.support])
    # start with substitutions representing x[i]*(x[j1]+x[j2]+...)
    for i in inds:
        j2 = {j for j in inds if Term({i,j}) in anf.support and i != j}
        if len(j2) > 0 and j2 != {i}:
            S.append(frozenset({frozenset({i}),frozenset(j2)}))
    # pairs that have to be considered
    newPairs = [ [i,j] for i in range(len(S)) for j in range(i,len(S)) ]
    it = 0 # count iterations of while loop
    num_checks = 0 # count number of pair checks
    # loop combines substitutions to find new ones until no new pairs are left or the maximum number of iterations is reached
    while True:
        it += 1
        if args.verbosity >= 60:
            print(f"findSub: iteration {it}, found subs: {len(S)}, len of new pairs: {len(newPairs)}", end="\r") # for more information
        pairs = newPairs
        if args.randomize:
            random.shuffle(pairs)
        newPairs = []
        for [n1,n2] in pairs:
            if args.verbosity >= 60 and num_checks % 100 == 0:
                print(f"findSub: iteration {it}, found subs: {len(S)}, len of new pairs: {len(newPairs)}", end="\r") # for more information
            # break after timeout
            sub1 = list(S[n1]); sub2 = list(S[n2])
            # foreach combination sub1={M0,M1}, sub2={N0,N1}
            for M0,M1 in [(sub1[0],sub1[1]),(sub1[1],sub1[0])]:
                for N0,N1 in [(sub2[0],sub2[1]),(sub2[1],sub2[0])]:
                    l1 = M0 & N0; l2 = M1 | N1
                    if not(len(l1) == 0) and not(l1 == l2):
                        newSub = frozenset({l1, l2})
                        if not(newSub in S):
                            S.append(newSub)
                            newPairs.extend(itertools.product(range(len(S)-1),[len(S)-1]))
            num_checks += 1
            if num_checks > args.quadIterations:
                break
        if len(newPairs) == 0:
            break
    assert(len(S) > 0)
    # chooses random substituion, but better substitutions are chosen with higher probability
    S = [list(s) for s in S]
    return Sub(random.choices(S,[sub_size(x) for x in S])[0])



def findSub_OMT(anf):
    """
    Same as findSub_bracket, but uses OptiMathSAT to find a good substitution
    Input has to be a quadratic Anf.
    """
    global args
    if not( os.popen(args.omspath+" -version").read().lower().startswith("mathsat5 version") ):
        raise Exception("OptiMathSAT could not be found in given path.")
    inds = anf.getHomogComp(2).variables()
    assert(anf.deg() == 2)
    if args.verbosity >= 50:
        print(f"findSub_OMT: {len(inds)} variables in deg 2 component")
        print("findSub_OMT: Constructing equations for OptiMathSAT")
    # create input string for OptiMathSAT
    s = OMSeqs(anf,inds)
    if args.verbosity >= 50:
        print("findSub_OMT: Waiting for OptiMathSAT")
    echo = subprocess.Popen(("echo", s), stdout=subprocess.PIPE)
    output = subprocess.check_output((args.omspath, "-optimization=TRUE", "-verbosity=0"), stdin=echo.stdout)
    if args.verbosity >= 50:
        print("findSub_OMT: Processing output of OptiMathSAT")
    output = output.decode("utf-8")
    output = output.replace(" ","").replace("(((","((").replace("))",")")
    l = output.split("\n")
    a = set()
    b = set()
    for w in output.split("\n"):
        if w[0:3] == "((a" and w[-2] == "1":
                a.add(int(w[3:-3]))
        if w[0:3] == "((b" and w[-2] == "1":
                b.add(int(w[3:-3]))
    sub = Sub([frozenset(a),frozenset(b)])
    if args.verbosity >= 50:
        print(f"findSub_OMT: found substitution of size {len(a)}x{len(b)}")
    return sub


def findSub_MaxSAT(anf):
    """
    Same as findSub_OMT, but uses a MaxSAT solver to find a good substitution
    Note: Python package pysat has to be installed.
    For details see https://pysathq.github.io/installation/
    Input has to be a quadratic Anf.
    """
    global args
    inds = list(anf.getHomogComp(2).variables())
    assert(anf.deg() == 2)
    # solving part
    try:
        from pysat.examples.rc2 import RC2
        from pysat.formula import WCNF
    except Exception as error:
        raise Exception("An error occurred while loading PySAT:\n" + repr(error))
    wcnf = WCNF()
    # a and b variables s.t. f ~ (a[0]inds[0]+...+a[n]inds[n])(b[0]inds[0]+...)
    a = list(range(1,len(inds)+1))
    b = list(range(len(inds)+1,2*len(inds)+1))
    y = 2*len(inds)+1 # additional variable number
    for i in range(len(inds)):
        for j in range(len(inds)):
            if i >= j: continue;
            # cnf representation of the equation y*(a[i]b[j]+a[j]b[i])=0
            if Term([inds[i],inds[j]]) in anf.support:
                wcnf.append([-y,a[i],a[j]])
                wcnf.append([-y,a[i],b[i]])
                wcnf.append([-y,b[j],a[j]])
                wcnf.append([-y,b[j],b[i]])
                wcnf.append([-y,-a[i],-a[j],-b[i],-b[j]])
            else:
                wcnf.append([-y,a[j],-a[i],-b[j]])
                wcnf.append([-y,b[i],-a[i],-b[j]])
                wcnf.append([-y,a[i],-a[j],-b[i]])
                wcnf.append([-y,b[j],-a[j],-b[i]])
            wcnf.append([y],weight=1)
            y += 1
    sol = RC2(wcnf).compute()
    a = {inds[i-1] for i in sol[:len(inds)] if i >= 0}
    b = {inds[i-len(inds)-1] for i in sol[len(inds):2*len(inds)] if i > 0}
    sub = Sub([frozenset(a),frozenset(b)])
    if args.verbosity >= 50:
        print(f"findSub_MaxSAT: found substitution of size {a}x{b}")
    return sub


def findOptimalSubs(anf):
    """
    Uses CryptoMiniSat to convert anf optimal (i.e. with a minimal number of substitutions).
    Needs CryptoMiniSat to be installed, see https://github.com/msoos/cryptominisat.
    Input has to be a quadratic Anf.
    """
    global args
    inds = list(anf.getHomogComp(2).variables())
    n = len(inds)
    assert(anf.deg() == 2)
    # solving part
    # increase r until a solution is found
    r = 1
    while "apples"!="oranges": # fancy way of writing "while True"
        if args.verbosity >= 50:
            print(f"findOptimalSubs: Starting iteration Nr. {r}"+" "*30)
        # first create XNF containing all hard clauses
        clauses = []
        # create additional variables
        # f = (sum from k=1 to r) (A[k,0]+A[k,1]*x[1]+...+A[k,n]*x[n])(B[k,0]+B[k,1]*x[1]+...+B[k,n]*x[n])
        # Y[k,i,j] additional variable for A[k,i]B[k,j]
        A = dict()
        B = dict()
        Y = dict()
        # first initialize A and B for better readability of the output
        numVars = 1
        for k in range(1,r+1):
            for i in range(n+1):
                A[k,i] = numVars; numVars+=1;
        for k in range(1,r+1):
            for i in range(n+1):
                B[k,i] = numVars; numVars+=1;
        for k in range(1,r+1):
            for i in range(n+1):
                for j in range(n+1):
                    Y[k,i,j] = numVars; numVars += 1;
        # add clauses to xnf
        # first definition of additional variables
        for k in range(1,r+1):
            for i in range(n+1):
                for j in range(n+1):
                    clauses.extend([xClause([[-Y[k,i,j]], [A[k,i]]]),
                                    xClause([[-Y[k,i,j]], [B[k,j]]]),
                                    xClause([[Y[k,i,j]], [-A[k,i]], [-B[k,j]]])])
        # (linear) clauses for c_ij
        for i in range(1,n+1):
            for j in range(i+1,n+1):
                l = sum([lineral([Y[k,i,j],Y[k,j,i]]) for k in range(1,r+1)],lineral([]))
                if Term([inds[i-1],inds[j-1]]) in anf.support:
                    clauses.append(xClause([l]))
                else:
                    clauses.append(xClause([l.Not()]))
        # (linear) clauses for c_ii
        for i in range(1,n+1):
            l = sum([lineral([Y[k,i,i],Y[k,0,i],Y[k,i,0]]) for k in range(1,r+1)],lineral([]))
            if Term([inds[i-1]]) in anf.support:
                clauses.append(xClause([l]))
            else:
                clauses.append(xClause([l.Not()]))
        # (linear) clause for c_0
        l = lineral([Y[k,0,0] for k in range(1,r+1)])
        if Term([]) in anf.support:
            clauses.append(xClause([l]))
        else:
            clauses.append(xClause([l.Not()]))
        x = Xnf(clauses,numVars)
        if args.verbosity >= 50:
            print(f"Solving XNF with {x.getNumVars()} variables and {x.getNumClauses()} clauases...",end="\r")
        sat, solution = x.solve()
        if sat:
            break
        else:
            r += 1
    # construct substitutions
    subs = set()
    for k in range(1,r+1):
        a = {inds[i-1] for i in range(1,n+1) if solution[A[k,i]]}
        b = {inds[i-1] for i in range(1,n+1) if solution[B[k,i]]}
        if solution[A[k,0]]:
            a.add(0)
        if solution[B[k,0]]:
            b.add(0)
        if a == b:
            continue
        if args.verbosity >= 50:
            print(f"Found sub: {a}x{b}"+" "*30)
        subs.add(Sub([frozenset(a-{0}),frozenset(b-{0})]))
    return subs


def findOptimalSubs_quad(anf):
    """
    Same as findOptimalSubs, but only finds substitutions that substitute quadratic terms (and not linear ones).
    Needs CryptoMiniSat to be installed, see https://github.com/msoos/cryptominisat.
    Input has to be a quadratic Anf.
    """
    global args
    inds = list(anf.getHomogComp(2).variables())
    n = len(inds)
    assert(anf.deg() <= 2)
    # solving part
    # increase r until a solution is found
    r = 1
    while "apples"!="oranges": # fancy way of writing "while True"
        if args.verbosity >= 50:
            print(f"findOptimalSubs: Starting iteration Nr. {r}"+" "*30)
        # first create XNF containing all hard clauses
        clauses = []
        # create additional variables
        # (quad part of f) = (sum from k=1 to r) (A[k,1]*x[1]+...+A[k,n]*x[n])(B[k,1]*x[1]+...+B[k,n]*x[n])
        # Y[k,i,j] additional variable for A[k,i]B[k,j]
        A = dict()
        B = dict()
        Y = dict()
        # first initialize A and B for better readability of the output
        numVars = 1
        for k in range(1,r+1):
            for i in range(1,n+1):
                A[k,i] = numVars; numVars+=1;
        for k in range(1,r+1):
            for i in range(1,n+1):
                B[k,i] = numVars; numVars+=1;
        for k in range(1,r+1):
            for i in range(1,n+1):
                for j in range(1,n+1):
                    Y[k,i,j] = numVars; numVars += 1;
        # add clauses to xnf
        # first definition of additional variables
        for k in range(1,r+1):
            for i in range(1,n+1):
                for j in range(1,n+1):
                    clauses.extend([xClause([[-Y[k,i,j]], [A[k,i]]]),
                                    xClause([[-Y[k,i,j]], [B[k,j]]]),
                                    xClause([[Y[k,i,j]], [-A[k,i]], [-B[k,j]]])])
        # (linear) clauses for c_ij
        for i in range(1,n+1):
            for j in range(i+1,n+1):
                l = sum([lineral([Y[k,i,j],Y[k,j,i]]) for k in range(1,r+1)],lineral([]))
                if Term([inds[i-1],inds[j-1]]) in anf.support:
                    clauses.append(xClause([l]))
                else:
                    clauses.append(xClause([l.Not()]))
        # A[k,i] and B[k,i] can never both be 1
        for k in range(1,r+1):
            for i in range(1,n+1):
                clauses.append(xClause([[-A[k,i]],[-B[k,i]]]))
        x = Xnf(clauses,numVars)
        if args.verbosity >= 50:
            print(f"Solving XNF with {x.getNumVars()} variables and {x.getNumClauses()} clauses...",end="\r")
        sat, solution = x.solve()
        if sat:
            break
        else:
            r += 1
    # construct substitutions
    subs = set()
    for k in range(1,r+1):
        a = {inds[i-1] for i in range(1,n+1) if solution[A[k,i]]}
        b = {inds[i-1] for i in range(1,n+1) if solution[B[k,i]]}
        if a == b:
            continue
        if args.verbosity >= 50:
            print("Found sub: " + str(a) + "x" + str(b)+" "*30)
        subs.add(Sub([frozenset(a),frozenset(b)]))
    return subs


def findSubs_linalg(anf):
    """
    Uses linear algebra to represent f using as few substitutions as possible.
    Writes f=l+l1*l2+...+l(n-1)*ln and uses linear relations among the l,l1,...,ln to rewrite f.
    Output is tuple ( [ (l1,l2), (l3,l4), ... ], l ).
    Input has to be a quadratic Anf.
    """
    def toSubFac(l):
        if Term() in l.support:
            return frozenset(l.variables()^{0})
        else:
            return frozenset(l.variables())
    return [ Sub([toSubFac(l1),toSubFac(l2)]) for l1,l2 in optimal_repr(anf,args.verbosity)[0] ]
        
    




def linPolyToXLit(f):
    """Takes a linear polynomial f and returns an lineral F with Z(f)=S(F)."""
    if Term() in f.getSupport():
        return lineral([t.getIndets().pop() for t in f.getSupport()-{Term()}],True)
    else:
        return lineral([t.getIndets().pop() for t in f.getSupport()],False)
    



def sub_size(sub):
    """
    Returns the number of terms of degree two in the polynomial Anf(sub[0])*Anf(sub[1]).
    Input: list [s1,s2] where s1 and s2 are sets or frozensets of integers
    """
    kl = len(sub[0]); km = len(sub[1]); k = len(sub[0] & sub[1])
    return kl*km - (k ** 2)
    
    

# Sub = Substitution
# facs is of the form [frozenset({i1,...,in}),frozenset({j1,...,jm})] for natural numbers i,j.
# represents substitution (x[i1]+...+x[in])(x[j1]+...+x[jn]) -> x[name] where x[0] == 1
# 1 is represented as 0, i.e. frozenset({1,2,0}) represents x[1]+x[2]+1
numSubs = 0 # number of instances of the class Sub
class Sub:
    indet = 0
    facs = 0 # [frozenset(int),frozenset(int)]
    def __init__(self, facs): # assumes facs is already of the desired form
        global indetDict
        global numSubs
        assert(not(frozenset() in facs))
        # key uses spaces so that it can not be one of the original variables
        key = "[var for (" + ")*(".join([str(Anf([[i] for i in fac-{0}])+(1 if 0 in fac else 0)) for fac in facs]) + ")]"
        # if same variable as this one already exist, create this as duplicate
        if key in indetDict.keys():
            self.indet = indNum(key)
        else:
            # indetDict["1"]=[], so len(indetDict) = <number of variables>+1
            self.indet = len(indetDict)
            indetDict[key] = self.indet
            numSubs += 1
        self.facs = facs
    def __str__(self):
        global indetDict
        return indStr(self.indet) + " replaces (" + ")*(".join([str(Anf([[i] for i in fac-{0}])+(1 if 0 in fac else 0)) for fac in self.facs]) + ")"
    def __repr__(self):
        return str(self)
    def __eq__(self,other):
        return frozenset(self.facs) == frozenset(other.facs)
    def __hash__(self):
        return hash(frozenset([frozenset(["i",self.indet]),
                               frozenset(["f",self.facs[0]]),
                               frozenset(["f",self.facs[1]])]))
    def applyTo(self,poly):
        """Takes a polynomial and returns the polynomial after substituting self in it."""
        return poly + self.getAnf()
    def getAnf(self):
        """Returns y+l1*l2 where y=self.indet and l1, l2 are the factors."""
        return Anf([[self.indet]]) \
            +(Anf(self.facs[0]-{0})+(1 if 0 in self.facs[0] else 0)) \
            *(Anf(self.facs[1]-{0})+(1 if 0 in self.facs[1] else 0))
    def getFacs(self):
        """Returns the factors l1,l2 of this substitution."""
        return self.facs
    def getSize(self):
        return sub_size(self.facs)
    def getIndet(self):
        """Returns the additional indeterminate for this substitution."""
        return self.indet
    def getXnf(self):
        """Returns an Xnf representation of this substitution."""
        global args
        y = lineral([self.indet],True);
        l1 = lineral(self.facs[0]-{0},0 in self.facs[0]);
        l2 = lineral(self.facs[1]-{0},0 in self.facs[1]);
        if args.txnf:
            if args.moreclauses:
                return Xnf([xClause([y+1,l1+1]),
                            xClause([y+1,l2+1]),
                            xClause([y+1,l1+1,l2]),
                            xClause([y,l2,l1])
                            ])
            else:
                # cannot be made more sparse, so --sparse leads here
                return Xnf([xClause([y+1,l1+1]),
                            xClause([y+1,l2+1]),
                            xClause([y,l2,l1])
                            ])                
        else:
            if args.sparse:
                return Xnf([xClause([y+1,l2+1]),
                            xClause([y+l1,l2]),
                            ])
            elif args.moreclauses:
                return Xnf([xClause([y+1,l1+1]),
                            xClause([y+1,l2+1]),
                            xClause([y+1,y+l1+l2]),
                            xClause([y+l1,l2]),
                            xClause([y+l2,l1]),
                            xClause([y+l2,y+l1])
                            ])
            else:
                return Xnf([xClause([y+1,l1+1]),
                            xClause([y+1,l2+1]),
                            xClause([y+l1,l2]),
                            ])
                

def applySubs(subs,g):
    """Takes a list or set of substitutions subs and applies them to a polynomial g if this reduces the number of quadratic terms."""
    for sub in subs:
        n = g.numTerms_nonLin()
        new = sub.applyTo(g)
        if new.numTerms_nonLin() < n:
            g = new
            if args.verbosity >= 40:
                print(f"Applied old sub! Now reduced from {n} terms to {g.numTerms_nonLin()} terms")
    return g


def anf_to_2xnf(system):
    """Takes a list of polynomials and converts it to 2-XNF."""
    global subs
    global args
    global sbox_given
    global sbox_polys
    global sbox_xnf
    global origNumIndets
    global indetDict
    assert(not(args.lfirst and args.sfirst))
    if args.lfirst:
        system.sort(key=Anf.numTerms_nonLin)
    if args.sfirst:
        system.sort(key=Anf.numTerms_nonLin)
        system.reverse()
    XNF = Xnf()
    # Loops over all polynomials in the system and converts them 1-by-1 to 2-XNF
    system_iter = iter(enumerate(system)) # to jump forward if sbox-polynomials are found
    for i, g in system_iter:
        if args.verbosity >= 15:
            print(f"Now processing Polynomial {i+1}/{len(system)}", end=("\r" if args.verbosity < 40 else "\n"))
        if args.verbosity >= 40 and g.deg() > 1:
            tmp = g.numTerms_nonLin()
            print(f"Terms of degree >1: {g.numTerms_nonLin()}, Indeterminates: {len(g.variables())}")
        # check whether following polynomials are s-Box-Polynomials
        if sbox_given and g.deg() > 1 and len(system)-i >= len(sbox_polys):
            candidates = set(system[i:i+len(sbox_polys)])
            indets = sorted(list({indet for f in candidates for indet in f.variables() }))
            found_sth = False
            if len(sbox_indetDict)-1 == len(indets):
                n = len(sbox_indetDict)-1
                # also check reversed S-Box
                for ind_candidates in [indets,indets[n//2:]+indets[:n//2]]:
                    substituted = { p.substIndets(sbox_inds,ind_candidates) for p in sbox_polys }
                    if candidates == substituted:
                        if args.verbosity >= 40:
                            print(f"Found S-Box polynomials! Now jump {len(sbox_polys)} steps further.")
                        XNF.extend(getSBoxXnf(ind_candidates))
                        _ = [next(system_iter) for r in range(len(sbox_polys)-1)]
                        # also increase i in case those are the last polynomials in the system
                        # (to avoid assertion after loop throwing an error)
                        i += len(sbox_polys)-1
                        found_sth = True
                        break
            if found_sth:
                continue
        while g.deg() > 2:
            # searches ind such that as many terms of deg >2 as possible are divisible by x[ind]
            badTerms = [t for t in g.support if t.deg() > 2]
            tmp = 0
            for i in g.variables():
                # count number of terms divisible by x[i]
                tmp_ = sum(i in t.indets for t in badTerms)
                if tmp_ > tmp:
                    tmp = tmp_
                    ind = i
            # write g = x[ind]*f+h where no term in h is divisible by x[i]
            xi = Term([ind])
            f = Anf([ t/xi for t in g.support if t.isDivisible(xi) ])
            h = g+xi*f
            # create additional indeterminate for substituting f
            key = "[var for "+str(f)+"]"
            if key in indetDict.keys():
                new_indet = indNum(key)
            else:
                new_indet = len(indetDict)
                indetDict[key] = new_indet
            # append y+f to system (y == name of new indeterminate)
            system.append(Anf([[new_indet]])+f)
            # replace g = x[ind]*f+h by x[ind]*x[new_indet]+h
            g = Anf([[ind,new_indet]]) + h
            if args.verbosity >= 40:
                print("Substituted:")
                print(f"    {xi}*({f}) + {h}")
                print(f" ~> {Anf([[ind,new_indet]])} + {h}")
        if args.optimal_subs or args.optimal_subs_quad or args.linalg:
            applySubs(subs,g)
            if args.optimal_subs:
                s = findOptimalSubs(g)
            if args.optimal_subs_quad:
                s = findOptimalSubs_quad(g)
            if args.linalg:
                s = findSubs_linalg(g)
            subs.update(s)
            if args.verbosity >= 40:
                print(f"Represented polynomial using {len(s)} substitutions."+" "*30)
            for sub in s:
                g = g + sub.getAnf()
        # quick substituion if args.onlyterms
        if args.onlyterms:
            lin_terms = [s for s in g.support if s.deg() < 2] # also contains Term()
            quad_terms = [s for s in g.support if s.deg() == 2]
            for t in quad_terms:
                # first check already found substitutions
                # if onlyterms is set, then all substitutions are of the form x[i]*x[j]
                sub = next((s for s in subs if t.indets == s.facs[0]|s.facs[1]),None)
                if sub is None:
                    sub = Sub([frozenset({max(t.indets)}),frozenset({min(t.indets)})])
                    subs.add(sub)
                lin_terms.append(Term([sub.indet]))
            g = Anf(lin_terms)
        # following loop is main part of function
        while g.deg() == 2:
            if args.verbosity > 50:
                print("Current poly:",g)
            # check if previous subs can be applied
            # has to be done in every iteration since new terms may be added with finSub_OMT or findSub_MaxSAT
            applySubs(subs,g)
            if g.deg() < 2:
                break;
            if args.omt:
                sub = findSub_OMT(g)
            elif args.maxsat:
                sub = findSub_MaxSAT(g)
            else:
                sub = findSub_bracket(g)
            assert(sub.getSize() > 0)
            subs.add(sub)
            g = g + sub.getAnf()
            if args.verbosity >= 40:
                print(f"Sub found! Remaining deg 2 terms: {g.numTerms_nonLin()}"+" "*30)
            if args.verbosity >= 60:
                print("Sub:",sub)
        XNF.append(linPolyToXLit(g))
    assert(i+1 == len(system))
    # interreduces substitutions and returns the corresponding XNF
    if args.verbosity >= 15:
        print("Interreducing Substitutions."+" "*10)
    XNF.extend(subsToXnf())
    if args.cleanup:
        XNF.cleanup(origNumIndets,indetDict)
    if args.cleanuphard:
        XNF.cleanup(0,indetDict)
    if args.cleanupvariables:
        XNF.cleanupVarnames(0,indetDict)
    return XNF



def subsToXnf():
    """Takes a list of substitutions, interreduces them, and returns the corresponding XNF."""
    global subs
    global args
    if args.onlyterms:
        xClauses = [ sub.getXnf() for sub in subs ]
        # return flattened list
        return Xnf([c for cList in xClauses for c in cList])
    global F2
    import galois
    if F2 is None:
        # ignore TBB outdated version warning
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            F2 = galois.GF(2)
    # first construct basis of polynomial vector space
    supps = []
    # following avoid calling sub.get_poly() multiple times
    subs_list = list(subs)
    subs_polys = [ sub.getAnf() + Anf([[sub.getIndet()]]) for sub in subs_list ]
    for i,p in enumerate(subs_polys):
        supps.extend(p.getSupport())
    # B is the set of all terms occuring in one of the substitutions
    # called B since it is the basis of a later used vector space
    B = list(set(supps))
    M = F2.Zeros((len(B),len(subs_list)))
    for i,p in enumerate(subs_polys):
        for t in p.support:
            M[B.index(t)][i] = 1
    N = F2(M).row_reduce()
    # pivot indices of N
    pivots = [ next((i for i,c in enumerate(row) if c == 1),-1) for row in N ]
    pivots = [ p for p in pivots if p >= 0 ]
    pivot_subs = [ subs_list[p] for p in pivots ]
    xClauses = []
    # add clauses from pivot subs
    for sub in pivot_subs:
        xClauses.extend(sub.getXnf().getXClauses())
    # add representations of non-pivot subs
    xClauses.extend([
        xClause(lineral(
            [sub.indet]+[s.indet for j,(s,c) in enumerate(zip(pivot_subs,subRepr)) if c == 1],
            False
        ))
        for i,sub in enumerate(subs_list)
        for subRepr in [N[:,i]]
        if not(i in pivots)
    ])
    if args.verbosity >= 30:
        print(f"Substitutions reduced from {len(subs_list)} to {len(pivots)}.")
    return Xnf(xClauses)




# -------------------------------------------------------------------------------
# auxiliary functions

sBoxVarNum = 0
def getSBoxXnf(indets):
    """Takes a list of indeterminates and returns the XNF of an S-Box (given in args.sBoxXnf in these indeterminates."""
    global sbox_xnf
    global indetDict
    global sBoxVarNum
    # numAdd = number of additional indets in the SBox-XNF
    numAdd = sbox_xnf.numVars - len(indets)
    numIndets_before = len(indetDict)-1
    numIndets_after = len(indetDict)+numAdd
    for i in range(numIndets_before+1,numIndets_after):
        sBoxVarNum += 1
        indetDict[f"[additional S-Box variable {sBoxVarNum}]"] = i
    # d : 
    d = {**dict(zip(range(1,len(indets)+1),indets)), **dict(zip(range(len(indets)+1,sbox_xnf.numVars+1),range(numIndets_before+1,numIndets_after)))}
    return [xClause([lineral([d[i] for i in l.lits],l.xnor) for l in c.xLits]) for c in sbox_xnf]



def OMSeqs(f,inds):
    """
    Helper function for findSub_OMT
    input : Anf f and its indeterminates inds
    output: String s which is an input for OptiMathSAT
    """
    s = "(set-option :produce-models true)\n"
    s +="(set-option :opt.priority lex)\n"
    # a and b are variables where f ~ (a1x1+...+anxn)(b1x1+...+bnxn)
    s += "(declare-fun a (Int) Int)\n"
    s += "(declare-fun b (Int) Int)\n"
    # assert that a and b map to 0 and 1
    s += "(assert (and (>= (a 0) 0) (<= (a 0) 1)))\n"
    s += "(assert (and (>= (b 0) 0) (<= (b 0) 1)))\n"
    for i in inds:
        s += f"(assert (and (>= (a {i}) 0) (<= (a {i}) 1)))\n"
        s += f"(assert (and (>= (b {i}) 0) (<= (b {i}) 1)))\n"
    # now polynomials are constructed
    # polynomials for quadratic terms
    s += "(declare-fun goal_quad (Int) Int)\n"
    s += "(declare-fun goal_lin (Int) Int)\n"
    goal_num_quad = 1
    for i in inds:
        for j in inds:
            if j <= i:
                continue;
            p1 = str(int(Term([i,j]) in f.support))
            s += """
(assert
  (= 
    (goal_quad """ + str(goal_num_quad) + """)
    (mod (+ (* (a """ + str(i) + """) (b """ + str(j) + """))
            (* (a """ + str(j) + """) (b """ + str(i) + """)) 
            """ + p1 + """
         )
     2
    )
  )
)"""
            goal_num_quad += 1
    # polynomials for linear terms
    goal_num_lin = 1
    for i in inds:
        p1 = str(int(Term([i]) in f.support))
        s += """
(assert
  (= 
    (goal_lin """ + str(goal_num_lin) + """)
    (mod (+ (* (a """ + str(i) + """) (b """ + str(0) + """))
            (* (a """ + str(0) + """) (b """ + str(i) + """))
            (* (a """ + str(i) + """) (b """ + str(i) + """)) 
            """ + p1 + """
         )
     2
    )
  )
)"""
        goal_num_lin += 1
    # polynomial for constant term
    s += f"\n(assert (= (goal_lin {goal_num_lin}) (+ (* (a 0) (b 0)) {int(Term() in f.support)})))"
    goal_num_lin += 1
    # both a and b have to contain at least 1 indeterminate
    s += "\n\n(assert (< 0 (+ " + " ".join(["(a " + str(i) + ")" for i in inds]) + ")))"
    s += "\n(assert (< 0 (+ " + " ".join(["(b " + str(i) + ")" for i in inds]) + ")))"
    # a and b should not be equal
    s += "\n\n(assert (or " + " ".join(["(not (= (a " + str(i) + ") (b " + str(i) + ")))" for i in inds]) + "))"
    # first priority: maximize number of quadratic terms
    s += "\n\n(declare-fun goal_sum_quad () Int)\n"
    if goal_num_quad > 2:
        s += "(assert (= goal_sum_quad (+ " + " ".join(["(goal_quad " + str(i) + ")" for i in range(1,goal_num_quad)]) + ")))\n"
    else:
        s += "(assert (= goal_sum_quad (goal_quad 1)))\n"
    s += "(minimize goal_sum_quad)\n"
    # second priority: minimize number of linear terms
    s += "\n\n(declare-fun goal_sum_lin () Int)\n"
    if goal_num_lin > 2:
        s += "(assert (= goal_sum_lin (+ " + " ".join(["(goal_lin " + str(i) + ")" for i in range(1,goal_num_lin)]) + ")))\n"
    else:
        s += "(assert (= goal_sum_lin (goal_lin 1)))"
    s += "(minimize goal_sum_lin)\n"
    # third priority: minimize non-zero coefficients
    s += "(declare-fun coeff_sum () Int)\n"
    s += "(assert (= coeff_sum (+ " + " ".join(["(a "+str(i)+") (b "+str(i)+")" for i in inds]) + ")))\n"
    s += "(minimize coeff_sum)\n"
    s += """
(get-objectives)
(check-sat)
(get-value ((a 0) """ + " ".join(["(a " + str(i) + ")" for i in inds]) + """
            (b 0) """ + " ".join(["(b " + str(i) + ")" for i in inds]) + """
            """ + " ".join(["(goal_quad " + str(i) + ")" for i in range(1,goal_num_quad)]) + """
            """ + " ".join(["(goal_lin " + str(i) + ")" for i in range(1,goal_num_lin)]) + """
            goal_sum_quad
            goal_sum_lin
            coeff_sum
           )
)"""
    return s;




# -------------------------------------------------------------------------------


import argparse
if __name__!='__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--verbosity",type=int,default=0)
    parser.add_argument("-qi","--quadIterations",type=int,default=3000,
                        help="Set a maximum number of iterations for standard substitution (number of pairs checked for factorizing polynomials).")
    args = parser.parse_args()
    # initialize 100 default indeterminates
    for i in range(1,100+1):
        indetDict["x["+str(i)+"]"] = i
else:
    parser = argparse.ArgumentParser()
    parser.add_argument("path",nargs='?',default=None,
                        help="Path of input. Input file has the following structure: The first line contains all indeterminates separated with a comma and AT LEAST ONE SPACE BAR, the other lines contain each exactly one polynomial. Polynomials sums (\'+\') of terms and a term is a product (\'*\') of indeterminates or simply \'1\'. Spaces and tabs are ignored and no indeterminate can be called 1. Comment lines are marked with a # at the beginning.")
    parser.add_argument("--seed", type=int,
                        help="Set seed to make random polynomials and conversion deterministic.")
    parser.add_argument("-v","--verbosity", type=int, default=10,
                        help="Sets verbosity level for command line output. Values range from 0 to 100")
    parser.add_argument("--quiet","-q", action="store_true",
                        help="Sets verbosity level to 0.")
    parser.add_argument("--no_conversion","-nc",action="store_true",
                        help="Does not do a conversion (only prints info for input ANF).")
    parser.add_argument("-xp","--oxnfpath",
                        help="Same as --cp, but stores the output in XNF file format.")
    parser.add_argument("-xcp","--oxcnfpath",
                        help="Stores the output XNF as DIMACS XCNF format in given path.")
    parser.add_argument("-cp","--ocnfpath",
                        help="Stores the output XNF as DIMACS CNF format in given path.")
    parser.add_argument("--oxnf", action="store_true",
                        help="If the input path is of the form name.ext, then the output XNF is stored in the file name.xnf as XNF format.")
    parser.add_argument("--oxcnf", action="store_true",
                        help="If the input path is of the form name.ext, then the output XNF is stored in the file name.cnf as DIMACS XCNF format (CNF clauses + XOR constraints).")
    parser.add_argument("--ocnf", action="store_true",
                        help="If the input path is of the form name.ext, then the output XNF is stored in the file name.cnf as DIMACS CNF format.")
    parser.add_argument("--txnf","--3xnf", action="store_true",
                        help="Sets the output to 3-XNF (instead of 2-XNF). The number of indeterminates stays the same, but there may be fewer clauses.")
    parser.add_argument("--sparse", action="store_true",
                        help="Reduces number of clauses in output (number of variables stays the same).")
    parser.add_argument("--moreclauses", action="store_true",
                        help="Enlarges number of clauses in output (number of variables stays the same).")
    parser.add_argument("-c","--cleanup","--gcp", action="store_true",
                        help="Does a short cleanup after computing the XNF (GCP and variable cleanup).")
    parser.add_argument("-ch","--cleanuphard", action="store_true",
                        help="Same as cleanup, but also deletes free variables from the ANF.")
    parser.add_argument("-cv","--cleanupvariables", action="store_true",
                        help="Only does a variable cleanup (no GCP). May also delete free variables from the ANF.")
    parser.add_argument("-sx","--sBoxXnf", type=str, 
                        help="Path to a previously comuted s-Box XNF. Only works in combination with --sBoxPolys.")
    parser.add_argument("-sp","--sBoxPolys", type=str, 
                        help="Path to a file containing S-Box polynomials that were used for computing the XNF in path --sBoxXnf. Only works in combination with --sBoxXnf.")
    parser.add_argument("--onlyterms", action="store_true", default=False,
                        help="Only substitutes single terms instead of longer products of linear polynomials.")
    parser.add_argument("--linalg", action="store_true", default=False,
                        help="Trys to find good substitutions using linear relations on previously found substitutions.")
    parser.add_argument("--maxsat", action="store_true", default=False,
                        help="Use a MaxSAT solver to substitute as many quadratic terms as possible at once (needs pysat to be installed; see https://pysathq.github.io/installation/)")
    parser.add_argument("--optimal_subs","-os", action="store_true", default=False,
                        help="Substitute single polynomials optimally using a SAT solver (needs cryptominisat to be installed; see https://github.com/msoos/cryptominisat).")
    parser.add_argument("--optimal_subs_quad","-osq", action="store_true", default=False,
                        help="Same as --optimal_subs, but only substitutes quadratic terms (needs cryptominisat to be installed; see https://github.com/msoos/cryptominisat).")
    parser.add_argument("-omt","--omt","-oms","--oms","--optimathsat", action="store_true", default=False,
                        help="Use the OMT solver OptiMathSAT to find subsitutions that substitute as many quadratic terms as possible at once (may be very inefficient).")
    parser.add_argument("--omspath", type=str, default=os.path.dirname(os.path.abspath(__file__))+"/optimathsat",
                        help="Give path to OptiMathSAT (only used if --optimathsat is set).")
    parser.add_argument("-qi","--quadIterations",type=int,default=3000,
                        help="Set a maximum number of iterations for standard conversion (number of pairs checked for factorizing polynomials).")
    parser.add_argument("--lfirst", action="store_true", default=False,
                        help="Only for quadratic polynomials: converts the polynomials one after each other by the number of their terms of degree 2 (longest first).")
    parser.add_argument("--sfirst", action="store_true", default=False,
                        help="Only for quadratic polynomials: converts the polynomials one after each other by the number of their terms of degree 2 (shortest first).")
    parser.add_argument("--randomize", action="store_true", default=False,
                        help="Makes standard conversion non-deterministic (for the cost of efficientcy).")
    args = parser.parse_args()

    
    # guarantee that only one conversion type is used
    assert(len([1 for i in [ args.onlyterms,
                             args.linalg,
                             args.maxsat,
                             args.optimal_subs,
                             args.optimal_subs_quad,
                             args.omt
                            ]
                if i ]) < 2)
    
               
    

    if args.seed is not None:
        random.seed(args.seed)
    
    if args.path == None:
        parser.print_usage(sys.stderr)
        quit()
    
    # checks for sBox input and tries to set default if exists
    polys_ex = False
    if args.sBoxPolys != None:
        sbox_indetDict = dict()
        sbox_indetDict["1"] = []
        sbox_polys = set(readPolySys(args.sBoxPolys,sbox_indetDict))
        sbox_inds = sorted([ v for v in sbox_indetDict.values() if isinstance(v,int) ])
        polys_ex = True
    
    xnf_ex = False
    if args.sBoxXnf != None:
        sbox_xnf = readXNF(args.sBoxXnf)
        xnf_ex = True
    
    sbox_given = False
    if polys_ex and xnf_ex:
        sbox_given = True
    
        
    # now main body
    system = [f for f in readPolySys(args.path,indetDict) if not(f == 0)]
    origNumIndets = len(indetDict)-1

    if len(system) == 0:
        if args.verbosity >= 5:
            print("WARNING: Given system is empty.")
        
    if args.quiet:
        args.verbosity = 0
    
    if args.verbosity >= 5:
        print(f"number of indeterminates: {len(indetDict)-1}")
        print(f"len of system:            {len(system)}")
        if len(system) > 0:
            print("average NumTerms:         " + str(sum([poly.numTerms() for poly in system])/len(system))[:5])
    t0 = time.time()

    
    if args.no_conversion:
        quit()
        
    XNF = anf_to_2xnf(system)
    
    
        
    if args.verbosity >= 5:
        print(f"ddv after conversion:                {XNF.ddv()}" + "".join([" " for i in range(70)]))
        print(f"number of variables after conversion: {XNF.getNumVars()}")
        print(f"number of clauses after conversion:   {XNF.getNumClauses()}")
    if args.verbosity >= 3:
        t1 = time.time()
        print(f"Running time:                         {str(t1-t0)[:5]} s")
        if len(system) > 0:
            print(f"effective number of variables:        {XNF.getNumVars()-XNF.ddv()[0]}")




    if args.verbosity >= 100 and len(system) < 10 and len(XNF) < 60: # probably just a toy example
        print("system:")
        print("  " + str(system))
        print("indeterminates:")
        print("  " + str(indetDict))
        print(XNF)
            
    if args.oxcnf:
        s = printIndets() + "\n" + XNF.asXcnf()
        path = args.path.rsplit(".",1)[0] + ".cnf"
        D = open(path, "w")
        print(s, file=D)
        D.close()
        if args.verbosity > 0:
            print(f"Created {path}")
        
    if args.ocnf:
        s = printIndets() + "\n" + XNF.asCnf()
        path = args.path.rsplit(".",1)[0] + ".cnf"
        D = open(path, "w")
        print(s, file=D)
        D.close()
        if args.verbosity > 0:
            print(f"Created {path}")
        
    if args.oxnf:
        s = printIndets() + "\n" + XNF.asXnf()
        path = args.path.rsplit(".",1)[0] + ".xnf"
        D = open(path, "w")
        print(s, file=D)
        D.close()
        if args.verbosity > 0:
            print(f"Created {path}")
    
    if args.oxcnfpath != None:
        s = printIndets() + "\n" + XNF.asXcnf()
        D = open(args.oxcnfpath, "w")
        print(s, file=D)
        D.close()
        if args.verbosity > 0:
            print(f"Created {args.oxcnfpath}")
        
    if args.ocnfpath != None:
        s = printIndets() + "\n" + XNF.asCnf()
        D = open(args.ocnfpath, "w")
        print(s, file=D)
        D.close()
        if args.verbosity > 0:
            print(f"Created {args.ocnfpath}")
        
    if args.oxnfpath != None:
        s = printIndets() + "\n" + XNF.asXnf()
        D = open(args.oxnfpath, "w")
        print(s, file=D)
        D.close()
        if args.verbosity > 0:
            print(f"Created {args.oxnfpath}")

#!/usr/bin/env python3

# tool for computing 2-XNF representations of polynomial systems
# type python3 anf_to_2xnf.py -h for more information

import sys, os, time
from xnf import *
from anf import *
import numpy as np
import random
import itertools
import subprocess


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
    return [ Sub([toSubFac(l1),toSubFac(l2)]) for l1,l2 in optimal_repr(anf,args.verbosity)[0][1:] ]
        


def sub_size(sub):
    """
    Returns the number of terms of degree two in the polynomial Anf(sub[0])*Anf(sub[1]).
    Input: list [s1,s2] where s1 and s2 are sets or frozensets of integers
    """
    kl = len(sub[0]); km = len(sub[1]); k = len(sub[0] & sub[1])
    return kl*km - (k ** 2)
    
    

# Sub = Substitution
# facs is of the form [frozenset({i1,...,in}),frozenset({j1,...,jm})] for natural numbers i,j.
# represents substitution (x[i1]+...+x[in])(x[j1]+...+x[jm]) -> x[name] where x[0] == 1
# 1 is represented as 0, i.e. frozenset({1,2,0}) represents x[1]+x[2]+1
numSubs = 0 # number of instances of the class Sub
class Sub:
    indet = 0
    facs = [] # [frozenset(int),...,frozenset(int)]
    indets = None
    anf = None
    is_term = False
    def __init__(self, facs): # assumes facs is already of the desired form
        global indetDict
        global numSubs
        assert(not(frozenset() in facs))
        assert(len(facs) > 1)
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
        if all(len(f) == 1 for f in self.facs):
            self.is_term = True
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
    def isTerm(self):
        """Returns whether self is of the form y+x1*...*xr."""
        return self.is_term
    def getAnf(self):
        """Returns y+l1*l2 where y=self.indet and l1, l2 are the factors."""
        if self.anf is None:
            self.anf = Anf([[self.indet]]) \
                +np.prod([ Anf(fac-{0}) + (1 if 0 in fac else 0) for fac in self.facs ])
        return self.anf
    def getFacs(self):
        """Returns the factors l1,l2 of this substitution."""
        return self.facs
    def getSize(self):
        assert(len(self.facs) == 2)
        return sub_size(self.facs)
    def getIndet(self):
        """Returns the additional indeterminate for this substitution."""
        return self.indet
    def getIndets(self):
        if self.indets is None:
            self.indets = set().union(*self.facs)
        return self.indets
    def getXnf(self):
        global args
        y = lineral([self.indet],True);
        lins = [ lineral(fac-{0}, 0 in fac) for fac in self.facs ]
        return special_poly_to_xnf(y,lins)

def special_poly_to_xnf(y,lins):
    """
    Returns the XNF representation of a polynomial of the form y+product(L) where y and all elements of L are linear polynomials.
    """
    global args
    if isinstance(y,Anf):
        y = lineral(y+1)
    lins = [ lineral(l) if isinstance(l,Anf) else l for l in lins ]
    assert([args.sparse,args.moreclauses,args.fewer_linerals].count(True) < 2)
    if args.sparse:
        return Xnf([ xClause([y+lins[0]] + lins[1:]) ] \
                   +[ xClause([y+1, l+1]) for l in lins[1:] ]
                   )
    elif args.moreclauses:
        # compute all sums of linerals in lins
        k = len(lins)
        subsets = itertools.chain.from_iterable(itertools.combinations(lins,r) for r in range(2,len(lins)+1))
        lins_sums = list({ sum(subset,lineral([], not(len(subset)%2))) for subset in subsets }-set(lins))
        return Xnf([ xClause([y+l1] + [l for l in lins if not(l == l1)]) for l1 in lins ] \
                   +[ xClause([ y+1, l+1 ]) for l in lins+lins_sums ]
                   )
    elif args.fewer_linerals:
        return Xnf([ xClause([ y, lins[0] ] + lins[1:]) ] \
                   +[ xClause([ y+1, lins[0]+1 ] + lins[1:]) ] \
                   +[ xClause([ y+1, l+1 ]) for l in lins ]
                   )
    else:
        return Xnf([ xClause([y+lins[0]] + lins[1:]) ] \
                   +[ xClause([ y+1, l+1 ]) for l in lins ]
                   )
    
    

def applySubs(subs,g):
    """Takes a list or set of substitutions subs and applies them to a polynomial g if this reduces the number of quadratic terms."""
    for sub in subs:
        new = sub.applyTo(g)
        if new.numTerms_nonLin() < g.numTerms_nonLin():
            if args.verbosity >= 40:
                print(f"Applied old sub! Reduced quad terms of g from {g.numTerms_nonLin()} to {new.numTerms_nonLin()}.")
            g = new
    return g


def applySubs_qrk(subs,g):
    """Same as applySubs, but uses the quadratic rank to decide whether to apply a substitution."""
    for sub in subs:
        if g.qrk() == 1: break;
        new = sub.applyTo(g)
        if new.qrk() < g.qrk():
            print("applied!")
            if args.verbosity >= 40:
                print(f"Applied old sub! Reduced qrk of g {g.qrk()} to {g.qrk()-1}.")
            g = new
    return g


def anf_to_2xnf(system):
    """Takes a list of polynomials and converts it to 2-XNF."""
    global subs
    global args
    global sbox_given
    global sbox_xnf_given
    global sbox_polys
    global sbox_xnf
    global sboxes
    global origNumIndets
    global indetDict
    assert(not(args.lfirst and args.sfirst))
    if args.lfirst:
        system.sort(key=Anf.numTerms_nonLin)
    if args.sfirst:
        system.sort(key=Anf.numTerms_nonLin)
        system.reverse()
    XNF = Xnf()
    if args.onlyterms:
        term_to_sub = {}
        already_converted = set()
    # insert S-Box XNFs if given
    if sbox_xnf_given:
        for sbox_indets in sboxes:
            XNF.extend(getSBoxXnf(sbox_indets))
    ### Main loop start
    # Loops over all polynomials in the system and converts them 1-by-1 to 2-XNF
    system_iter = iter(enumerate(system)) # to jump forward if sbox-polynomials are found
    for i, g in system_iter:
        if args.verbosity >= 15:
            print(f"anf_to_2xnf: Now processing Polynomial {i+1}/{len(system)}", end=("\r" if args.verbosity < 40 else "\n"))
        if args.verbosity >= 40 and g.deg() > 1:
            tmp = g.numTerms_nonLin()
            print(f"anf_to_2xnf: Terms of degree >1: {g.numTerms_nonLin()}, Indeterminates: {len(g.variables())}")
        ## substitute s-Box polynomials if possible
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
                            print(f"anf_to_2xnf: Found S-Box polynomials! Now jump {len(sbox_polys)} steps further.")
                        XNF.extend(getSBoxXnf(ind_candidates))
                        _ = [next(system_iter) for r in range(len(sbox_polys)-1)]
                        # also increase i in case those are the last polynomials in the system
                        # (to avoid assertion after loop throwing an error)
                        i += len(sbox_polys)-1
                        found_sth = True
                        break
            if found_sth:
                continue
        ## transform g to degree k
        # represents g=xi*f+h to eliminate as many terms as possible and then introduces
        # an additional variable y=f
        while g.deg() > args.k and not(args.k == 0):
            # searches ind such that as many terms of deg > args.k as possible are divisible by x[ind]
            badTerms = [t for t in g.support if t.deg() > args.k]
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
                print("anf_to_2xnf: Substituted:")
                print(f"anf_to_2xnf:     {xi}*({f}) + {h}")
                print(f"anf_to_2xnf:  ~> {Anf([[ind,new_indet]])} + {h}")
        ## onlyterms substitution
        # quickest substituion
        if args.onlyterms or (args.k != 2 and g.deg() > 2):
            if not(args.onlyterms):
                print("WARNING: Not yet implemented. Onlyterms substitution is applied.")
            lin_terms = [s for s in g.support if s.deg() < 2] # also contains Term()
            nonlin_terms = [s for s in g.support if s.deg() >= 2]
            for t in nonlin_terms:
                # first check already found substitutions
                # if onlyterms is set, then all substitutions are of the form x[i1]*...*x[is]
                if t in already_converted:
                    sub = term_to_sub[t]
                else:
                    sub = Sub([frozenset({i}) for i in t.indets])
                    already_converted.add(t)
                    term_to_sub[t] = sub
                    subs.add(sub)
                lin_terms.append(Term([sub.indet]))
            g = Anf(lin_terms)
        ## check special cases
        # check if g is already a lineral (e.g. if onlyterms loop was executed)
        if g.deg() == 1:
            XNF.append(lineral(g))
            continue
        # check if g is of the form g=l1*l2 (very fast!)
        factors = g.factor_quad()
        if [ f.deg() for f in factors ] == [1,1]:
            if args.verbosity >= 40:
                print("anf_to_2xnf: Polynomial is a product of two linear polynomials, so we directly transform it to 2-XNF.")
            XNF.append(xClause([lineral(factors[0]),lineral(factors[1])]))
            continue
        assert(g.deg() == 2)
        # check if g is of the form g=l1*l2+l3 (-> direct subsitution to 2-XNF)
        qrk = g.qrk()
        if qrk == 0:
            [(l1,l2)],l3 = optimal_repr(g)
            XNF.extend(special_poly_to_xnf(l3,[l1,l2]).getXClauses())
            continue
        # check if g is of the form g=l1*l2+l3*l4+1 (-> direct substitution to 2-XNF)
        if qrk == 1:
            [(l1,l2),(l3,l4)], l = optimal_repr(g,reduced=True)
            if l == 1:
                # 2-XNF representation of g is <(l1+1)(l3+1), (l2+1)(l4+1), (l1+l4+1)(l2+l3+1)>
                # (XNFs can be combined with 'and' operator)
                g_clauses = [xClause([lineral(l1+1),lineral(l3+1)]),
                             xClause([lineral(l2+1),lineral(l4+1)]),
                             xClause([lineral(l1+l4+1),lineral(l2+l3+1)])]
                XNF.extend(g_clauses)
                continue
        ## variable-optimal direct substituion of polynomial
        if args.linalg:
            applySubs_qrk(subs,g)
            s = findSubs_linalg(g)
            subs.update(s)
            if args.verbosity >= 40:
                print(f"anf_to_2xnf: Represented polynomial using {len(s)} additional variables."+" "*30)
            g = g + sum((sub.getAnf() for sub in s),Anf())
            # Now g is of the form l1*l2+l3
            [(l1,l2)],l3 = optimal_repr(g)
            XNF.extend(special_poly_to_xnf(l3,[l1,l2]).getXClauses())
            g = Anf()
        ## default search for 'good' substitution
        # applies previously found substitutions and tries to find good ones that eliminate
        # a large amount of terms
        while g.deg() == 2:
            if args.verbosity > 50:
                print("anf_to_2xnf: Current poly:",g)
            # check if g is of the form g=l1*l2+l3
            if g.qrk() == 0:
                [(l1,l2)],l3 = optimal_repr(g)
                XNF.extend(special_poly_to_xnf(l3,[l1,l2]).getXClauses())
                g = Anf()
                break
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
                print(f"anf_to_2xnf: Sub found! Remaining deg 2 terms: {g.numTerms_nonLin()}"+" "*30)
            if args.verbosity >= 60:
                print("anf_to_2xnf: Sub:",sub)
        if g != 0:
            XNF.append(lineral(g))
    ### Main loop end
    if len(system) > 0:
        # ensure that loop didn't terminate too early
        assert(i+1 == len(system))
    ## interreduces substitutions and returns the corresponding XNF
    if args.verbosity >= 15:
        print("anf_to_2xnf: Interreducing Substitutions."+" "*10)
    XNF.extend(subsToXnf())
    if args.cleanup:
        XNF.cleanup(origNumIndets)
    if args.cleanuphard:
        XNF.cleanup(0)
    if args.cleanupvariables:
        XNF.cleanupVarnames(0)
    return XNF


def subsToXnf():
    """Takes a list of substitutions, interreduces them, and returns the corresponding XNF."""
    global subs
    global args
    if args.onlyterms:
        xClauses = [ sub.getXnf() for sub in subs ]
        # return flattened list
        return Xnf([c for cList in xClauses for c in cList])
    F2 = getF2()
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
    N = F2(M).row_space()
    # pivot indices of N
    pivots = [ row.nonzero()[0][0] for row in N ]
    pivot_subs = [ subs_list[p] for p in pivots ]
    xClauses = []
    # add clauses from pivot subs
    for sub in pivot_subs:
        xClauses.extend(sub.getXnf().getXClauses())
    # add representations of non-pivot subs
    xClauses.extend([
        xClause(lineral(
            [sub.indet]+[pivot_subs[j].indet for j in N[:,i].nonzero()[0]],
            False
        ))
        for i,sub in enumerate(subs_list)
        if not(i in pivots)
    ])
    if args.verbosity >= 30:
        print(f"Substitutions reduced from {len(subs_list)} to {len(pivots)}.")
    return Xnf(xClauses)




# -------------------------------------------------------------------------------
# auxiliary functions

sBoxVarNum = 0
def getSBoxXnf(linerals):
    """Takes a list of indeterminates and returns the XNF of an S-Box (given in sbox_xnf) in these indeterminates."""
    global sbox_xnf
    global indetDict
    global sBoxVarNum
    # numAdd = number of additional indets in the SBox-XNF
    numAdd = sbox_xnf.numVars - len(linerals)
    numIndets_before = len(indetDict)-1
    numIndets_after = len(indetDict)+numAdd
    for i in range(numIndets_before+1,numIndets_after):
        sBoxVarNum += 1
        indetDict[f"[additional S-Box variable {sBoxVarNum}]"] = i
    # d : {1,...,number of indets in sbox_xnf} -> {linerals[0],...,linerals[s],new indeterminate 1,...,new indeterminate r}
    d = {**dict(zip(range(1,len(linerals)+1),linerals)),
         **dict(zip(range(len(linerals)+1,sbox_xnf.numVars+1),list(range(numIndets_before+1,numIndets_after))))}
    return [xClause([ lineral({ d[i] for i in l.lits },l.xnor) for l in c.xLits ]) for c in sbox_xnf]



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
    parser.add_argument("--sparse", action="store_true",
                        help="Reduces number of clauses in output (number of variables stays the same).")
    parser.add_argument("--moreclauses", action="store_true",
                        help="Enlarges number of clauses in output (number of variables stays the same).")
    parser.add_argument("--fewer-linerals", action="store_true",
                        help="Output contains fewer linerals within the XNF clauses.")
    parser.add_argument("--k","-k", type=int, default=2,
                        help="Set k s.t. the output XNF is in k-XNF.")
    args = parser.parse_args()
    # initialize 100 default indeterminates
    for i in range(1,100+1):
        indetDict["x["+str(i)+"]"] = i
else:
    parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter)
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
    parser.add_argument("-ap","--oanfpath",
                        help="Stores the output XNF as ANF format in given path. (product of linear polynomials)")
    parser.add_argument("--oxnf", action="store_true",
                        help="If the input path is of the form name.ext, then the output XNF is stored in the file name.xnf as XNF format.")
    parser.add_argument("--oxcnf", action="store_true",
                        help="If the input path is of the form name.ext, then the output XNF is stored in the file name.xcnf as DIMACS XCNF format (CNF clauses + XOR constraints).")
    parser.add_argument("--ocnf", action="store_true",
                        help="If the input path is of the form name.ext, then the output XNF is stored in the file name.cnf as DIMACS CNF format.")
    parser.add_argument("--blowupxcnf", action="store_true",
                        help="Adds equivalent clauses to the XCNF output to improve propagation in some cases.")
    parser.add_argument("--k","-k", type=int, default=2,
                        help="Set k s.t. the output XNF is in k-XNF (set k=0 for any XNF output).")
    parser.add_argument("-ll","--linerallength", type=int,
                        help="Set maximal length of linerals in output.")
    parser.add_argument("-cl","--cuttinglength", type=int, default=5,
                        help="Set cutting length of linerals for CNF output, i.e., the maximal length of a lineral that is converted to CNF without additional variables.")
    parser.add_argument("--sparse", action="store_true",
                        help="Reduces number of clauses in output (number of variables stays the same).")
    parser.add_argument("--fewer-linerals", action="store_true",
                        help="Output contains fewer linerals within the XNF clauses.")
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
    parser.add_argument("--optimal_subs","-os","--optimal_subs_quad","-osq", action="store_true", default=False,
                        help="Deprecated. Use --linalg instead.")
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
    parser.add_argument("--show", action="store_true", default=False,
                        help="Print output XNF to console.")
    args = parser.parse_args()

    if args.optimal_subs:
        raise Exception("--optimal_subs is deprecated. Use --linalg instead.")
    
    # guarantee that only one conversion type is used
    methods = [ args.onlyterms,
                args.linalg,
                args.maxsat,
                args.omt
               ]
    assert(methods.count(True) < 2)

        

    # check whether k != 1 (1-XNF is not NP-complete)
    assert(args.k == 0 or args.k >= 2)

    # ensure cutting length is >= 3
    assert(args.cuttinglength is None or args.cuttinglength >= 3)
    
    # ensure lineral length is >= 1
    assert(args.linerallength is None or args.linerallength >= 1)
    

    if args.seed is not None:
        random.seed(args.seed)
    
    if args.path == None:
        parser.print_usage(sys.stderr)
        quit()
    
    # checks for sBox input and tries to set default if exists
    sbox_polys_given = False
    if args.sBoxPolys is not None:
        sbox_indetDict = dict()
        sbox_indetDict["1"] = []
        sbox_polys = set(readPolySys(args.sBoxPolys,sbox_indetDict)[0])
        sbox_inds = sorted([ v for v in sbox_indetDict.values() if isinstance(v,int) ])
        sbox_polys_given = True
    
    sbox_xnf_given = False
    if args.sBoxXnf is not None:
        sbox_xnf = readXNF(args.sBoxXnf)
        sbox_xnf_given = True
    
    sbox_given = sbox_polys_given and sbox_xnf_given
    
        
    # now main body
    system, sboxes = readPolySys(args.path,indetDict)
    system = [ f for f in system if f != 0 ]
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

    # reduce linerals
    if args.linerallength is not None:
        if args.linerallength == 1:
            XNF = XNF.convertToCnf(args.cuttinglength)
        elif args.linerallength == 2:
            raise Exception("Not Yet Implemented.")
        else:
            XNF.cropLinerals(args.linerallength)


    if args.verbosity >= 5:
        print(f"ddv after conversion:                {XNF.ddv()}" + "".join([" " for i in range(70)]))
        print(f"number of variables after conversion: {XNF.getNumVars()}")
        print(f"number of clauses after conversion:   {XNF.getNumClauses()}")
    if args.verbosity >= 3:
        t1 = time.time()
        print(f"Running time:                         {str(t1-t0)[:5]} s")
        if len(system) > 0:
            print(f"effective number of variables:        {XNF.getNumVars()-XNF.ddv()[0]}")




    if (args.verbosity >= 100 and len(system) < 10 and len(XNF) < 60) or args.show: # probably just a toy example
        print("system:")
        print("  " + str(system))
        print("indeterminates:")
        print("  " + str(indetDict))
        print(XNF)
            
    if args.oxcnf:
        s = printIndets() + "\n" + XNF.asXcnf(args.blowupxcnf)
        path = args.path.rsplit(".",1)[0] + ".xcnf"
        D = open(path, "w")
        print(s, file=D)
        D.close()
        if args.verbosity > 0:
            print(f"Created {path}")
        
    if args.ocnf:
        s = printIndets() + "\n" + XNF.asCnf(args.cuttinglength)
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
    
    if args.oxcnfpath is not None:
        s = printIndets() + "\n" + XNF.asXcnf(args.blowupxcnf)
        D = open(args.oxcnfpath, "w")
        print(s, file=D)
        D.close()
        if args.verbosity > 0:
            print(f"Created {args.oxcnfpath}")
        
    if args.ocnfpath is not None:
        s = printIndets() + "\n" + XNF.asCnf(args.cuttinglength)
        D = open(args.ocnfpath, "w")
        print(s, file=D)
        D.close()
        if args.verbosity > 0:
            print(f"Created {args.ocnfpath}")
        
    if args.oxnfpath is not None:
        s = printIndets() + "\n" + XNF.asXnf()
        D = open(args.oxnfpath, "w")
        print(s, file=D)
        D.close()
        if args.verbosity > 0:
            print(f"Created {args.oxnfpath}")

    if args.oanfpath is not None:
        indet_str = ", ".join([l for l in indetDict.keys() if l != "1"])
        poly_strs = [ "*".join([f"({Anf(l)})" for l in c]) if len(c) > 1 else str(Anf(c[0]))
                      for c in XNF ]
        with open(args.oanfpath,"w") as f:
            print(indet_str,file=f)
            print("\n".join(poly_strs),file=f)

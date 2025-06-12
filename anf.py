#!/usr/bin/env python3

from collections import Counter # for efficiently counting elements in Anf.__init__
import sys
import itertools # for cartesian product of ranges
import random
import xnf
import numpy as np


def indNum(string):
    """Returns number of indeterminate name"""
    global indetDict
    return indetDict[string]

def indStr(num):
    """Returns string corresponding to indeterminate number"""
    global indetDict_rev
    return indetDict_rev[num]


F2 = None
def getF2():
    global F2
    if F2 is None:
        # ignore TBB outdated version warning
        import galois
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            F2 = galois.GF(2)
    return F2


# dictionary that stores the indeterminate names, e.g. indetDict["x"] == 1
# only positive integers allowed for indeterminate numbers
indetDict = dict()
indetDict_rev = dict()
indetDict["1"] = 0
indetDict_rev[0] = "1"

class Anf:
    # support is a set of terms
    support = frozenset()
    ntd2 = -1 # number of degree 2 terms
    my_qrk = None
    def __init__(self,support = []):
        if isinstance(support,Term):
            self.support = frozenset({support})
            return
        if isinstance(support,Anf):
            self.support = support.support
            ntd2 = Anf.ntd2
            return
        if isinstance(support,str):
            support = support.replace(" ","").replace("\t","").replace("\n","")
            self.support = Anf([[indetDict[x] for x in t.split("*")] for t in support.split("+") if not(t == "0")]).support
            return
        if isinstance(support,frozenset) and all(isinstance(t,Term) for t in support):
            self.support = support
            return
        if isinstance(support,set) and all(isinstance(t,Term) for t in support):
            self.support = frozenset(support)
            return
        if isinstance(support,xnf.lineral):
            l = support
            supp = {Term(i) for i in l.lits}
            if l.xnor: supp.add(Term())
            self.support = supp
            return
        if support == 1:
            self.support = frozenset({Term()})
            return
        if support == [] or support == frozenset() or support == 0:
            self.support = frozenset()
            return
        assert(not(isinstance(support,int) and not(support in [0,1])))
        # first make support a homogeneous list
        supp_tmp = [Term(t) for t in support]
        c = Counter(supp_tmp)
        self.support = frozenset({t for t in supp_tmp if c[t] % 2})
    def __str__(self):
        if self == 0:
            return("0")
        if self == 1:
            return("1")
        else:
            return " + ".join([str(t) for t in sorted(self.support,reverse=True)])
    def print(self,termorder=None):
        if termorder == None:
            return str(self)
        termorder = parseTO([self],termorder)
        if self == 0:
            return("0")
        if self == 1:
            return("1")
        else:
            supp = sorted(list(self.support),key=termorder)
            return " + ".join([str(t) for t in reversed(supp)])
    def __repr__(self):
        return str(self)
    def __eq__(self,other):
        if other == 0:
            return len(self.support) == 0
        elif other == 1:
            return self.support == frozenset({Term()})
        if isinstance(other,Anf):
            return self.support == other.support
        print("WARNING: Compared ANF to something that is not ANF.")
        return False
    def __len__(self):
        return self.numTerms()
    def __hash__(self):
        return hash(self.support)
    def variables(self) -> set:
        """Returns a set containing all variables (ints) occurring in self."""
        return set().union(*[t.indets for t in self.support])
    def deg(self) -> int:
        """Returns the degree of the polynomial."""
        return max({t.deg() for t in self.support},default=-1)
    def LT(self,TO = None):
        """Returns the DegLex-leading term of self."""
        TO = parseTO(self,TO)
        return max(self.support,key=TO)
    def numTerms(self) -> int:
        """Returns the number of terms in the support."""
        return len(self.support)
    def numTerms_nonLin(self) -> int:
        """Returns the number of terms of degree 2 in the support."""
        if self.ntd2 == -1:
            self.ntd2 = len([t for t in self.support if t.deg() > 1])
        return self.ntd2
    def __add__(self,other):
        """Returns a polynomial that is the sum of the two given ones."""
        if isinstance(other,int) and other == 1:
            return self+Anf(1)
        if isinstance(other,int) and other == 0:
            return self+Anf(0)
        if isinstance(other,str) and other in ["0","1"]:
            return self+int(other)
        if isinstance(other,Anf):
            return Anf(self.support^other.support)
        if isinstance(other,Term):
            return self+Anf(other)
        raise Exception(f"Cannot add ANF and {type(other)}.")
    def __mul__(self,other):
        """Returns a product that is the sum of the two given ones."""
        if other == 1:
            return self
        if other == 0:
            return Anf()
        if isinstance(other,Term):
            other = Anf(other)
        if isinstance(other,str) and other in ["0","1"]:
            return self*int(other)
        if isinstance(other,Anf):
            return Anf([s*t for s in self.support for t in other.support])
        raise Exception(f"Cannot multiply ANF and {type(other)}.")
    def __truediv__(self,other):
        """Returns self/other if self is divisible by other."""
        rem = f.copy()
        g = Anf()
        t = other.LT()
        while rem != Anf():
            if rem.deg() == 1:
                if g.LT() == other.LT():
                    g += 1
            g += Anf(rem.LT()/other.LT())
            rem += Anf(rem.LT()/other.LT())*other
        return g
    def copy(self):
        return Anf([Term(t.indets.copy()) for t in self.support])
    def NR(self,other,TO=None):
        """Returns the NR of self and other (other is also a polynomial)."""
        if other == 1:
            return Anf(0)
        elif other == 0:
            return self
        TO = parseTO([self,other],TO)
        t = other.LT(TO)
        rem = Anf(self.getSupport())
        while rem != Anf(0) and rem.LT(TO).isDivisible(t):
            rem += Anf(rem.LT(TO)/t)*other
            t = other.LT(TO)
        return rem
    def getSupport(self):
        """Returns a copy of the support."""
        return self.support.copy()
    def getHomogComp(self,d):
        """Returns the homogeneous component of degree d."""
        assert(isinstance(d,int))
        return Anf({t for t in self.support if t.deg() == d})
    def substIndets(self,selfInds,otherInds):
        """Returns a copy of self where the indeterminates were substituted by the ones in the list indets."""
        if len(selfInds) != len(otherInds):
            print("selfInds:",selfInds)
            print("otherInds:",otherInds)
        assert(len(selfInds) == len(otherInds))
        d = dict(zip(selfInds,otherInds))
        return Anf([ Term([d[i] for i in t.getIndets()]) for t in self.getSupport() ])
    def evaluate(self,sol):
        """Evaluates self at sol where sol is a tuple with entries True,False such that sol[i] is substituted for x[i] (sol[0] is None)."""
        return sum([t.evaluate(sol) for t in self.support])%2
    def deriv(self,i):
        """Returns the derivative of self in the indeterminate i."""
        supp = set()
        for t in self.support:
            if i in t.indets:
                supp.add(Term(t.indets-{i}))
        return Anf(supp)
    def gradient(self):
        """Returns a tuple (None,deriv(self,x1),deriv(self,x2),...) (gradient(self)[i] should be the deriv(f,i))"""
        v = sorted(list(self.variables()))
        return {x: self.deriv(x) for x in v}
    def factor_quad(self):
        """Returns list [l1,l2] s.t. self == l1*l2. Returns [1,self] if no linear factors exist."""
        v = self.variables()
        n = len(v)
        minTerm = min(self.support-{Term([])},key=len)
        # either c0 is a root and c1 not or reversed
        c0 = {i: 0 for i in v}
        c1 = {i: int(i in minTerm.indets) for i in v}
        Df = self.gradient()
        coeffs = {i: (Df[i].evaluate(c0)+Df[i].evaluate(c1))%2 for i in v}
        l1 = sum([ Anf([[i]])*coeffs[i] for i in v ],Anf())
        l2 = self.NR(l1)
        l2_ = self.NR(l1+Anf(1))
        if l2 == Anf(0):
            output = [l1,l2_,l1+l2_+Anf(1)]
        elif l2_ == Anf(0):
            output = [l1+Anf(1),l2,l1+l2]
        else:
            output = [Anf(1),self]
        if len(output) > 2:
            output = sorted(output,key=len)[:2]
        return output
    def randomQuad(n,r=0):
        """Returns a random quadratic polynomial in n indeterminates that is the sum of r products of two linear polynomials (but may also be a sum of fewer factors)."""
        """If r is 0 then only a random quadratic non-zero polynomial is returned."""
        if len(indetDict) < n+1:
            for i in range(1,n+1):
                name = f"x[{i}]"
                indetDict[name] = i
                indetDict_rev[i] = name
        if r == 0:
            terms = [ [] ]+[ [i,j] for i in range(1,n+1) for j in range(i,n+1) ]
            return Anf(random.sample(terms,random.randint(1,len(terms))))
        else:
            return sum([Anf([ [i] for i in random.sample(list(range(1,n+1))+[[]],random.randint(1,n)) ])
                        *Anf([ [i] for i in random.sample(list(range(1,n+1))+[[]],random.randint(1,n)) ])
                        for j in range(r)],Anf())
    def randomQuadSys(n,s,sat=False,sol=None):
        """Returns a system of s random quadratic polynomials in n indeterminates."""
        """If sat == True, then guarantees that the system is solvable."""
        if len(indetDict) < n+1:
            for i in range(1,n+1):
                name = f"x[{i}]"
                indetDict[name] = i
                indetDict_rev[i] = name
        # inefficient (set of terms is computed for each polynomial separately), but easy to debug
        terms = [ [] ]+[ [i,j] for i in range(1,n+1) for j in range(i,n+1) ]
        if not(sat):
            return [ Anf(random.sample(terms,random.randint(1,len(terms)))) for i in range(s) ]
        if sol is None:
            sol = tuple([None])+tuple(random.getrandbits(1) for i in range(n))
        system = set()
        return [ p if p.evaluate(sol) == 0 else p+1 \
                 for p in [ Anf(random.sample(terms,random.randint(1,len(terms)))) for i in range(s)]]
    def random(n,deg=0):
        """Returns a random polynomial in n indeterminates."""
        if deg == 0:
            deg = n
        if len(indetDict) < n+1:
            for i in range(1,n+1):
                name = f"x[{i}]"
                indetDict[name] = i
                indetDict_rev[i] = name
        # first attempt: compute list of all terms and choose a random subset
        from itertools import chain, combinations
        allTerms = list(chain.from_iterable(combinations(range(1,n+1),r) for r in range(deg+1)))
        supp = random.sample(allTerms,random.randint(1,len(allTerms)))
        return Anf(supp)
    def randomSys(n,s,deg=0,sat=False,sol=None):
        """Returns a system of s random polynomials in n indeterminates."""
        """If sat == True, then guarantees that the system is solvable."""
        if deg == 0:
            deg = n
        if len(indetDict) < n+1:
            for i in range(1,n+1):
                name = f"x[{i}]"
                indetDict[name] = i
                indetDict_rev[i] = name
        # inefficient (set of terms is computed for each polynomial separately), but easy to debug
        if not(sat):
            return [Anf.random(n,deg) for i in range(s)]
        if sol is None:
            sol = tuple([None])+tuple(random.getrandbits(1) for i in range(n))
        system = set()
        while len(system)<s:
            p = Anf.random(n,deg)
            if p.evaluate(sol) == 0:
                system.add(p)
            else:
                system.add(p+1)
        return list(system)
    def QCM(self,v=None):
        """Returns the Quadratic Coefficient Matrix of self."""
        """Output is nxn matrix (a_ij) with a_ii = 0 and a_ij = 1 iff x_ix_j in supp(f)."""
        if v is None:
            v = list(self.variables())
        n = len(v)
        F2 = getF2()
        return F2([ [ (v1 != v2 and Term([v1,v2]) in self.support) for v1 in v ] for v2 in v ])
    def qrk(self):
        """Returns the quadratic rank of self"""
        """qrk(0)=qrk(1)=qrk(l)=0 for linear polynomials l"""
        """If deg(f)=2, qrk(f) is the minimal s s.t. f=l11*l12 +...+ l(s+1)1*l(s+1)2 + l for linear polynomials lij and l"""
        assert(self.deg() == 2)
        if self in [0,1]:
            return 0
        if self.my_qrk is None:
            self.my_qrk = int(max([0, np.linalg.matrix_rank(self.QCM())//2-1]))
        return self.my_qrk
        
        
        
        




class Term:
    indets=frozenset()
    hash_val=0
    def __init__(self,indets=frozenset()):
        # Term(0) is not allowed
        assert(not(isinstance(indets,int) and indets == 0))
        if isinstance(indets,Term):
            self.indets = indets.indets
            self.hash_val = indets.hash_val
            return
        if isinstance(indets,int):
            self.indets = frozenset({indets})
            return
        if len(indets) == 0 or indets == [0]:
            self.indets = frozenset()
            return
        assert(not(0 in indets))
        self.indets=frozenset(indets)
    def __str__(self):
        if self.indets == set():
            return "1"
        return "*".join([indStr(ind) for ind in sorted(list(self.indets))])
    def __repr__(self):
        return str(self)
    def deg(self):
        """Returns the polynomial degree of self."""
        return len(self.indets)
    def __len__(self):
        return self.deg()
    def __mul__(self,other):
        """Returns the product of the two given terms."""
        if isinstance(other,Anf):
            return other*Anf(self)
        return Term(self.indets|other.indets)
    def __eq__(self,other):
        """Checks whether two terms are equal (semantically)."""
        if other == 1:
            return self.indets == set()
        else:
            return self.indets == other.indets
    def __hash__(self):
        if self.hash_val == 0:
            self.hash_val = hash(self.indets)
        return self.hash_val
    def __lt__(self,other):
        """Compares two terms with the term ordering DegLex where 1 > 2 > ..."""
        if self == other:
            return False
        if self.deg() == other.deg():
            a = self.indets-other.indets
            b = other.indets-self.indets
            return min(a) > min(b)
        else:
            return self.deg() < other.deg()
    def __le__(self,other):
        """Compares two terms with the term ordering DegLex where 1 > 2 > ..."""
        return self == other or self < other
    def __gt__(self,other):
        """Compares two terms with the term ordering DegLex where 1 > 2 > ..."""
        return other < self
    def __ge__(self,other):
        """Compares two terms with the term ordering DegLex where 1 > 2 > ..."""
        return other <= self
    def __add__(self,other):
        return Anf(self)+Anf(other)
    def getIndets(self):
        """Returns a copy of the set of indeterminates."""
        return set(self.indets)
    def evaluate(self,sol):
        """Evaluates self at sol where sol is a dictionary with sol[x] in {True,False}."""
        return int(not(False in {bool(sol[i]) for i in self.indets}))
    def isDivisible(self,other):
        """Checks whether self is divisible by other."""
        return other.indets.issubset(self.indets)
    def __truediv__(self,other):
        if self.isDivisible(other):
            return Term(self.indets-other.indets)
        else:
            raise Exception("Division not possible.")
    def log(self,n):
        """Returns a list [a1,...,an] s.t. self = x1^a1*...*xn^an."""
        return [int(i+1 in self.indets) for i in range(n)]


def optimal_repr(anf,verbosity=0,reduced=False):
    """
    Input: ANF anf
    Output: Tuple ( [ (l1,l2), (l3,l4), ..., (l(s-1),ls) ], l ) s.t. f = l+l1*l2+l3*l4+...+l(s-1)*ls, l1,...,ls have no constant coefficient, and 1,l1,...,ls are linearly independent.
    If reduced is set to True then l is either constant or 1,l,l1,...,ls are linearly independent (but may have non-constant coefficient).
    """
    assert(anf.deg() <= 2)
    if anf.deg() < 2:
        return [ [], anf ]
    inds = list(anf.variables())
    M = anf.QCM(inds)
    N, T = to_blockdiag(M)
    T = np.linalg.inv(T)
    assert((mat_prod([T,N,T.transpose()]) == M).all())
    lins = [ Anf([ [ind] for i,ind in enumerate(inds) if col[i] ]) for j,col in enumerate(T.transpose()) ]
    s = anf.qrk()
    quad_part = [ (lins[2*i],lins[2*i+1]) for i in range(s+1) ]
    lin_part = anf + sum([ l[0]*l[1] for l in quad_part ],Anf())
    assert(lin_part.deg() < 2)
    assert(sum([ l1*l2 for l1,l2 in quad_part ], Anf()) + lin_part == anf)
    if reduced:
        relations = linear_relations((Anf(1), lin_part)+sum(quad_part,tuple()))
        if len(relations) > 0:
            # TODO: which relation is the best one?
            c = relations[0][2:]
            quad_part = [ (l1+Anf(c[2*i+1]), l2+Anf(c[2*i])) for i,(l1,l2) in enumerate(quad_part) ]
            lin_part = Anf(relations[0][0])+Anf(sum([ c[2*i]*c[2*i+1] for i in range(s+1) ])%2)
            assert(sum([ l1*l2 for l1,l2 in quad_part ], Anf()) + lin_part == anf)
    assert(lin_part.deg() < 2)
    return ( quad_part, lin_part )


def optimal_repr_old(anf,verbosity=0,reduced=False):
    """
    Same as optimal_repr, but old implementation.
    """
    assert(anf.deg() <= 2)
    quad_part = anf.getHomogComp(2)
    lin_part = anf + quad_part
    # write quad_part as x[1]*l1+x[2]*l2+...+x[n]*ln
    # curr_repr is tuple [[(l1,l2),(l3,l4),...], l] s.t. anf = l + l1*l2+l3*l4+...
    curr_repr = [ [], lin_part ]
    remainder = quad_part
    for x in quad_part.variables():
        vars_rem = remainder.variables()
        if not(x in vars_rem):
            continue
        l = sum([ Anf(Term([y])) for y in vars_rem if Term([x,y]) in remainder.support ],Anf())
        curr_repr[0].append( ( Anf(Term([x])), l) )
        remainder = remainder + Anf(Term([x]))*l
    iteration = 0
    while True:
        if verbosity >= 40:
            iteration += 1
            print("optimal_repr: iteration Nr.",iteration,end="\r")
        relations = linear_relations(sum(curr_repr[0],tuple())+tuple([Anf(1)]))
        if relations == []:
            break
        chosen_rel = relations[0]
        index = next(i for i,c in enumerate(chosen_rel) if c == 1)
        ls1,ls2 = curr_repr[0][index//2] if index%2 == 0 else reversed(curr_repr[0][index//2])
        cs2 = chosen_rel[index+1 if index%2 == 0 else index-1]
        # (sum) i=1 to s-1 ci1*ci2
        summe = sum(ci1*ci2 for ci1,ci2 in [ chosen_rel[2*i:2*i+2] for i in range(len(chosen_rel)//2) if i != index//2])
        new_repr = [ [], curr_repr[1]+ls2*( (chosen_rel[-1] + cs2 + summe)%2 ) ]
        for i, (li1,li2) in enumerate(curr_repr[0]):
            if {li1,li2} == {ls1,ls2}:
                continue
            eq_prod = next( ((lj1,lj2) for lj1,lj2 in new_repr[0] if {li1,li2} == {lj1,lj2}) , None)
            if eq_prod is not None:
                new_repr[0].remove(eq_prod)
                continue
            ci1,ci2 = chosen_rel[2*i:2*i+2]
            new_tup = (li1+ls2*ci2, li2+ls2*ci1)
            if not(0 in new_tup):
                new_repr[0].append(new_tup)
        curr_repr = new_repr
    s = len(curr_repr[0])
    # now l1,l2,...,ls are linearly independent and don't have a constant coefficient
    # check whether l,l1,...,ls is linearly independent and whether 1 is in <l,l1,...,ls>
    if reduced:
        c1 = linear_relations(tuple([Anf(1)])+tuple([curr_repr[1]])+sum(curr_repr[0],tuple()))
        if c1 != []:
            c = c1[0][2:]
            new_repr = [ [], Anf() ]
            new_repr[1] = Anf(c1[0][0])+Anf(sum([ c[2*i]*c[2*i+1] for i in range(s) ])%2)
            for i,(l1,l2) in enumerate(curr_repr[0]):
                # m1 = l1 + (coefficient of l2 in c) and vice versa
                m1 = l1 + Anf(c[2*i+1])
                m2 = l2 + Anf(c[2*i])
                new_repr[0].append( (m1,m2) )
            curr_repr = new_repr
    return curr_repr


def linear_relations(anfs):
    """
    Takes a list of ANFs and returns a basis of its linear relations, i.e., all
    c s.t. np.dot(anfs,c) == 0.
    """
    assert(all(isinstance(p,Anf) for p in anfs))
    F2 = getF2()
    if anfs == []:
        return []
    basis = set()
    for s in anfs:
        basis = basis | set(s.support) # union
    basis = list(basis)
    # zero matrix of size len(basis) >< len(anfs)
    M = F2.Zeros((len(basis),len(anfs)))
    # write polynomials in matrix
    for j,anf in enumerate(anfs):
        for t in anf.support:
            M[basis.index(t)][j] = 1
    M_red = M.row_space()
    pivots = [ next((i for i,c in enumerate(row) if c),-1) for row in M_red ]
    out = [ [0]*len(anfs) for i in range(len(anfs)) ]
    for i in range(len(anfs)):
        if i in pivots:
            continue
        out[i][i] = 1
        for j,c in enumerate(M_red[:,i]):
            if c:
                out[i][pivots[j]] = 1
    return [ l for l in out if 1 in l ]


        

def interreduced_lin(anfs,termorder = None, linsfirst = False):
    """
    Takes a list of anfs and interreduces them using linear algebra.
    Returns a tuple (LIST,MAT) where LIST is the list of reduced polynomials and MAT is a matrix such that MAT*input = output.
    Set linsfirst to True if the polynomials should be primarily interreduced by their linear parts.
    """
    assert(all(isinstance(p,Anf) for p in anfs))
    F2 = getF2()
    if anfs == []:
        return False, []
    termorder = parseTO(anfs,termorder)
    basis = set()
    for s in anfs:
        basis = basis | set(s.support) # union
    if linsfirst:
        basis = sorted([t for t in basis if t.deg() <= 1],key=termorder,reverse = True) \
            + sorted([t for t in basis if t.deg() > 1],key=termorder,reverse = True)
    else:
        basis = sorted(list(basis),key=termorder,reverse=True)
    # zero matrix of size len(anfs) >< len(basis)
    M = F2.Zeros((len(anfs),len(basis)))
    # write polynomials in matrix
    for j,anf in enumerate(anfs):
        for t in anf.support:
            M[j][basis.index(t)] = 1
    M_red = M.row_space()
    # construct transformation matrix
    ## C = [ M^tr | M_red^tr ]
    C = np.concatenate((M.transpose(),M_red.transpose()),axis=1)
    C = C.row_space()
    ## pivot columns of C
    pivots = [ next(j for j,c in enumerate(row) if c == 1) for row in C ]
    C_rows = [r for r in C]
    C_rows.reverse()
    X_rows = []
    zero_row = F2.Zeros(M_red.shape[0])
    for j in range(len(anfs)):
        if j in pivots:
            X_rows.append(C_rows.pop()[len(anfs):])
        else:
            X_rows.append(zero_row)
    X = F2(X_rows).transpose()
    # compute polynomials (more efficient than reading from M_red)
    newAnfs = applyMatToAnfs(X,anfs)
    return newAnfs,X


def TOfromMat(M):
    """Takes a term ordering matrix M and returns a key function corresponding to it."""
    M = np.matrix(M)
    def leq_lex(v1,v2):
        if np.array_equal(v1,v2):
            return 0
        # returns 1 if first element v1 >= v2 and -1 otherwise
        return next( (np.sign(v1[i]-v2[i]) for i in range(len(v1)) if v1[i] != v2[i]), 1 )
    def mat_mul(M,V):
        return np.dot(M,np.matrix(V).transpose())
    def leq(t1,t2):
        n = M.shape[1]
        if isinstance(t1,Anf): # assuming that t1 only has one term
            t1 = t1.LT()
        if isinstance(t2,Anf):
            t2 = t2.LT()
        return leq_lex(mat_mul(M,t1.log(n)),mat_mul(M,t2.log(n)))
    import functools
    return functools.cmp_to_key(leq)


def DegRevLex(n):
    L = [ [1 for i in range(n)] ]
    L.extend([ [0 for i in range(n)] for j in range(n-1) ])
    for i in range(1,n):
        L[i][n-i] = -1
    return TOfromMat(L)


def DegLex(n):
    L = [ [1 for i in range(n)] ]
    L.extend([ [0 for i in range(n)] for j in range(n-1) ])
    for i in range(1,n):
        L[i][i-1] = 1
    return TOfromMat(L)


def Lex(order):
    if isinstance(order,int):
        order = list(range(1,order+1))
    n = len(order)
    L = [ [0 for i in range(n)] for j in range(n) ]
    for i in range(n):
        L[order.index(i+1)][i] = 1
    return TOfromMat(L)


def Xel(n):
    L = [ [0 for i in range(n)] for j in range(n) ]
    for i in range(n):
        L[i][n-i-1] = 1
    return TOfromMat(L)


def Elim(inds,n):
    """Returns an elimination TO matrix of size for indeterminates in ind."""
    return TOfromWeights([(1 if i+1 in inds else 0) for i in range(n)])


def TOfromWeights(weights):
    """Takes a list of weights (>= 0) and returns a term ordering function."""
    assert(all(w >= 0 for w in weights))
    assert(any(w > 0 for w in weights))
    n = len(weights)
    L = [ weights ]
    firstZero = next((i for i,w in enumerate(weights) if w == 0),None)
    firstNonZero = next((i for i,w in enumerate(weights) if w > 0),None)
    if firstZero is None:
        L.extend([ [0 for i in range(n)] for j in range(n-1) ])
        for i in range(1,n):
            L[i][n-i] = -1
    else:
        colWithoutMinus1 = max(firstZero,firstNonZero)
        L.append([ 0 if w > 0 else 1 for i,w in enumerate(weights) ])
        L.extend([ [0 for i in range(n)] for j in range(n-2) ])
        for i in range(1,n-colWithoutMinus1):
            L[i+1][n-i] = -1
        for i in range(n-colWithoutMinus1,n-1):
            L[i+1][n-i-1] = -1
    return TOfromMat(L)



def parseTO(anfs,TO=None):
    """
    Takes a list of anfs and TO, which may be a term order, a string or None.
    E.g. TO can also be "lex", then the corresponding term order for the ring of anfs will be returned.
    """
    if isinstance(anfs,Anf):
        anfs = [anfs]
    # make anfs homogeneous
    anfs = [Anf(f) for f in anfs]
    if callable(TO): # TO probably is already a term order
        return TO
    if isinstance(TO,str):
        TO = TO.lower()
        n = max({max(f.variables(),default=0) for f in anfs})
        assert(TO in ["lex","deglex","degrevlex","xel"])
        if TO == "lex":
            return Lex(n)
        elif TO == "deglex":
            return DegLex(n)
        elif TO == "xel":
            return Xel(n)
        elif TO == "degrevlex":
            return DegRevLex(n)
    if TO is None:
        n = max({max(f.variables(),default=0) for f in anfs})
        return DegRevLex(n)



def applyMatToAnfs(A,P):
    """Computes A*P^tr. A is k >< s, P has length s."""
    return [ sum([ p*int(c) for p,c in zip(P,row)], Anf()) for row in A ]




def groebnerFanLin(anfs):
    """
    Computes the Grobner Fan of the linear ideal <anfs>.
    Assumes that all elements of anfs are sums of indeterminates.
    """
    import itertools
    F2 = getF2()
    assert(all(anf.deg() == 1 for anf in anfs))
    assert(all((Term() not in anf.support) for anf in anfs))
    n = max([max(anf.variables()) for anf in anfs])
    s = len(anfs)
    # zero matrix of size s >< len(basis)
    A = F2.Zeros((s,n))
    # write polynomials in matrix
    for row,anf in enumerate(anfs):
        for col in anf.variables():
            A[row][col-1] = 1
    full_inds = itertools.combinations(range(n),s)
    # list of all indices s.t. corresponding submatrix of A is non-singular
    M = [ i for i in full_inds if np.linalg.det(A[np.ix_(range(s),i)]) == 1 ]
    return [ ({ j+1 for j in i },applyMatToAnfs(np.linalg.inv(A[np.ix_(range(s),i)]),anfs)) for i in M ]


def linPolyToXLit(f):
    """Takes a linear polynomial f and returns an lineral l with Z(f)=S(l)."""
    """(obsolete: integrated in constructor of xnf.lineral)"""
    return xnf.lineral(f)

    
def readPolySys(path,indetDict,indetDict_rev):
    """
    Input: path to anf file, indetDict and indetDict_rev (to be filled)
    Ouptut: system of Anfs from file in given path
    For the structure of the input file see documentation.
    """
    import re
    f = open(path,"r")
    L = f.readlines()
    f.close()
    # delete first line if it contains the field
    if L[0].replace("\n","").replace(" ","") in ["F2","GF(2)"]:
        del L[0]
    # create indeterminate list
    indets = L[0].replace("\n","").split(", ")
    # delete spaces and tabs in single indeterminates
    indets = [i.replace(" ","").replace("\t","") for i in indets]
    # remove empty indeterminates
    indets = [i for i in indets if not(i == "")]
    indetDict.update(dict(zip(indets,range(1,len(indets)+1))))
    indetDict_rev.update(dict(zip(range(1,len(indets)+1),indets)))
    # if polyStr is "# S-Box x[1] x[2] x[3] x[4]", then the S-Box XNF with the indeterminates x[1],...,x[4] is inserted here
    sboxes = []
    for polyStr in [ l for l in L[1:] if len(l) > 0 and l.lower().startswith("# s-box ") ]:
        linerals = polyStr[8:].removesuffix("\n").split(", ")
        linerals = [l.replace(" ","").replace("\t","") for l in linerals]
        # linerals that are only indeterminates are added as integer (for the sake of efficiency), other ones as linerals
        sboxes.append([ xnf.lineral(Anf(f)+1) if "+" in f else indNum(f) for f in linerals ])
    L = [ l for l in L[1:] if not(l.startswith("#")) ]
    # remove spaces, tabs, newlines and exponents from polynomial strings
    for i,l in enumerate(L):
        L[i] = l.replace(" ","").replace("\t","").replace("\n","")
        L[i] = re.sub(r"\^[0-9]+","",L[i])
    system = []
    for polyStr in [ l for l in L if len(l) > 0 ]:
        try:
            system.append(Anf([[indetDict[x] for x in t.split("*")] for t in polyStr.split("+") if not(t == "0")]))
        except KeyError as e: # throw error if an unknown indeterminate is used
            raise NameError("Unknown indeterminate name: " + str(e)) from None
    return system, sboxes


def printIndets():
    """Returns a string containing the indeterminates as lines of the form \'c x[1] 1\'."""
    global indetDict
    s = "c Assignments of the variables:"
    for key, value in indetDict.items():
        if key != "1":
            s += "\nc " + key + " " + str(value)
    return s


def printPolySys(sys,path,termorder=None):
    """
    Input: system sys of Anfs, path to output
    Prints given system to given path
    """
    indets = sorted(list({Term(v) for p in sys for v in p.variables()}),reverse=True)
    if termorder is not None:
        termorder = parseTO(sys,termorder)
        indets.sort(key=termorder,reverse=True)
    s = ", ".join([str(ind) for ind in indets]) + "\n"
    s += "\n".join([s.print(termorder) for s in sys])
    with open(path,"w") as f:
        print(s,file=f)



# -------------------------------------------------------------------------------
# linear algebra stuff for simultaneous row and column transformations

def to_blockdiag(M):
    r"""
    Converts a symmetric Boolean matrix to a block diagonal matrix using elementary
    row and column operations.

    Input:
        M (matrix): Symmetric matrix over galois.GF(2) of size n.

    Output:
        N (matrix): Block diagonal matrix of size n with blocks of the form
                    / 0 1 \
                    \ 1 0 /
                    or zero.
        T (matrix): Square matrix of size n s.t. N = T*M*T^(tr)
    """
    F2 = getF2()
    M = F2(M) # copy M
    assert((M == M.transpose()).all())
    n = len(M)
    # Transformation matrix
    T = F2.Identity(n)
    curr_rowcol = 0
    while True:
        if (M[curr_rowcol:,curr_rowcol:] == 0).all():
            break;
        # Search for nonzero entry in bottom right quater of matrix
        L = nonzero_positions_in_row(M,curr_rowcol)
        if L:
            nz_row = L[0]
        else:
            nz_row,nz_col = next((r,c) for r,c in zip(M.nonzero()[0],M.nonzero()[1]) if r >= curr_rowcol)
            # Swap rows and columns such that curr_rowcol has a one in it
            swap_columns(M,curr_rowcol,nz_col)
            swap_rows(M,curr_rowcol,nz_col)
            swap_rows(T,curr_rowcol,nz_col)
        # Swap rows and columns such that curr_rowcol+1 has a one in its entry
        swap_columns(M,curr_rowcol+1,nz_row)
        swap_rows(M,curr_rowcol+1,nz_row)
        swap_rows(T,curr_rowcol+1,nz_row)
        # Cancel out other ones in cur_rowcol
        for one_row in nonzero_positions_in_row(M,curr_rowcol):
            if one_row == curr_rowcol+1:
                continue
            add_row_to_row(M,one_row,curr_rowcol+1)
            add_col_to_col(M,one_row,curr_rowcol+1)
            add_row_to_row(T,one_row,curr_rowcol+1)
        for one_row in nonzero_positions_in_row(M,curr_rowcol+1):
            if one_row == curr_rowcol:
                continue
            add_row_to_row(M,one_row,curr_rowcol)
            add_col_to_col(M,one_row,curr_rowcol)
            add_row_to_row(T,one_row,curr_rowcol)
        curr_rowcol += 2
    return M, T

def nonzero_positions(M):
    return list(zip(M.nonzero()[0],M.nonzero()[1]))

def nonzero_positions_in_row(M,i):
    return [ y for x,y in nonzero_positions(M) if x == i ]

# swap columns i and j of M
def swap_columns(M,i,j):
    M[:, [i,j]] = M[:, [j,i]]

# swap rows i and j of M
def swap_rows(M,i,j):
    M[[i,j]] = M[[j,i]]

# add j-th row to i-th row
def add_row_to_row(M,i,j):
    M[i] = M[i]+M[j]

# add j-th column to i-th column
def add_col_to_col(M,i,j):
    M[:, i] = M[:, i]+M[:, j]

# mat_product of list of matrices
def mat_prod(L):
    global F2
    if len(L) == 1:
        return L[0]
    return F2.dot(L[0],mat_prod(L[1:]))



# -------------------------------------------------------------------------------
import argparse
if __name__!='__main__':
    class dummy:
        def __init__(self):
            return
    args = dummy()
    args.verbosity = 0
else:
    parser = argparse.ArgumentParser()
    parser.add_argument("path",nargs='?',default=None,
                        help="Path of input. Input file has the following structure: The first line contains all indeterminates separated with a comma and AT LEAST ONE SPACE BAR (important for reading in indeterminates of the form \'x[1,1]\'), the other lines contain each exactly one polynomial. Polynomials sums (\'+\') of terms and a term is a product (\'*\') of indeterminates or simply \'1\'. Spaces and tabs are ignored and no indeterminate can be called 1. Comment lines are marked with a # at the beginning.")
    parser.add_argument("--random","-r", nargs=4, metavar=("num_vars","num_polys","max_deg","sat"),default=None,
                        help="Creates a random system of num_polys polynomials in num_vars variables. If sat==True, then the system is guaranteed to be satisfiable.")
    parser.add_argument("--randomquad","-rq", nargs=3, metavar=("num_vars","num_polys","sat"),default=None,
                        help="Creates a random system of num_polys quadratic polynomials in num_vars variables. If sat==True, then the system is guaranteed to be satisfiable.")
    parser.add_argument("--seed", type=int, default=random.randrange(sys.maxsize),
                        help="Set seed to make random polynomials deterministic.")
    parser.add_argument("--output","-o", type=str,
                        help="If --random or --randomquad is set: prints polynomial system to given path.")
    parser.add_argument("--info",action="store_true",
                        help="Prints some info of the ANF.")
    parser.add_argument("--qrks",action="store_true",
                        help="Print quadratic ranks of input polynomials.")
    parser.add_argument("--quiet","-q",action="store_true",
                        help="Does not print anything on console.")
    args = parser.parse_args()

    if args.path is None and args.randomquad is None and args.random is None:
        parser.print_usage(sys.stderr)
        quit()


    random.seed(args.seed)


    assert(args.randomquad is None or args.random is None)
    
    if args.randomquad is not None:
        if not(args.quiet):
            print("Seed was", args.seed)
        for i in range(1,int(args.randomquad[0])+1):
            name = f"x[{i}]"
            indetDict[name] = i
            indetDict_rev[i]=name
        system = Anf.randomQuadSys(int(args.randomquad[0]),int(args.randomquad[1]),bool(args.randomquad[2]))


    if args.random is not None:
        if not(args.quiet):
            print("Seed was", args.seed)
        for i in range(1,int(args.random[0])+1):
            name = f"x[{i}]"
            indetDict[name] = i
            indetDict_rev[i]=name
        system = Anf.randomSys(n=int(args.random[0]),s=int(args.random[1]),deg=int(args.random[2]),sat=bool(args.random[3]))


        
    if args.path is not None:
        system = readPolySys(args.path,indetDict,indetDict_rev)[0]

    if args.output is not None:
        printPolySys(system,args.output)


    if args.info:
        print("nb. of indeterminates:     "+str(len(indetDict)-1))
        print("nb. of polynomials:        "+str(len(system)))
        print("av. nb. of terms:          "+str(sum([ p.numTerms() for p in system ])/len(system))[:5])
        print("av. nb. of non-lin. terms: "+str(sum([ p.numTerms_nonLin() for p in system ])/len(system))[:5])
        print("degree distribution:       "+str(dict(Counter([ p.deg() for p in system ]))))
        

    if args.qrks:
        print("quadratic ranks of polys:  "+str([ p.qrk() for p in system ]))

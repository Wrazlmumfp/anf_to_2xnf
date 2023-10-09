#!/usr/bin/env python3

import sys
import os
import numpy as np
import time
import copy # for deepcopy
import itertools
import random

F2 = None

class Xnf:
    numVars = 0
    xClauses = []
    comments = [] # string containing the comments
    def __init__(self, clauses=[], numVars=-1, comments=[]):
        # special cases
        if not(type(clauses) in {list,str}):
            raise TypeError("Please insert a list of clauses or a string to construct XNF.")
        if not(type(numVars) == int):
            raise TypeError("Please insert a number of variables to construct XNF.")
        if clauses == [] or clauses == [[]]:
            self.comments = comments
            self.xClauses = []
            return
        # now main part
        self.comments = comments
        if type(clauses) == str:
            x = Xnf.fromString(clauses)
            self.numVars = x.numVars
            self.xClauses = x.xClauses
            self.comments.extend(x.comments)
            return
        self.xClauses = []
        if type(clauses[0]) == int:
            self.xClauses = [xClause(lineral(clauses))]
            return
        for c in clauses:
            if type(c) == xClause:
                self.xClauses.append(c)
            elif type(c) == list or type(c) == lineral:
                self.xClauses.append(xClause(c))
            else:
                raise TypeError("Allowed types in list for constructing XNF: list, xClause, lineral.")
        # compute numVars
        if numVars == -1:
            self.numVars = max(self.getVars(),default=0) # + [0] since otherwise argument could be empty
        else:
            self.numVars = numVars
    def __str__(self,ind_len=0):
        ind = "".join([" " for i in range(ind_len)])
        s = ind + "{ XNF with " + str(self.numVars) + " variables,\n"
        if self.comments != []:
            s += ind + "  Comments:\n"
            s += "\n".join([ind + "    " + c for c in self.comments]) + "\n"
        if self.xClauses != []:
            s += ind + "    ( " + str(self.xClauses[0]) + " )\n"
        for l in self.xClauses[1:]:
            s += ind + "  & ( " + str(l) + " )\n"
        s += "}"
        return s
    def __repr__(self):
        return str(self)
    def __getitem__(self,index):
        """Returns the i'th xClause."""
        return self.xClauses[index]
    def __setitem__(self,index,value):
        """Return sets the i'th clause to the given value."""
        if not(type(value) == xClause):
            raise TypeError("can only set objects of type xClause.")
        self.xClauses[index] = value
    def __len__(self):
        """Returns the number of clauses."""
        return len(self.xClauses)
    def __and__(self,other):
        """Takes one additional Xnf and returns a new Xnf whose clauses are the union of the given Xnfs."""
        return Xnf(self.xClauses + other.xClauses,max(self.numVars,other.numVars))
    def deg(self):
        return max([len(c) for c in self.xClauses])
    def fromString(s):
        """Takes a string containing a description of an XNF in XNF or DIMAS CNF format and returns the corresponding XNF."""
        lines = s.split("\n") # split at "\n"
        comments = [x for x in lines if len(x) > 0 and x[0] == "c"]
        lines = [l for x in lines for l in x.split(" 0") if l != '' and not(x[0] == "c")] # remove comments and split at " 0"
        cList = [] # list of all XOR clauses
        for x in lines:
            if x == '':
                continue
            if x[0] == "p":
                xList = x.split()
                if not(xList[1] == "cnf" or xList[1] == "xnf"):
                    raise Exception('Unknown problem. Please use \"xnf\" or \"cnf\" as problem type.')
                if len(xList) != 4:
                    raise Exception('Syntax Error. \"p\" has to be followed by the problem def, the number of vars, and then the number of clauses.')
                if 'numVars' in vars():
                    raise Exception('Multiple uses of lines starting with \"p\" not allowed.')
                numVars = int(xList[2]) # currently not used
                getNumClauses = xList[3] # currently not used
            elif x[0] == "x":
                cList.append(xClause(lineral([int(lit) for lit in x.split()[1:] if lit != ""])))
            else:
                cList.append(xClause(x))
        return Xnf(clauses=cList,comments=comments)
    def getComments(self):
        return "\n".join(self.comments)
    def getXClauses(self):
        """Returns a list containing all clauses."""
        return self.xClauses
    def getClauses(self):
        """Returns a list containing all clauses."""
        return self.getXClauses()
    def getVars(self):
        """Returns a (sorted) list contianing all variables appearing in the XNF."""
        return sorted(list({lit for clause in self.xClauses for xLit in clause.xLits for lit in xLit.lits}))
    def add(self,c):
        """Takes an xClause and adds it to the set of clauses. Allowed input: List, lineral, xClause."""
        self.append(c)
    def append(self,c):
        """Takes an xClause and adds it to the set of clauses. Allowed input: List, lineral, xClause."""
        if type(c) == list or type(c) == lineral:
            c = xClause(c)
        elif type(c) != xClause:
            raise TypeError("Can only append objects of type xClause or list to Xnf.")
        self.xClauses.append(c)
        vars = [ v for xLit in c.xLits for v in xLit.lits ]
        if vars != []:
            self.numVars = max(self.numVars,max(vars))
    def extend(self,L):
        """Takes a list or set of xClauses and appends all of them to self."""
        for l in L:
            self.append(l)
    def getNumVars(self) -> int:
        """Returns the maximal variable occuring in self."""
        return self.numVars
    def getNumClauses(self) -> int:
        """Returns the number of clauses."""
        return len(self.xClauses)
    def asXnf(self) -> str:
        """Converts self into a string in XNF file format."""
        s = "p xnf " + str(self.numVars) + " " + str(self.getNumClauses()) + "\n"
        s += "\n".join([xclause.asXnf() for xclause in self.xClauses])
        return s
    def asXcnf(self) -> str:
        """Converts self into a string in DIMACS CNF file format with additional XOR literals (input for CryptoMiniSat)."""
        xcnf = self.convertToXcnf()
        s = "p cnf " + str(xcnf.numVars) + " " + str(xcnf.getNumClauses()) + "\n"
        clause_strings = []
        for clause in xcnf.xClauses:
            if clause.len() > 1:
                clause_strings.append(clause.asXnf())
            else:
                clause_strings.append(clause[0].asCnf())
        return s + "\n".join(clause_strings)
    def asCnf(self,cuttingLength=5) -> str:
        """Converts self into a string in DIMACS CNF file format (introduces additional variables for substituting XOR literals)."""
        cnf = self.convertToCnf(cuttingLength)
        s = "p cnf " + str(cnf.getNumVars()) + " " + str(cnf.getNumClauses()) + "\n"
        return s + "\n".join([clause.asXnf() for clause in cnf.getClauses()])
    def isCnf(self) -> bool:
        """Checks whether self is in CNF."""
        return False in [len(xl) > 1 for xc in self.xClauses for xl in xc]
    def ddv(self) -> list:
        """Returns ddv(self) as a list of integers [a_1,...,a_d] where a_i is the number of clauses of length i."""
        L = []
        for c in self.xClauses:
            if len(c) > len(L):
                L.extend([ 0 for i in range(len(c)-len(L))])
            L[len(c)-1] = L[len(c)-1] + 1
        return L
    def cleanup(self,origNumIndets,indetDict):
        """Interreduces XOR clauses and updates self (Gaussian Constraint Propagation)."""
        sthChanged = True
        while sthChanged:
            sthChanged = False
            sthChanged = self.reduceLins() or sthChanged
            sthChanged = self.deleteVars(origNumIndets,indetDict) or sthChanged
            sthChanged = self.cleanupVarnames(origNumIndets,indetDict) or sthChanged
            sthChanged = self.update() or sthChanged
    def cleanup_light(self):
        """Light version of cleanup (Gaussian Constraint Propagation); does not need indetDict."""
        sthChanged = True
        while sthChanged:
            sthChanged = False
            sthChanged = self.reduceLins() or sthChanged
            sthChanged = self.update() or sthChanged
    def deleteVars(self,origNumIndets,indetDict):
        """
        Only used after reduceLins(). Deletes redundant XOR literals that only describe indets greater than origNumIndets.
        Returns Boolean whether something was deleted.
        """
        remove = []
        removeVars = []
        for i,c in enumerate(self.xClauses):
            if len(c) > 1 or c.head().head() <= origNumIndets:
                continue
            remove.append(i)
            removeVars.append(c[0].head())
        for l in reversed(remove):
            del self.xClauses[l]
        # the following is just removing removed variables from indetDict
        # only because python can not do call by reference to overwrite indetDict
        removeKeys = []
        for key, value in indetDict.items():
            if value in removeVars:
                removeKeys.append(key)
        for key in removeKeys:
            del indetDict[key]
        return len(remove) > 0
    def cleanupVarnames(self,origNumIndets,indetDict):
        """Cleans up variable names such that all variables in {1,...,xnf.numVars}. Returns whether something has changed."""
        indets = list(set(self.getVars()+list(range(1,origNumIndets+1))))
        # delete indeterminates that are not part of self.getVars()
        for key in [k for k in indetDict.keys() if not((indetDict[k] in indets) or (indetDict[k] == []) or (indetDict[k] < origNumIndets))]:
            del indetDict[key]
        translateDict = dict()
        for i,v in enumerate(indets):
            translateDict[v] = i+1
        for key, value in indetDict.items():
            if not(value == []) and value in translateDict.keys():
                indetDict[key] = translateDict[value]
        lookup = dict()
        vname = 0
        for i in indets:
            vname += 1
            lookup[i] = vname
        self.numVars = vname
        for xClause in self.xClauses:
            for xLit in xClause.xLits:
                xLit.lits = frozenset({lookup[lit] for lit in xLit.lits})
    def convertToXcnf(self):
        """Returns an equivalent Xnf (in possibly more variables) which only contains clauses and pure XOR literals, i.e. can be used as input for CryptoMiniSat."""
        cnf = Xnf([])
        numVars = self.numVars
        auxVars = dict() # dictionary storing auxVars[xLit.lits] = corresponding additional variable
        for xCl in self.xClauses:
            if len(xCl) == 1:
                cnf.add(xCl)
                continue
            newClause = xClause()
            for xLit in xCl.xLits:
                if len(xLit) == 1:
                    newClause.add(xLit)
                    continue
                if xLit.lits in auxVars:
                    newClause.add(lineral([auxVars[xLit.lits]],xLit.xnor))
                else:
                    numVars += 1
                    y = numVars
                    auxVars[xLit.lits] = y
                    newClause.add(lineral([y],xLit.xnor))
                    cnf.add(lineral([y],False) + lineral(xLit.lits,True)) # add NOT(y XOR xLit) == (y <-> xLit)
            cnf.add(newClause)
        return cnf
    def convertToCnf(self,cuttingLength=5):
        """
        Returns an equivalent Xnf (in possibly more variables) which is in CNF.
        cuttingLength (default 5) is the maximal length of XOR literals that are not split up using additional variables.
        """
        xcnf = self.convertToXcnf()
        numVars = xcnf.getNumVars()
        # first introduce additional variables to split up XOR literals
        xLits = [c[0] for c in xcnf.getXClauses() if len(c) == 1]
        newxLits = [l for l in xLits if len(l) <= cuttingLength]
        oldxLits = [l for l in xLits if len(l) > cuttingLength]
        while oldxLits != []:
            xLit = oldxLits.pop()
            lits = list(xLit.lits)
            addVars = []
            for i in range(int(np.ceil(len(lits)/(cuttingLength-1)))):
                numVars += 1
                newxLits.append(lineral([numVars]+lits[(cuttingLength-1)*i:(cuttingLength-1)*i+(cuttingLength-1)],False))
                addVars.append(numVars)
            if not(xLit.xnor):
                newxLits[-1].xnor = False
            newXLit = lineral(addVars,xLit.xnor)
            if len(newXLit) > cuttingLength:
                oldxLits.append(newXLit)
            else:
                newxLits.append(newXLit)
        xcnf = Xnf([c for c in xcnf.getXClauses() if len(c) > 1] + [xClause(xLit) for xLit in newxLits], numVars)
        clauses = []
        for clause in xcnf.xClauses:
            if clause.len() > 1:
                clauses.append(clause)
                continue;
            xlit = clause[0]
            if xlit.xnor:
                negs_list = [set(s) for k in range(len(xlit)+1) if k%2==0 for s in itertools.combinations(xlit.lits,k)]
            else:
                negs_list = [set(s) for k in range(len(xlit)+1) if k%2==1 for s in itertools.combinations(xlit.lits,k)]
            for s in negs_list:
                clauses.append(xClause([[i] for i in xlit.lits-s|{-i for i in s}]))
        return Xnf(clauses,numVars)
    def substitute(self,xlit):
        """Takes an lineral with literals x_1+...+x_r, and uses it to substitute x_1 it in the whole Xnf by x_2+...+x_r."""
        for c in self.xClauses:
            c.substitute(xlit)
    def solve(self):
        """
        Uses CryptoMiniSat to solve self. Returns a tuple (sat?,solution) where solution is a tuple (None, ...) such that tuple[var] contains the assignment of variable var.
        Needs CryptoMiniSat installed, see https://github.com/msoos/cryptominisat.
        """
        # actually, you should use temporary file since string may be too big to be passed to "echo"
        tmp_filename = "xnf_solve_cryptominisat_tmp_" + str(random.randint(0,1000)) + ".cnf"
        tmp = open(tmp_filename,"w")
        print(self.asXcnf(),file=tmp)
        tmp.close()
        out = os.popen("cryptominisat5 --verb 0 " + tmp_filename).read()
        os.popen("/bin/rm " + tmp_filename)
        # uncomment if file does not work
#        out = os.popen("echo \"" + self.asXcnf() + "\" | cryptominisat5 --verb 0").read()
        if "UNSATISFIABLE" in out:
            return (False,None)
        else:
            return (True, tuple([None]) + tuple([not(str(-(i+1))+" " in out) for i in range(self.numVars)]))
    def solve_randomwalk(self):
        """
        Solves self with a random walk algorithm (see Papadimitriou, 'On Selecting a Satisfying Truth Assignment')
        Returns a tuple (k,sol) where k is the number of steps needed to solve and sol is of the form (None, bool1, bool2, ...) such that sol[var] contains the assignment of var.
        Note: Only works if self is in 2-XNF.
        """
        if self.deg() > 2:
            raise Exception("solve_randomwalk only works for XNFs of degree <= 2")
        self.cleanup_light() # very important!
        n = self.getNumClauses()
        randomSol = [None] + [bool(random.getrandbits(1)) for i in range(self.getNumVars())]
        deg1_lits = [c[0] for c in self.getXClauses() if len(c) == 1]
        deg2_clauses_inds = [i for i in range(n) if len(self[i]) == 2]
        step_counter = 1
        while True:
            remaining_deg2clauses_inds = [i for i in deg2_clauses_inds] # copy of deg2_clauses_inds
            # function iterates over all inds i in remaining_deg2clauses_inds and checks whether self[i] evaluates to True
            solChanged = False
            while remaining_deg2clauses_inds != []:
                # choose random clause
                rand = random.randint(0,len(remaining_deg2clauses_inds)-1)
                c_ind = remaining_deg2clauses_inds[rand]
                del remaining_deg2clauses_inds[rand]
                c = self[c_ind]
                # evaluate random clause
                if not(c.evaluate(randomSol)):
                    # if c does not evaluate to True, then flip one random bit of randomSol such that it does
                    rand_lit = c[random.getrandbits(1)]
                    rand_var = list(rand_lit.lits)[random.randint(0,len(rand_lit)-1)]
                    randomSol[rand_var] = not(randomSol[rand_var])
                    step_counter += 1
                    solChanged = True
                    break
            if not(solChanged):
                for c in deg1_lits: # suffices to be done at the end
                    randomSol[c.head()] = not(randomSol[c.head()] != c.evaluate(randomSol)) # != is XOR
                return (step_counter,tuple(randomSol))
    def reduceLins(self):
        """Interreduces all pure XOR literals of self. Returns whether something has changed."""
        sthChanged, xors = interreduced([ c[0] for c in self.xClauses if len(c) == 1 ])
        self.xClauses = [ c for c in self.xClauses if len(c) != 1 ]
        for x in xors:
            try: # strictly spoken one needs to do an update every iteration, but that is very expensive
                self.substitute(x)
            except:
                self.update()
                self.substitute(x)
        self.xClauses.extend([xClause(x) for x in xors])
        return sthChanged
    def update(self):
        """Updates all xClauses and removes the ones that evaluate to True. Return whether something has changed."""
        trues = []
        sthChanged = False
        if True in [c.isFalse() for c in self.xClauses]:
            self.xClauses = []
            return True
        for i,c in enumerate(self.xClauses):
            sthChanged = sthChanged or c.reduce()
            if c.isTrue():
                trues.append(i)
                sthChanged = True
        # remove elements with index in "trues" from self.xClauses
        self.xClauses = MakeSet([c for i,c in enumerate(self.xClauses) if not(i in trues)])
        return sthChanged
    def evaluate(self,sol):
        """Evaluates self at sol where sol is a tuple with entries True, False such that sol[i] is substituted for x[i] (sol[0] is None)."""
        if sol[0] is not None:
            sol = tuple([None])+tuple(sol)
        return not(0 in [c.evaluate(sol) for c in self.xClauses])
    def random(num_vars:int, num_clauses:int, k:int, sat:bool):
        """Returns a random xnf in k-XNF with num_vars variables, num_clauses clauses. If sat==True, then the xnf is guaranteed to have at least one solution."""
        variables=list(range(1,num_vars+1))
        if not(sat):
            return Xnf([xClause.random(variables,k) for i in range(num_clauses)])
        random_sol = [None] + [bool(random.randint(0,1)) for i in range(num_vars)]
        clauses = []
        for j in range(num_clauses):
            c = xClause.random(variables,k)
            while not(c.evaluate(random_sol)):
                c = xClause.random(variables,k)
            clauses.append(c)
        return Xnf(clauses)
    def random_cnf(num_vars:int, num_clauses:int, k:int, sat:bool):
        """Returns a random xnf in k-CNF (!) with num_vars variables, num_clauses clauses. If sat==True, then the xnf is guaranteed to have at least one solution."""
        variables=list(range(1,num_vars+1))
        if not(sat):
            return Xnf([ [[(-1)**random.randint(0,1)*lit] for lit in random.sample(variables,k)] for i in range(num_clauses)])
        random_sol = [None] + [bool(random.randint(0,1)) for i in range(num_vars)]
        clauses = []
        for j in range(num_clauses):
            c = xClause([[(-1)**random.randint(0,1)*lit] for lit in random.sample(variables,k)])
            while not(c.evaluate(random_sol)):
                c = xClause([[(-1)**random.randint(0,1)*lit] for lit in random.sample(variables,k)])
            clauses.append(c)
        return Xnf(clauses)



class xClause:
    xLits = []
    def __init__(self, xLits=[]):
        if xLits == []:
            self.xLits = []
            return
        elif type(xLits) == lineral:
            self.xLits = [xLits]
        elif type(xLits) == list:
            if type(xLits[0]) == list:
                self.xLits = [lineral(xlit) for xlit in xLits]
            elif type(xLits[0]) == lineral:
                self.xLits = xLits
            elif type(xLits[0]) == int:
                self.xLits = [lineral(xLits)]
        elif type(xLits) == str:
            self.xLits = [lineral(xlit) for xlit in xLits.split() if xlit != "0"]
        else:
            raise TypeError("Allowed types in list for constructing xClause: list of lists of int, list of lineral, lineral, list of int.")
        self.xLits.sort()
    def __str__(self):
        if self.xLits == []:
            return "False"
        return " || ".join([str(xLit) for xLit in self.xLits])
    def __repr__(self):
        return str(self)
    def len(self) -> int:
        """Returns number of linerals."""
        return len(self.xLits)
    def asXnf(self) -> str:
        """Prints self as one line for DIMACS CNF format."""
        return " ".join([xLit.asXnf() for xLit in reversed(self.xLits)]) + " 0"
    def head(self):
        """Returns the first lineral in self.xLits."""
        return list(self.xLits)[0]
    def __getitem__(self,index):
        """Returns the i'th lineral in self.xLits."""
        return self.xLits[index]
    def __setitem__(self,index,value):
        """Sets the i'th lineral in self.xLits to value. self.xLits are sorted afterwards to maintain the correct order."""
        if type(value) == list:
            self.xLits[index] = lineral(value)
        elif type(value) == lineral:
            self.xLits[index] = value
        else:
            raise TypeError("can only set objects of type list or lineral into an xClause")
        self.xLits.sort()
    def __len__(self) -> int:
        """Returns number of linerals."""
        return len(self.xLits)
    def __eq__(self,other) -> bool:
        """Checks (semantic) equality."""
        if type(other) == xClause:
            return set(self.xLits) == set(other.xLits)
        else:
            return False
    def __or__(self,other):
        """Returns a new xClause that is the conctenation of self and other."""
        return xClause(self.xLits + other.xLits)
    def __hash__(self):
        return hash(str(self))
    def add(self,l):
        """Appends a given lineral to the list of linerals."""
        self.append(l)
    def append(self,l):
        """Appends a given lineral to the list of linerals and sorts them again."""
        if type(l) == list:
            self.xLits.append(lineral(l))
        elif type(l) == lineral:
            self.xLits.append(l)
        else:
            raise TypeError("can only append objects of type list or lineral to an xClause")
        self.xLits.sort()
    def extend(self,L):
        """Appends all linerals in a given list to the list of linerals."""
        for l in L:
            self.append(l)
    def getVars(self):
        """Returns a (sorted) list containing all variables appearing in the XOR clause."""
        return sorted(list({lit for xLit in self.xLits for lit in xLit.lits}))
    def substitute(self,xlit):
        """Takes a XOR literal and substitutes it in every XOR literal of self."""
        for i in range(len(self)):
            self.xLits[i].substitute(xlit)
    def reduce(self):
        """Reduces the XOR literals such that they have pair-wise distinct leading terms."""
        len_bev = len(self.xLits)
        self.xLits = [l.Not() for l in interreduced([l.Not() for l in self.xLits])[1]]
        return len(self.xLits) < len_bev
    def isTrue(self) -> bool:
        """Checks whether one of the linerals already evaluates to True."""
        t = lineral([],False) # XNOR() == True == 1
        return t in self.xLits
    def isFalse(self):
        """Checks whether there are no literals in self.xLits."""
        return self.xLits == []
    def update(self):
        """Same as self.reduce()."""
        self.reduce()
    def evaluate(self,sol):
        """Evaluates self at sol. Sol has to be a tuple with entries True,False."""
        if sol[0] is not None:
            sol = tuple([None])+tuple(sol)
        return 1 in [xLit.evaluate(sol) for xLit in self.xLits]
    def random(variables, k):
        """Returns a random clause of length <= k in the given variables."""
        return xClause([lineral.random(variables) for i in range(random.randint(1,k))])
        

    
# Note: False is the neutral element of XOR. Hence lineral([]) = False, even if lineral([]).xnor = True.
class lineral:
    lits = frozenset()
    xnor = True # if False, then lineral == XNOR(lits) == lits+1
    def __init__(self, lits, xnor=None):
        if isinstance(lits,str): # also allowed to initialize with string of the form "-1+3"
            lits = [int(x) for x in lits.split("+")]
        if xnor is None:
            if len(lits) == 1: # more efficient to not use np.prod
                self.xnor = bool(np.sign(lits[0]) == 1)
            else:
                self.xnor = bool(np.prod([np.sign(l) for l in lits]) == 1) # needs bool(...) since otherwise the type is numpy.bool_
        else:
            self.xnor = xnor
        assert(all(isinstance(l,int) for l in lits))
        if isinstance(lits,set) or isinstance(lits,frozenset):
            lits = frozenset({abs(l) for l in lits})
        elif isinstance(lits,list):
            lits = [abs(l) for l in lits]
            lits = frozenset({ i for i in lits if lits.count(i) % 2 == 1 })
        if 0 in lits:
            lits.remove(0)
            xnor = False
        self.lits = lits
    def __str__(self):
        if self.lits == frozenset():
            return str(not(self.xnor)) # empty XOR literal is False, empty XNOR literal true
        s = "(" + "+".join([str(s) for s in sorted(list(self.lits))]) + ")"
        if not(self.xnor):
            s = "^" + s
        return s
    def __repr__(self):
        return str(self)
    def __getitem__(self,index):
        raise Exception("Obsolete functions. __getitem__ should not be used on lineral.")
    def __setitem__(self,index,val):
        raise Exception("Obsolete functions. __setitem__ should not be used on lineral.")
    def __len__(self):
        return len(self.lits)
    def __eq__(self,other):
        """Checks semantic equality."""
        if type(other) != lineral:
            return False
        return self.lits == other.lits and self.xnor == other.xnor
    def __lt__(self,other):
        """Compares two XOR literals with some order (not important which order, just has to be fixed)"""
        if self.lits == other.lits:
            return not(self.xnor) and not(self.xnor == other.xnor)
        elif len(self) == len(other):
            a = self.lits-other.lits
            b = other.lits-self.lits
            return min(a) > min(b)
        else:
            return len(self) < len(other)
    def __le__(self,other):
        """Compares two XOR literals with some order (not important which order)"""
        return self == other or self < other
    def __gt__(self,other):
        """Compares two XOR literals with some order (not important which order)"""
        return other < self
    def __ge__(self,other):
        """Compares two XOR literals with some order (not important which order)"""
        return other <= self
    def __hash__(self):
        return hash(frozenset({self.lits,self.xnor}))
    def __len__(self):
        return len(self.lits)
    def Not(self):
        """Returns a new lineral which is the negation of the current one."""
        return lineral(self.lits.copy(),not(self.xnor))
    def isTrue(self):
        """Returns whether lineral evaluates to True."""
        return self.lits == frozenset() and self.xnor == False
    def isFalse(self):
        """Returns whether lineral evaluates to False."""
        return self.lits == frozenset() and self.xnor == True
    def notEq(self,other):
        """Checks whether self == not(other)."""
        return self.lits == other.lits and self.xnor != other.xnor
    def __add__(self,other):
        """Computes self XOR other."""
        if type(other) == int and other == 1:
            return self.Not()
        return lineral(self.lits ^ other.lits, self.xnor == other.xnor)
    def negate(self):
        """Sets self := not(self)"""
        self.xnor = not(self.xnor)
    def as_list(self):
        """Returns self as list [i_1,...,i_s] with integers (variables) where the sign of the first one represents self.xnor."""
        l = list(self.lits)
        if self.xnor:
            l[0] = -l[0]
        return l
    def append(self,item):
        """Adds a given variable to self.lits."""
        self.add(item)
    def add(self,item):
        """Adds a given variable to self.lits."""
        self.lits.add(item)
    def extend(self,L):
        """Extends self.lits by a given list or set of variables."""
        for l in L:
            self.add(l)
    def head(self):
        """Returns largest literal or 0 if lineral is empty"""
        return max(self.lits,default=0)
    def asXnf(self):
        """Prints self for XNF file type, e.g. \'-1+2+3\'."""
        s = "+".join([str(s) for s in sorted(list(self.lits))])
        if not(self.xnor):
            s = "-" + s
        return s
    def asCnf(self):
        """Prints self for DIMACS CNF file type, e.g. \'x 1 2 3 0\'."""
        s = "" if len(self) == 1 else "x "
        s += "-" if not(self.xnor) else ""
        s += " ".join([str(s) for s in sorted(list(self.lits))])
        s += " 0"
        return s
    # takes a lineral and uses it to substitute the first occuring variable
    def substitute(self,other):
        """Takes an lineral and substitutes its largest variable in self, if it is in self.lits."""
        if other.head() in self.lits:
            # if we assume that xlit holds, then (self <=> not(self XOR xlit))
            self.lits = self.lits ^ other.lits
            self.xnor = not(self.xnor == other.xnor)
    def evaluate(self,sol):
        """Evaluates self at sol. Sol has to be a tuple with entries True,False."""
        if sol[0] is not None:
            sol = tuple([None])+tuple(sol)
        return bool((sum([int(sol[i]) for i in self.lits])+self.xnor+1)%2)
    def random(variables):
        """Returns a random lineral in the given variables."""
        return lineral(random.sample(variables,random.randint(1,len(variables))),bool(random.getrandbits(1)))


def splitList(l,value):
    """Splits a given list l at a given value."""
    if l == []:
        return []
    size = len(l)
    idx_list = [idx + 1 for idx, val in
                enumerate(l) if val == value]
    return [l[i: j] for i, j in
            zip([0] + idx_list, idx_list + ([size] if idx_list[-1] != size else []))]


def convertToXOR(c):
    """
    Converts a given string of a XOR literal into a list of the literals.
    E.g.\'1+2+3+-4\' is converted to [-1,2,3,4] (where the latter contains ints).
    """
    return lineral(list(map(int,c.split("+"))))


def readXNF(file_path):
    """Takes a file path to a DIMACS CNF or an XNF file and converts it to an object of the class XNF."""
    f = open(file_path, "r")
    s = f.read()
    f.close()
    return Xnf(s)



def MakeSet(L):
    """Removes duplicates from a given list L."""
    #temp_L = []
    #for l in L:
    #    if not(l in temp_L):
    #        temp_L.append(l)
    #return temp_L
    return list(set(L))


def interreduced(xLits):
    """
    Takes a list of linerals and interreduces them using linear algebra.
    Returns a tuple (BOOL,LIST) where BOOL states whether something changed in the interreduction
    """
    import galois
    global F2
    if F2 is None:
        # ignore TBB outdated version warning
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            F2 = galois.GF(2)
    if xLits == []:
        return False, []
    basis = set()
    for s in xLits:
        if type(s) != lineral:
            raise TypeError("Input of interreduced has to be a list of objects of type lineral.")
        basis = basis | set(s.lits) # union
    basis = sorted(list(basis),reverse=True)
    # matrix has one additional column for 1 or NOT
    #M = zeroMat(len(xLits),len(basis)+1)
    M = F2.Zeros((len(xLits),len(basis)+1))
    for j in range(len(xLits)):
        xlit = xLits[j]
        for lit in xlit.lits:
            M[j][basis.index(lit)] = 1
        if xlit.xnor:
            M[j][-1] = 1
    Mnew = M.row_reduce()
    newLits = []
    for row in Mnew:
        lit = { b for index, (b,c) in enumerate(zip(basis,row[0:-1])) if c == 1 }
        newLits.append(lineral(lit,row[-1] == 1))
    return set(newLits) != set(xLits), newLits




import argparse
if __name__=='__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("path",nargs='?',default=None,
                        help="Path to input xnf file.")
    parser.add_argument("--info",action="store_true",
                        help="Prints some info of the XNF.")
    parser.add_argument("--ddv", action="store_true",
                        help="Prints ddv of input xnf.")
    parser.add_argument("--numVars", action="store_true",
                        help="Prints number of variables of input xnf.")
    parser.add_argument("--numClauses", action="store_true",
                        help="Prints number of clauses of input xnf.")
    parser.add_argument("--random","-r", nargs=4, metavar=('num_vars','num_clauses','k','sat'),
                        help="Creates a random k-XNF with num_vars variables and num_clauses clauses. If sat==True, then the XNF is guaranteed to be satisfiable.")
    parser.add_argument("-xcp","--oxcnfpath",
                        help="If --random is used: stores the random XNF as DIMACS XCNF format in given path.")
    parser.add_argument("-cp","--ocnfpath",
                        help="If --random is used: Stores the random XNF as DIMACS CNF format in given path.")
    parser.add_argument("-xp","--oxnfpath",
                        help="If --random is used: Stores the random XNF in XNF file format.")
    
    args = parser.parse_args()

    if args.path is not None:
        x = readXNF(args.path)
    if args.ddv:
        print(x.ddv())
    if args.numVars:
        print(x.getNumVars())
    if args.numClauses:
        print(x.getNumClauses())
    if args.info:
        d = x.ddv()
        print("ddv:                   "+str(d))
        print("#clauses:              "+str(x.getNumClauses()))
        print("#variables:            "+str(x.getNumVars()))
        print("effective #variables:  "+str(x.getNumVars()-d[0]))
        print("average clause length: "+str(sum([j*(i+1) for i,j in enumerate(d)])/x.getNumClauses())[:5])

    if args.random is not None:
        if len(args.random) != 4:
            raise Exception("--random has to have exactly four input parameters: num_vars:Int, num_clauses:Int, k:Int, and sat:Bool")
        x = Xnf.random(int(args.random[0]),int(args.random[1]),int(args.random[2]),args.random[3] in {"True","true","t","T"})

    if args.oxcnfpath is not None:
        f = open(args.oxcnfpath,"w")
        if x.comments != []:
            print("\n".join(x.comments) + "\n" +  x.asXcnf(),file=f)
        else:
            print(x.asXcnf(),file=f)
        f.close()
    if args.ocnfpath is not None:
        f = open(args.ocnfpath,"w")
        if x.comments != []:
            print("\n".join(x.comments) + "\n" + x.asCnf(),file=f)
        else:
            print(x.asCnf(),file=f)
        f.close()
    if args.oxnfpath is not None:
        f = open(args.oxnfpath,"w")
        if x.comments != []:
            print("\n".join(x.comments) + "\n" + x.asXnf(),file=f)
        else:
            print(x.asXnf(),file=f)
        f.close()
    

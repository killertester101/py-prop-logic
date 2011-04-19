#prop_logic.py
#Functions, definitions and classes to manage propositional logic
#Based on pseudo code from Artificial Intelligence a Modern Approach by Russel and Norvig
#
#FolKB
#A FolKB is a knowledge base that can contain Horn-clauses.
#FolKB implements
# - tell(clause), this stores clause in the knowledge base
# - ask(clause), this asks if clause is entailed by what is already stored (telled) to the knowledge base.
# - retract(clause), removes clause from the knowledge base
#
#If clause is a string, it tries to create an Expr by calling make_expr
#FolKB can handle two types of clauses:
#- Facts: F(a,b,c...)
#- Rules: A & B & C & ... -> D
#NOTE: Variables are lower case, constants are upper case (reverse from Prolog)
#- Can handle negation as failure with the special keyword Not(...)
#See examples by running this with "python prop_logic.py"
#
#Copyright (C) 2011 Ulf Daniel Palmqvist
#This program is free software: you can redistribute it and/or modify
#it under the terms of the GNU General Public License as published by
#the Free Software Foundation, either version 3 of the License, or
#(at your option) any later version.

#This program is distributed in the hope that it will be useful,
#but WITHOUT ANY WARRANTY; without even the implied warranty of
#MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#GNU General Public License for more details.
#
#You should have received a copy of the GNU General Public License
#along with this program.  If not, see <http://www.gnu.org/licenses/>.

import string


def dprint(level,what):
    if level<3:
        print what

_i = 1
def standardize_variables(variables):
    return standardize(variables,{})
    
def standardize(variables,new_vars={}):
    global _i
    dprint(4,"standardize_variables, _i=%d, new_vars=%s"%(_i,new_vars))
    if isinstance(variables,list):
        output = []
        for v in variables:
            output.append(standardize(v,new_vars))
            _i += 1
        return output
    elif isinstance(variables,Expr):
        (new_exp,_i) = variables.standardize_variables(_i,new_vars)
        return new_exp
    elif isinstance(variables,str) and (variables[0] in string.lowercase):
        if variables in new_vars:
            return new_vars[variables]
        else:
            new_var = "x_%d" % _i
            _i += 1
            new_vars[variables] = new_var
            return new_var
    else:
        return variables

def subst(x,theta):
    if isinstance(x,list):
        output = []
        for xx in x:
            output.append(subst(xx,theta))
        return output
    elif isinstance(x,Expr):
        return Expr(x.op,subst(x.args,theta))
    elif isinstance(x,str) and (x[0] in string.uppercase):
        return x
    elif isinstance(x,str) and (x[0] in string.lowercase):
        if x in theta:
            return subst(theta[x],theta)#theta[x]
        else:
            return x
    else:
        return False


def make_expr(exp):
    #Makes the necessary Expr's from an input string. Minimal syntax check.
    exp=exp.strip()
    if "->" in exp:
        exp = exp.split("->")
        implication = exp[1]
        args = [make_expr(implication.strip())]
        clauses = exp[0].split('&')
        for c in clauses:
            args.append(make_expr(c.strip()))
        return Expr("<-",args)
    elif exp[0:3]=="Not":
        sub_exp = exp[4:(exp.rfind(")",4))]
        sub_expr = make_expr(sub_exp)
        op = "Not"
        args = [sub_expr]
        return Expr(op,args) 
    else:
        exp = exp.split("(")
        op = exp[0]
        exp[1]=exp[1].rstrip(")")
        args = exp[1].split(',')
        return Expr(op,args)
        

class Expr:
    def __init__(self, op, args):
        self.op = op
        self.args = args

        

    def __repr__(self):
        if self.op=="<-":
            args = [str(a) for a in self.args[1:]]
            op = str(self.args[0])
            return " & ".join(args)+" -> "+op
        else:
            args = [str(a) for a in self.args]
            op = self.op
            return "#:"+op+"("+",".join(args)+")"

    def standardize_variables(self,i,new_vars):
        output = []
        for v in self.args:
            if isinstance(v,Expr):
                (new_v,i) = v.standardize_variables(i,new_vars)
                output.append(new_v)
            elif v not in new_vars and v[0] in string.lowercase:
                new_vars[v]="x_%d"%i
                output.append(new_vars[v])
                i += 1
            elif v[0] in string.lowercase:
                output.append(new_vars[v])
            else:
                output.append(v)
        return (Expr(self.op, output),i)

    def __eq__(self, other):
        equal =  (other.op == self.op)
        equal &= len(self.args)==len(other.args)
        if not equal:   #Safequarding the zip operation below
            return False
        return all([x==y for (x,y) in zip(self.args,other.args)]) #This compares each argument, will
                                                                 # recursively call __eq__ if there are
                                                                 # Expr's among them.


def unify(x,y, exttheta = {}, naf = False):
    dprint(4,"unify x=%s, y=%s, theta=%s"%(x,y,exttheta))
    
    if exttheta==None:
        dprint(4,"unify theta=False, returned None")
        return None
    theta = dict(exttheta)
    if (x==y):
        dprint(4,"Unify, not NAF, %s==%s, returned %s"%(x,y,theta))
        return theta
    elif isinstance(x,str) and (x[0] in string.lowercase):
        return unify_var(x,y,theta)
    elif isinstance(y,str) and (y[0] in string.lowercase):
        return unify_var(y,x,theta)
    elif isinstance(x,Expr) and isinstance(y,Expr):
        return unify(x.args,y.args,unify(x.op,y.op,theta),naf)
    elif isinstance(x,list) and isinstance(y,list):
        return unify(x[1:],y[1:],unify(x[0],y[0],theta),naf)
    else:
        dprint(4,"unify returned None")
        return None
        
        
def unify_var(var,x,theta):
    if var in theta:
        return unify(theta[var],x,theta)
    elif x in theta:
        return unify(var,theta[x],theta)
    elif occurs(var,x):
        return None
    else:
        theta[var]=x
        return theta

        
def occurs(var,x):
    if isinstance(x,Expr):
        if occurs(var,x.args):
            return True
    if isinstance(x,list):
        if var in x:
            return True
    else:
        if var==x:
            return True
    return False    



def fol_bc_or(KB,goal,theta,level=0):
    dprint(3,"fol_bc_or: goal=%s, theta=%s, level=%d"%(goal,theta,level))
    if goal.op=="Not":
        sub_goal = goal.args[0]
        key = sub_goal.op
        naf = True
    else:
        key = goal.op
        naf = False
    rules = KB[key]
    dprint(3,"fol_bc_or: rules=%s"%rules)
    if not naf:
        for rule in rules:
            srule = standardize_variables(rule)
            if srule.op=="<-":
                (lhs,rhs) = (srule.args[1:],srule.args[0])
            else:
                rhs = srule
                lhs = []
            dprint(3,"fol_bc_or: lhs=%s, rhs=%s"%(lhs,rhs))

            dprint(3,"fol_bc_or: after unification, theta=%s"%theta)
            for thetap in fol_bc_and(KB,lhs,unify(rhs,goal,theta),level+1):
                dprint(3,"fol_bc_or: after fol_bc_and theta=%s"%theta)
                if thetap!=None:
                    yield dict(thetap)
                else:
                    yield None
    else:
        #Negation as failure
        check_goal = subst(sub_goal,theta)
        if any([x!=None for x in fol_bc_or(KB,check_goal,{})]):
            yield None
        else:
            yield dict(theta)
    
    raise StopIteration()
                    
def fol_bc_and(KB,goals,theta,level=0):
    dprint(3,"fol_bc_and: goals=%s, theta=%s"%(goals,theta))
    if theta == None:
        dprint(3,"fol_bc_and returned False")
        yield None
    elif len(goals)==0:
        dprint(3,"fol_bc_and: len(goals)==0")
        yield dict(theta)
    else:
        (first,rest) = (goals[0],goals[1:])
        for thetap in fol_bc_or(KB,subst(first,theta),theta,level+1):
            for thetapp in fol_bc_and(KB,rest,thetap,level+1):
                if thetapp:
                    yield dict(thetapp)
                else:
                    yield None
    raise StopIteration()

class FolKB:
    def __init__(self):
        self.KB =  {}
            
    def tell(self,goal):
        #This KB can store sentences of the form
        #Encoded as Expr("<-",[X,Y,Z]) where X, Y and Z are Expr's
        if isinstance(goal,str):
            goal=make_expr(goal)
            
        if goal.op=="<-":
            key = goal.args[0].op
        else:
            key = goal.op
        try:
            self.KB[key].append(goal)
        except:
            self.KB[key] = [goal]

    def retract(self,goal):
        if isinstance(goal,str):
            goal = make_expr(goal)
        if goal.op=="<-":
            key = goal.args[0].op
        else:
            key = goal.op
        if key in self.KB:
            if goal in self.KB[key]:
                self.KB[key].remove(goal)

    def ask(self,query):
        if isinstance(query,str):
            query = make_expr(query)
        query_vars = []
        for x in query.args:
            if x[0] in string.lowercase:
                query_vars.append(x)
        if len(query_vars)==0:
            #Return True or False only. No free variables to assign.
            if any([x!=None for x in self.fol_bc_ask(query)]):
                yield True
            else:
                yield False
            raise StopIteration()
        else:
            for r in self.fol_bc_ask(query):
                if r:
                    retval = dict()
                    for c in query_vars:
                        retval[c] = r[c]
                    yield retval
            raise StopIteration()                    

    def fol_bc_ask(self, query):
        #return prove_any(self.KB, query,{})
        return fol_bc_or(self.KB,query,{})

if __name__ == "__main__":

    if True:
        print "==================================================================================="
        print "Conversion from string to Expr"
        print "==================================================================================="
        
        to_convert = []
        
        to_convert.append("American(x) & Weapon(y) & Hostile(z) & Sells(x,y,z) -> Criminal(x)")
        to_convert.append("NewYorker(x) -> American(x)")
        to_convert.append("American(West)")
        to_convert.append("Not(Male(x)) -> Female(x)")
        for s in to_convert:
            print "%s ==> %s"% (s, make_expr(s))

    if False:
        print "==================================================================================="
        print "Cats"
        print "==================================================================================="
        myKB = FolKB()
        to_tell = []
        to_tell.append("Likes(Adam,Cats)")  #Adam likes Cats
        to_tell.append("Likes(x,x)")        #Everyone likes themselves
        to_tell.append("Likes(Jonas,x)")    #Jonas likes everyone

        to_ask=[]
        to_ask.append("Likes(x,Cats)")      #Who likes cats?
        for fact in to_tell:
            print "telling: %s" % fact
            myKB.tell(fact)
        for question in to_ask:
            print "Asking: %s" % question 
            for r in myKB.ask(question):    
                print "yielded:",r
    if False:
        print "==================================================================================="
        print "Weapon sales"
        print "==================================================================================="
        myKB = FolKB()

        to_tell = []
        to_tell.append("American(x) & Weapon(y) & Hostile(z) & Sells(x,y,z) -> Criminal(x)")
        to_tell.append("NewYorker(x) -> American(x)")
        to_tell.append("American(West)")
        to_tell.append("Weapon(Missile)")
        to_tell.append("Hostile(Nono)")
        to_tell.append("Sells(West,Missile,Nono)")
        to_tell.append("Sells(East,Missile,Nono)")
        to_tell.append("NewYorker(East)")
        to_tell.append("American(North)")
        to_ask = []
        to_ask.append("Criminal(West)") #Is West a criminal?
        to_ask.append("Criminal(East)") #Is East a criminal?
        to_ask.append("Criminal(North)")#Is North a criminal? (He is not, Iranically)
        to_ask.append("Criminal(x)") #Get the whole list of criminals
        
        for fact in to_tell:
            print "telling: %s" % fact
            myKB.tell(make_expr(fact))
        for question in to_ask:
            print "Asking %s" % question
            for r in myKB.ask(make_expr(question)):
                print "    yielded:",r
        print "Retracting NewYorker(East)"
        myKB.retract("NewYorker(East)")
        print "Asking Criminal(x)"
        for r in myKB.ask("Criminal(x)"):
            print "    yielded:",r

    if False:
        #This is by no means an attempt to implement the wumpus world example from AIMA
        #Please do not use
        print "==================================================================================="
        print "Wumpus!"
        print "==================================================================================="
        
        myKB = FolKB()
        physical_rules = []
        physical_rules.append("Neighbor(x,y) & Wumpus(y) -> Stench(x)")
        physical_rules.append("Visited(x) -> Safe(x)")
        physical_rules.append("Neighbor(x,y) & Stench(y) -> Unsafe(x)")
        print "Telling some physics rules"
        for r in physical_rules:
            print "telling: %s" % r
            myKB.tell(r)
        wumpus  = "Wumpus(B13)"
        n1      = "Neighbor(B12,B11)"
        n2      = "Neighbor(B12,B13)"
        v1      = "Visited(B11)"
        v2      = "Visited(B12)"
        q1      = "Unsafe(B11)"
        q2      = "Stench(B12)"
        q3      = "Unsafe(x)"
        q4      = "Safe(x)"
        neighbor_comm = Expr("<-",[Expr("Neighbor",["x","y"]),Expr("Neighbor",["y","x"])])    
        to_tell = [v1,v2,wumpus]
        to_ask  = [q1,q2,q3,q4]
        ymax=5
        xmax=5
        for fact in to_tell:
            print "Telling: %s" % fact
            myKB.tell(fact)
        if True:
            for x in range(1,xmax+1):
                for y in range(1,ymax+1):
                    if x>1:
                        neighbor="Neighbor(B%d%d,B%d%d)"%((x-1),y,x,y)
                        print "Telling: %s" %neighbor
                        myKB.tell(neighbor)
                    if y>1:
                        neighbor="Neighbor(B%d%d,B%d%d)"%(x,(y-1),x,y)
                        print "Telling: %s"% neighbor
                        myKB.tell(neighbor)
                    if x<xmax:
                        neighbor="Neighbor(B%d%d,B%d%d)"%((x+1),y,x,y)
                        print "Telling: %s" %neighbor
                        myKB.tell(neighbor)
                    if y<ymax:
                        neighbor="Neighbor(B%d%d,B%d%d)"%(x,(y+1),x,y)
                        print "Telling: %s"% neighbor
                        myKB.tell(neighbor)
        for question in to_ask:
            print "Asking  %s?"%question
            i=0
            for r in myKB.ask(question):
                print "yielded:",r
    if True:
        #This contains some more complicated relations
        print "==================================================================================="
        print "Family matters"
        print "==================================================================================="
        to_tell = []
        to_tell.append("Parent(Pam,Bob)")
        to_tell.append("Parent(Tom,Bob)")
        to_tell.append("Parent(Tom,Liz)")
        to_tell.append("Parent(Bob,Ann)")
        to_tell.append("Parent(Bob,Pat)")
        to_tell.append("Parent(Pat,Jim)")
#        to_tell.append("Female(Pam)")  #If this is included in the KB, we will not use negation as failure
#        to_tell.append("Female(Liz)")
#        to_tell.append("Female(Ann)")
#        to_tell.append("Female(Pat)")
        to_tell.append("Not(Male(x)) -> Female(x)") #Anything that is not Male is Female through negation as failure
        to_tell.append("Male(Tom)")
        to_tell.append("Male(Bob)")
        to_tell.append("Male(Jim)")
        to_tell.append("Parent(x,y) -> Offspring(y,x)")
        to_tell.append("Parent(x,y) & Female(x) -> Mother(x,y)")
        to_tell.append("Parent(y,x) & Parent(z,y) -> Grandparent(z,x)")
        to_tell.append("Parent(x,y) & Male(x) -> Father(x,y)")
        to_tell.append("Offspring(x,y) -> Descendant(x,y)")
        to_tell.append("Offspring(z,y) & Descendant(x,z)-> Descendant(x,y)")
        to_tell.append("Parent(z,x) & Parent(z,y) & Female(x) -> Sister(x,y)")
        to_tell.append("Father(x,y) & Father(y,z) -> Grandfather(x,z)")
        to_ask = []
        to_ask.append("Parent(x,Bob)")
        to_ask.append("Parent(Pam,Bob)")
        to_ask.append("Parent(x,y)")
        to_ask.append("Mother(x,y)")
        to_ask.append("Offspring(y,x)")
        to_ask.append("Grandparent(x,y)")
        to_ask.append("Father(x,Bob)")
        to_ask.append("Father(Bob,x)")
        to_ask.append("Descendant(x,Pam)")
        to_ask.append("Sister(x,y)")
        to_ask.append("Grandfather(x,y)")
        to_ask.append("Female(Jim)")
        to_ask.append("Female(Pam)")
        myKB = FolKB()
        for fact in to_tell:
            print "telling: %s" % fact
            myKB.tell(make_expr(fact))
        for question in to_ask:
            print "asking: %s" % question
            for r in myKB.ask(make_expr(question)):
                print "yielded:",r


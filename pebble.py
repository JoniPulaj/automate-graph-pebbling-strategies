import math
import random
import networkx as nx
from pyscipopt import Model, quicksum
import matplotlib.pyplot as plt
import cplex
import copy as cp


# Makes the LxL with directed edges.. using one from Glen's linear optimization technique paper
def makeLemkeProdDi():
    G=nx.Graph()
    G.add_edges_from([(1,2),(1,3),(2,4),(4,6),(3,6),(3,5),(4,8),(4,7),(4,5),(5,8),(7,8),(3,7),(6,8)])
    Lemk = nx.cartesian_product(G,G)
    Lemke = Lemk.to_directed()
    return Lemke
    
    
# Makes LxL undirected version
def makeLemkeProd():
    G=nx.Graph()
    G.add_edges_from([(1,2),(1,3),(2,4),(4,6),(3,6),(3,5),(4,8),(4,7),(4,5),(5,8),(7,8),(3,7),(6,8)])
    Lemk = nx.cartesian_product(G,G)
    return Lemk
    
    
# model for the bilevel programming formulation, the software license is expired needs to be updates
def makeModel(edges,rt,n):
    G=nx.Graph()
    G.add_edges_from(edges)
    G=G.to_directed()
    nx.draw(G)
    V=G.nodes()
    A = G.edges()
    size = len(A)
    
    
   # W[23]=-20
   # W[63]= 0
    #W[40]= 0
   # W[41]= 0
   # W[47]= -10
  #  W[59]= 0
   # W[20]= 0
    #W[27]= 0
  #  W[31]= -10
   
    model = Model()
    model.hideOutput() # silent/verbose mode
    z = {}
    y= {}
    model.setMinimize()
    keeps = 0
    total = len(V)
    f = open("FruchtGraphPebble.aux", "w")
    f.write('N %i \n' %size)
    f.write('M %i \n' %total)
    for i in V:
        if i!=rt:
           a= math.pow(2,nx.shortest_path_length(G,i,rt))-1
           y[i]= model.addVar(ub=a, vtype='I', obj=0.0, lb=0.0, name="y%s"% keeps)
           keeps = keeps +1

    for (i,j) in A:
        if j != rt:
           z[i,j] = model.addVar(ub=n/2, vtype='I', obj=0.0, lb=0.0, name="z%s"% keeps)
           f.write('LC %i \n' %keeps)
        else:
           z[i,j] = model.addVar(ub=n/2, vtype='I', obj=1.0, lb=0.0, name="z%s"% keeps)
           f.write('LC %i \n' %keeps)
        keeps = keeps +1
     
  
       

    count = 0
    model.addCons(quicksum(y[i] for i in V if i !=rt) <= n, name="cons%s"% count)
    count = count+1
    model.addCons(quicksum(y[i] for i in V if i !=rt) >= n , name="cons%s"% count)
    count = count+1
    for i in V:
        #print i
        if i != rt:
           model.addCons(quicksum(z[j,i] for j in V if (j,i) in A) -2*quicksum(z[i,j] for j in V if (i,j) in A) + y[i] >= 0, name="cons%s"% count)
        else:
           model.addCons(quicksum(z[j,i] for j in V if (j,i) in A ) -2*quicksum(z[i,j] for j in V if (i,j) in A ) >= 0, name="cons%s"% count)
        f.write('LR %i \n' %count)
        count = count+1
    for (i,j) in A:
        if j != rt:
          
           f.write('LO 0 \n')
        else:
           f.write('LO -1 \n')
    minus = 1
    f.write('OS %i \n' %minus)
    
  
   # model.setMaximize()
    model.writeProblem('pebbleLemke.lp')
    model.writeProblem('FruchtGraphPebble.mps')
    #spx=cplex.Cplex()
    #spx.read('pebbleLemke.lp')
    #spx.solve()
    plt.show()
    return 'A'


def partitionfunc(n,k,l=1):
    '''n is the integer to partition, k is the length of partitions, l is the min partition element size'''
    if k < 1:
        raise StopIteration
    if k == 1:
        if n >= l:
            yield (n,)
        raise StopIteration
    for i in range(l,n+1):
        for result in partitionfunc(n-i,k-1,i):
            yield (i,)+result
def random_ints_with_sum(n):
    """
    Generate non-negative random integers summing to `n`.
    """
    while n > 0:
        r = random.randint(0, n)
        yield r
        n -= r  
        
# method for getting solutions from cplex      
def access_solution_values(c, zinv):
    count = []
    for i, x in enumerate(c.solution.get_values()):
        if (x!= 0):
           print "Solution value of ",c.variables.get_names(i), " = ",x 
           #print(str(c.variables.get_names(i)))
           count.append(str(c.variables.get_names(i)))
           #print count
    return count 
    
    
#auxillary function for producing trivial variable bounds on shortest paths
def solvesmall(rt,filename):
    G= makeLemkeProdDi()
    spx=cplex.Cplex()
    spx.read(filename)
    spx.solve()
    V = G.nodes() 	 
    for i in V:
        s = str(i)
        nr = ''.join(i for i in s if i.isdigit())
        a= math.pow(2,nx.shortest_path_length(G,i,rt)) -1
        bd = str(a)
        print ("x%s" % nr + " <= " + bd)
    return list(spx.solution.get_values())


# find a bound for tree strategies using linear ordering and steiner trees

def makeTreesHop(Gr,rt,H,num,B,fixed):
    Hl = [0]*H
    for i in range(H):
        Hl[i]=i
    lnum=[0]*num
    for i in range(num):
        lnum[i]=i
    V=sorted(Gr.nodes())
    # get the edges from graph
    A = Gr.edges()
    # make some dictionaries for values of nodes
    l={}
    x={}
    g={}
    linv ={}
    xinv = {}
    ginv = {}
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMaximize()
    for t in range(num):
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            x[i,j,t] = model.addVar( vtype='B', obj=fixed[V.index(j)], lb=0.0,name="x%s"% nr)
            xinv['f'+ nr]=(i,j,t)

    for t in range(num):
        for i in range(H):
            for j in V:
                s = str((i,j,t))
                nr = ''.join(i for i in s if i.isdigit())
                g[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="g%s"% nr)
                ginv['g'+ nr]=(i,j,t)

  
    for t in range(num):
        for i in range(H):
            for j in V:
                s = str((j,i,t))
                nr = ''.join(i for i in s if i.isdigit())
                l[j,i,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="l%s"% nr)
                linv['l'+ nr]=(j,i,t)

    # fix roots constraint for every time period
    for t in range(num):
        s = str(t)
        nr = ''.join(i for i in s if i.isdigit())
        model.addCons(l[rt,0,t] == 0, name="rootfixl%s"% nr)
        model.addCons(g[0,rt,t] == 0, name="rootfixg%s"% nr)
    
    # all the other nodes fixed somewhere in between
    for t in range(num):      
        for j in V:
            if j != rt:
               s = str((j,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(l[j,1,t] == 0, name="allothernodesfixedls%s"% nr)
               model.addCons(g[H-1,j,t] == 0, name="allothernodesfixedgs%s"% nr)

    # trasitivity greater
    for t in range(num):
        for i in range(H-1):
            for j in V:
                s = str((i,j,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(g[i,j,t] - g[i+1,j,t] >= 0, name="transgreat%s"% nr)

    # each node either greater than i or less than i+1 not both
    for t in range(num):
        for i in range(H-1):
            for j in V:
                s = str((i,j,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(g[i,j,t] + l[j,i+1,t] == 1, name="lgnotboth%s"% nr)

    # forcing the direction of x_(i,j) or x_(j,i) in the chosen tree
    for t in range(num):
        for h in range(H):
            keepsi = [False]*len(A)
            for (i,j) in A:
                ind = A.index((i,j))
                if not keepsi[ind]:
                       keepsi[ind] = True
                       indrev =  A.index((j,i))
                       keepsi[indrev] = True
                       s = str((i,j,h,t))
                       nr = ''.join(i for i in s if i.isdigit())
                       srev = str((j,i,h,t))
                       nrev = ''.join(i for i in srev if i.isdigit())
                       model.addCons(l[i,h,t] + g[h,j,t]- x[i,j,t] >= 0, name="lgxij%s"% nr)
                       model.addCons(l[j,h,t] + g[h,i,t]- x[j,i,t] >= 0, name="lgxji%s"% nrev)

     #at most one incoming arc
    for t in range(num):
         for i in V:
             if i != rt:
                neb = Gr.neighbors(i)
                s = str((i,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(quicksum(x[j,i,t] for j in neb) <= 1, name="atmostonex%s"% nr)

     #connectee tree
    for t in range(num):
         for i in V:
             if i != rt:
                neb = Gr.neighbors(i)
                for w in neb:
                    s = str((i,w,t))
                    nr = ''.join(i for i in s if i.isdigit())
                    model.addCons(quicksum(x[j,i,t] for j in neb if j != w)  - x[i,w,t] >= 0, name="conntrex%s"% nr)


  



     

     #at least one v everytime period
    #for i in V:
         #if i != rt:
            # s = str(i)
            # nr = ''.join(i for i in s if i.isdigit())
            # model.addCons(quicksum(x[j,i,t] for j in V if (j,i) in A for t in lnum) >= 2, name="atleastonez%s"% nr)

    for t in range(num):
        model.addCons(0.5*quicksum(x[i,j,t] for t in lnum for (i,j) in A) + 0.5*quicksum(x[j,i,t] for t in lnum for (i,j) in A) <= B, name="numberofedgesnodes")

    #model.addCons(quicksum(z[i,h,t] for h in Hl for t in lnum for i in V if i !=rt) <= 428, name="bounad")
    #model.addCons(z[(1,2),1,0]==32, name="f1")
    #model.addCons(z[(2,1),1,1]==32, name="f2")
    #model.addCons(z[(3,1),1,2]==32, name="f3")
    #model.addCons(z[(1,3),1,3]==32, name="f4")
 
    model.writeProblem('treecuth.lp')
    spx=cplex.Cplex()
    spx.read('treecuth.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
    print spx.solution.get_objective_value()
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()

 # select tree strategies using Miller-Tucker-Z... formulation, weaker but fewer variables so more cuts...         
def makeTreeMtz(Gr,rt,H,num,extra):
    Hl = [0]*H
    for i in range(H):
        Hl[i]=i
    lnum=[0]*num
    for i in range(num):
        lnum[i]=i
    V=sorted(Gr.nodes())
    # get the edges from graph
    A = Gr.edges()
    # make some dictionaries for values of nodes
    x={}
    z={}
    y={}
 
    xinv = {}
    zinv = {}
    yinv = {}
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMinimize()
    #setting the variables: x is the flow from node to node, directed..
    for t in range(num):
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            x[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="x%s"% nr)
            xinv['f'+ nr]=(i,j,t)
    #z is variable that keeps track of weight distribution in nodes of chosen tree ..
    for t in range(num):
            for j in V:
                if j != rt:
                   s = str((j,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   z[j,t] = model.addVar(ub = 2**(H-1), vtype='C', obj=1.0, lb=0.0,name="z%s"% nr)
                   zinv['z'+ nr]=(i,t)
    #y is zero one variable on nodes for the flow ..
    for t in range(num):
            for j in V:
                if j !=rt:
                   s = str((j,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   y[j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="y%s"% nr)
                   yinv['y'+ nr]=(j,t)

   # setting constranints from now on : one incoming arc or zero
    for t in range(num):
         for i in V:
             if i != rt:
                neb = Gr.neighbors(i)
                s = str((i,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(quicksum(x[j,i,t] for j in neb) == y[i,t], name="atmostonex%s"% nr)
    #at least one z everytime period
    for i in V:
         if i != rt:
             s = str(i)
             nr = ''.join(i for i in s if i.isdigit())
             model.addCons(quicksum(z[i,t] for t in lnum) >= num+extra, name="atleastonez%s"% nr)
    #forcing y and z
    for t in range(num):
        for i in V:
            if i != rt:
               s = str(i)
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(y[i,t] <= z[i,t], name="yforcez%s"% nr)
               model.addCons(z[i,t] <= 2**(H-1)*y[i,t], name="zforceyz%s"% nr)
    for t in range(num):
             for i in V:
                 if i != rt:
                    neb = Gr.neighbors(i)
                    for w in neb:
                        if w != rt:
                           s = str((i,w,t))
                           nr = ''.join(i for i in s if i.isdigit())
                           model.addCons(z[i,t]-2*z[w,t] +(2**(H-1))*(1-x[i,w,t])>= 0, name="weights%s"% nr) 
    
    model.writeProblem('treemtzcut.lp')
    spx=cplex.Cplex()
    spx.read('treemtzcut.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()
def makeTreeMtznorm(Gr,rt,H,num,cycles):

    cutcoeffs = {}
    ln3 = len(cyclecut3(len(cycles[0])))
    ln7 = len(cyclecut7(len(cycles[0])))
    ln5 = len(cyclecut5(len(cycles[0])))
    lnc = len(cycles)
    C=[0]*lnc
    J3=[0]*ln3
    J7=[0]*ln7
    J5=[0]*ln5
    for i in range(lnc):
        C[i]=i
    for i in range(ln3):
          J3[i]=i
    for i in range(ln5):
          J5[i]=i
    for i in range(ln7):
          J7[i]=i
   

    for c in cycles:
        cutcoeffs[(tuple(c),5)]=cyclecut5(len(c))
        cutcoeffs[(tuple(c),3)]=cyclecut3(len(c))
        cutcoeffs[(tuple(c),7)]=cyclecut7(len(c))
    Hl = [0]*H
    for i in range(H):
        Hl[i]=i
    lnum=[0]*num
    for i in range(num):
        lnum[i]=i
    V=sorted(Gr.nodes())
    # get the edges from graph
    A = Gr.edges()
    # make some dictionaries for values of nodes
    x={}
    z={}
    y={}
    g={}
 
    xinv = {}
    zinv = {}
    yinv = {}
    ginv = {}
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMinimize()
    for c in cycles:
          for i in range(len(cutcoeffs[(tuple(c),3)])):
              s = str((c,i,3))
              nr = ''.join(i for i in s if i.isdigit())
              g[tuple(c),i,3] = model.addVar( vtype='C', obj=sum(cutcoeffs[(tuple(c),3)][i]), lb=0.0,name="g%s"% nr)
              ginv['g'+ nr]=(tuple(c),i,3)
    for c in cycles:
          for i in range(len(cutcoeffs[(tuple(c),5)])):
              s = str((c,i,5))
              nr = ''.join(i for i in s if i.isdigit())
              g[tuple(c),i,5] = model.addVar( vtype='C', obj=sum(cutcoeffs[(tuple(c),5)][i]), lb=0.0,name="g%s"% nr)
              ginv['g'+ nr]=(c,i,5)
    for c in cycles:
          for i in range(len(cutcoeffs[(tuple(c),7)])):
              s = str((c,i,7))
              nr = ''.join(i for i in s if i.isdigit())
              g[tuple(c),i,7] = model.addVar( vtype='C', obj=sum(cutcoeffs[(tuple(c),7)][i]), lb=0.0,name="g%s"% nr)
              ginv['g'+ nr]=(c,i,7)
    for t in range(num):
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            x[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="x%s"% nr)
            xinv['f'+ nr]=(i,j,t)
    for t in range(num):
            for j in V:
                if j != rt:
                   s = str((j,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   z[j,t] = model.addVar(ub = 2**(H-1), vtype='C', obj=1.0, lb=0.0,name="z%s"% nr)
                   zinv['z'+ nr]=(i,t)
    for t in range(num):
            for j in V:
                if j !=rt:
                   s = str((j,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   y[j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="y%s"% nr)
                   yinv['y'+ nr]=(j,t)

   #one incoming arc or zero
    for t in range(num):
         for i in V:
             if i != rt:
                neb = Gr.neighbors(i)
                s = str((i,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(quicksum(x[j,i,t] for j in neb) == y[i,t], name="atmostonex%s"% nr)
    #at least one z everytime period
    for i in V:
         if i != rt:
             s = str(i)
             nr = ''.join(i for i in s if i.isdigit())
             model.addCons(quicksum(z[i,t] for t in lnum) + quicksum(cutcoeffs[(tuple(c),3)][j][c.index(i)]*g[tuple(c),j,3] for c in cycles if i in c for j in makelist(len(cyclecut3(len(c))))) + quicksum(cutcoeffs[(tuple(c),5)][j][c.index(i)]*g[tuple(c),j,5] for c in cycles if i in c for j in  makelist(len(cyclecut5(len(c))))) + quicksum(cutcoeffs[(tuple(c),7)][j][c.index(i)]*g[tuple(c),j,7] for c in cycles if i in c for j in  makelist(len(cyclecut7(len(c))))) >= 1, name="atleastonez%s"% nr)
    #forcing y and z
    for t in range(num):
        for i in V:
            if i != rt:
               s = str(i)
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(y[i,t] <= 100*z[i,t], name="yforcez%s"% nr)
               model.addCons(z[i,t] <= 2**(H-1)*y[i,t], name="zforceyz%s"% nr)
    for t in range(num):
             for i in V:
                 if i != rt:
                    neb = Gr.neighbors(i)
                    for w in neb:
                        if w != rt:
                           s = str((i,w,t))
                           nr = ''.join(i for i in s if i.isdigit())
                           model.addCons(z[i,t]-2*z[w,t] +(2**(H-1))*(1-x[i,w,t])>= 0, name="weights%s"% nr) 
    
    model.writeProblem('treemtzcut.lp')
    spx=cplex.Cplex()
    spx.read('treemtzcut.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()
    
    
    
### input: A product of a graph, which we call (the product) G, a root node which we call rt, a maximum hop size(
### how long at most can each path be in terms or edges or nodes) which we will call H, the number of tree strategies ### which we call num, and how much extra integer cover you want which we will call extra (every node must have a 
### collective coeffiecient of at least 1 + extra) 
###
### output: An upper bound for the rooted pebbling numer of G, where the root is rt, as the value of the objective ### function of the associated mixed integer program in makeTreeMtzsym.. this continues \TODO get each tree and the  ### corresponding coefficients from the solution.
def makeTreeMtzsym(Gr,rt,H,num,extra):
    ## making a list out the number H, now this is made into a function in this module called makelist(n), where n is
    ## a positive integer
    Hl = [0]*H
    for i in range(H):
        Hl[i]=i
    ## making list again...
    lnum=[0]*num
    for i in range(num):
        lnum[i]=i
    ## splitting into even and odd since we are asking for symmetric tree strategies
    lnume= [x for x in lnum if x%2 ==0]
    lnumo= [x for x in lnum if x%2 ==1]
    ## making a sorted list of the graphs' nodes
    V=sorted(Gr.nodes())
    # get the edges from graph
    A = Gr.edges()
    # make some dictionaries for variables
    x={}
    z={}
    y={}
    # also inverse dictionaries to get the index from the variable name
    xinv = {}
    zinv = {}
    yinv = {}
    # scip py opt model declaration
    model = Model()
    # model.hideOutput() # silent/verbose mode
    # want the tighest upper bound 
    model.setMinimize()
    #making the 
    for t in range(num):
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            x[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="x%s"% nr)
            xinv['x'+ nr]=(i,j,t)
    for t in range(num):
            for j in V:
                if j != rt:
                   s = str((j,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   z[j,t] = model.addVar(ub = 2**(H-1), vtype='I', obj=1.0/num, lb=0.0,name="z%s"% nr)
                   zinv['z'+ nr]=(i,t)
    for t in range(num):
            for j in V:
                if j !=rt:
                   s = str((j,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   y[j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="y%s"% nr)
                   yinv['y'+ nr]=(j,t)

   #one incoming arc or zero
    for t in lnume:
         for i in V:
             if i != rt:
                neb = Gr.neighbors(i)
                s = str((i,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(quicksum(x[j,i,t] for j in neb) == y[i,t], name="atmostonex%s"% nr)
    #at least one z everytime period
    for i in V:
         if i != rt:
             s = str(i)
             nr = ''.join(i for i in s if i.isdigit())
             model.addCons(quicksum(z[i,t] for t in lnum) >= num+extra, name="atleastonez%s"% nr)
    #forcing y and z
    for t in lnume:
        for i in V:
            if i != rt:
               s = str(i)
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(y[i,t] <= z[i,t], name="yforcez%s"% nr)
               model.addCons(z[i,t] <= 2**(H-1)*y[i,t], name="zforceyz%s"% nr)
    for t in lnume:
             for i in V:
                 if i != rt:
                    neb = Gr.neighbors(i)
                    for w in neb:
                        if w != rt:
                           s = str((i,w,t))
                           nr = ''.join(i for i in s if i.isdigit())
                           model.addCons(z[i,t]-2*z[w,t] +(2**(H-1))*(1-x[i,w,t])>= 0, name="weights%s"% nr)
    for t in lnume:
             for i in V:
                 if i != rt:
                    s = str((i,t))
                    nr = ''.join(i for i in s if i.isdigit())
                    model.addCons(z[i,t]==z[(i[1],i[0]),lnumo[lnume.index(t)]], name="symm%s"% nr)  
    
    model.writeProblem('treemtzcutsym.lp')
    spx=cplex.Cplex()
    spx.read('treemtzcutsym.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
    justx = [d for d in solz if d[0]=='x']
    keeprow=[]
    for t in lnum:
        tmp = []
        for i in justx:
            if int(i[len(i)-1])==t:
               
               tmp.append((int(i[1]),int(i[2])))
               tmp.append((int(i[3]),int(i[4])))
        print tmp
        keeprow.append(tmp)       
             
        
    #iterm = [xinv[i] for i in solz]
    #print iterm
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()
# same as above instead normalized 
def makelist(l):
    L=[0]*l
    for i in range(l):
        L[i]=i
    return L
        
def justcyclecuts(Gr,rt,cycles,num):
    V=sorted(Gr.nodes())
    # get the edges from graph
    A = Gr.edges()
    # make some dictionaries for values of nodes
    x={}
    xinv = {}
    total=[]
    for c in cycles:
        #a = cyclecut3(len(c))
        #b = cyclecut5(len(c))
        d = cyclecut7(len(c))
        total.append(d)
   
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMinimize()
    for i in range(len(cycles)):
        for j in range(len(total[i])):
           s = str((i,j))
           nr = ''.join(i for i in s if i.isdigit())
           x[i,j] = model.addVar( vtype='C', obj=float(sum(total[i][j]))/num, lb=0.0,name="x%s"% nr)
           xinv['x'+ nr]=(i,j)
    for i in V:
         if i != rt:
             s = str(i)
             nr = ''.join(i for i in s if i.isdigit())
             model.addCons(quicksum(total[j][k][h]*x[j,k] for j in makelist(len(cycles)) for k in makelist(len(total[j])) for h in makelist(len(total[j][k])) if cycles[j][h]==i ) >= num, name="atleastonez%s"% nr)
    model.writeProblem('justcyclecuts.lp')
    spx=cplex.Cplex()
    spx.read('justcyclecuts.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
    iterm = [xinv[i] for i in solz]
    print iterm
    small=[cycles[i] for (i,j) in iterm]
    print spx.solution.get_objective_value()
    return small
def puttrans(total,cycles):
    trans = [30,15,10,15,2.5,5,2.5,float(40.0/31.0)]
    for i in range(len(cycles)):
        total.append(trans)
    return total
      
def justlollicuts(Gr,rt,sink,cycles,ddcycles,d17, num):
    V=sorted(Gr.nodes())
    cikli = cp.deepcopy(cycles)
    d17c = cp.deepcopy(d17)
    # get the edges from graph
    A = Gr.edges()
    # make some dictionaries for values of nodes
    x={}
    xinv = {}
    total=[]
    total1 = makelolliend(Gr,rt,(8,7),d17c)
    total = makelolliend(Gr,rt,sink,cikli)
    total = total + total1
    cikli = cikli + d17c
    #total = puttrans(total,cycles)
    for i in range(len(ddcycles)):
        cikli.append(ddcycles[i])
   
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMinimize()
    for i in range(len(cikli)):
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           x[i] = model.addVar( vtype='C', obj=float(sum(total[i]))/num, lb=0.0,name="x%s"% nr)
           xinv['x'+ nr]=(i)
    for i in V:
         if i != rt:
             s = str(i)
             nr = ''.join(i for i in s if i.isdigit())
             model.addCons(quicksum(total[j][h]*x[j] for j in makelist(len(cikli)) for h in makelist(len(total[j])) if cikli[j][h]==i ) >= num, name="atleastonez%s"% nr)
    model.writeProblem('justcyclecuts.lp')
    spx=cplex.Cplex()
    spx.read('justcyclecuts.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
    print spx.solution.get_objective_value()
    iterm = [xinv[i] for i in solz]
    print iterm
    small=[cycles[i] for (i,j) in iterm]
    return small
    #print [i for i in xinv if spx.solution.get_dual_values(i) != 0]
#cycles in the original formulation with max   
def justlollies(Gr,rt,sink,cycles,d17,dd):
    V=sorted(Gr.nodes())
    cikli = cp.deepcopy(cycles)
    d17c = cp.deepcopy(d17)
    # make some dictionaries for values of nodes
    x={}
    xinv = {}
    total=[]
    total1 = makelolliend(Gr,rt,(8,7),d17c)
    total = makelolliend(Gr,rt,sink,cikli)
    total = total + total1
    
    cikli = cikli + d17c
    total = puttrans(total,dd)
    cikli = cikli + dd
   
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMaximize()
    for i in V:
        if i !=rt:
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           x[i] = model.addVar( vtype='I', obj=1, lb=0.0,name="x%s"% nr)
           xinv['x'+ nr]=(i)  
    for i in range(len(cikli)):
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           model.addCons( quicksum(total[i][j]*x[h] for j in makelist(len(total[i])) for h in V if cikli[i][j]==h) <= sum(total[i]), name="atleastonez%s"% nr)
    model.writeProblem('justcycles.lp')
    spx=cplex.Cplex()
    spx.read('justcycles.lp')
    spx.solve()
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()     
def justcycles(Gr,rt,cycles):
    V=sorted(Gr.nodes())
    # make some dictionaries for values of nodes
    x={}
    xinv = {}
    total=[]
    for c in cycles:
        #a = cyclecut3(len(c))
        #b = cyclecut5(len(c))
        d = cyclecut7(len(c))
        total.append(d)
   
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMaximize()
    for i in V:
        if i !=rt:
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           x[i] = model.addVar( vtype='I', obj=1, lb=0.0,name="x%s"% nr)
           xinv['x'+ nr]=(i)  
    for i in range(len(cycles)):
          for j in range(len(total[i])):
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           model.addCons( quicksum(total[i][j][h]*x[cycles[i][h]] for h in makelist(len(total[i][j]))) <= sum(total[i][j]), name="atleastonez%s"% nr)
    model.writeProblem('justcycles.lp')
    spx=cplex.Cplex()
    spx.read('justcycles.lp')
    spx.solve()
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()     
              
def makeTreeMtzsymnorm(Gr,rt,H,num,cycles):
    lengths = list(set([len(x) for x in cycles]))
    cutcoeffs = {}
    ln3 = len(cyclecut3(len(cycles[0])))
    ln7 = len(cyclecut7(len(cycles[0])))
    ln5 = len(cyclecut5(len(cycles[0])))
    lnc = len(cycles)
    C=[0]*lnc
    J3=[0]*ln3
    J7=[0]*ln7
    J5=[0]*ln5
    for i in range(lnc):
        C[i]=i
    for i in range(ln3):
          J3[i]=i
    for i in range(ln5):
          J5[i]=i
    for i in range(ln7):
          J7[i]=i
   

    for c in cycles:
        cutcoeffs[(tuple(c),5)]=cyclecut5(len(c))
        cutcoeffs[(tuple(c),3)]=cyclecut3(len(c))
        cutcoeffs[(tuple(c),7)]=cyclecut7(len(c))
    Hl = [0]*H
    for i in range(H):
        Hl[i]=i
    
    lnum=[0]*num
    for i in range(num):
        lnum[i]=i
    lnume= [x for x in lnum if x%2 ==0]
    lnumo= [x for x in lnum if x%2 ==1]
    V=sorted(Gr.nodes())
    size_nodes = len(V)
    # get the edges from graph
    A = Gr.edges()
    # get the cardinality of the set of edges
    size_arcs = len(A)
    # make some dictionaries for values of nodes
    x={}
    z={}
    y={}
    g={}
 
    xinv = {}
    zinv = {}
    yinv = {}
    ginv = {}
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMinimize()
    for t in range(num):
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            x[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="x%s"% nr)
            xinv['f'+ nr]=(i,j,t)
    for t in range(num):
            for j in V:
                if j != rt:
                   s = str((j,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   z[j,t] = model.addVar(ub = 2**(H-1), vtype='C', obj=1.0, lb=0.0,name="z%s"% nr)
                   zinv['z'+ nr]=(i,t)
    for t in range(num):
            for j in V:
                if j !=rt:
                   s = str((j,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   y[j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="y%s"% nr)
                   yinv['y'+ nr]=(j,t)
    for c in cycles:
          for i in range(len(cutcoeffs[(tuple(c),3)])):
              s = str((c,i,3))
              nr = ''.join(i for i in s if i.isdigit())
              g[tuple(c),i,3] = model.addVar( vtype='C', obj=sum(cutcoeffs[(tuple(c),3)][i]), lb=0.0,name="g%s"% nr)
              ginv['g'+ nr]=(tuple(c),i,3)
    for c in cycles:
          for i in range(len(cutcoeffs[(tuple(c),5)])):
              s = str((c,i,5))
              nr = ''.join(i for i in s if i.isdigit())
              g[tuple(c),i,5] = model.addVar( vtype='C', obj=sum(cutcoeffs[(tuple(c),5)][i]), lb=0.0,name="g%s"% nr)
              ginv['g'+ nr]=(c,i,5)
    for c in cycles:
          for i in range(len(cutcoeffs[(tuple(c),7)])):
              s = str((c,i,7))
              nr = ''.join(i for i in s if i.isdigit())
              g[tuple(c),i,7] = model.addVar( vtype='C', obj=sum(cutcoeffs[(tuple(c),7)][i]), lb=0.0,name="g%s"% nr)
              ginv['g'+ nr]=(c,i,7)
   #one incoming arc or zero
    for t in lnume:
         for i in V:
             if i != rt:
                neb = Gr.neighbors(i)
                s = str((i,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(quicksum(x[j,i,t] for j in neb) == y[i,t], name="atmostonex%s"% nr)
    #at least one z everytime period
    
    
    for i in V:
         if i != rt:
             s = str(i)
             nr = ''.join(i for i in s if i.isdigit())
             model.addCons(quicksum(z[i,t] for t in lnum) + quicksum(cutcoeffs[(tuple(c),3)][j][c.index(i)]*g[tuple(c),j,3] for c in cycles if i in c for j in makelist(len(cyclecut3(len(c))))) + quicksum(cutcoeffs[(tuple(c),5)][j][c.index(i)]*g[tuple(c),j,5] for c in cycles if i in c for j in  makelist(len(cyclecut5(len(c))))) + quicksum(cutcoeffs[(tuple(c),7)][j][c.index(i)]*g[tuple(c),j,7] for c in cycles if i in c for j in  makelist(len(cyclecut7(len(c))))) >= 1, name="atleastonez%s"% nr)
    #forcing y and z
    for t in lnume:
        for i in V:
            if i != rt:
               s = str(i)
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(y[i,t] <= 100*z[i,t], name="yforcez%s"% nr)
               model.addCons(z[i,t] <= 2**(H-1)*y[i,t], name="zforceyz%s"% nr)
    for t in lnume:
             for i in V:
                 if i != rt:
                    neb = Gr.neighbors(i)
                    for w in neb:
                        if w != rt:
                           s = str((i,w,t))
                           nr = ''.join(i for i in s if i.isdigit())
                           model.addCons(z[i,t]-2*z[w,t] +(2**(H-1))*(1-x[i,w,t])>= 0, name="weights%s"% nr)
    for t in lnume:
             for i in V:
                 if i != rt:
                    s = str((i,t))
                    nr = ''.join(i for i in s if i.isdigit())
                    model.addCons(z[i,t]==z[(i[1],i[0]),lnumo[lnume.index(t)]], name="symm%s"% nr)  
    
    model.writeProblem('treemtzcutsym.lp')
    spx=cplex.Cplex()
    spx.read('treemtzcutsym.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()
def makeTreeMtzsymnorml(Gr,rt,sink,H,num,cycles):
    lengths = list(set([len(x) for x in cycles]))
    cutcoeffs = {}
    cikli = cp.deepcopy(cycles)
    total = makelolliend(Gr,rt,sink,cikli)
    Hl = [0]*H
    for i in range(H):
        Hl[i]=i
    
    lnum=[0]*num
    for i in range(num):
        lnum[i]=i
    lnume= [x for x in lnum if x%2 ==0]
    lnumo= [x for x in lnum if x%2 ==1]
    V=sorted(Gr.nodes())
    size_nodes = len(V)
    # get the edges from graph
    A = Gr.edges()
    # get the cardinality of the set of edges
    size_arcs = len(A)
    # make some dictionaries for values of nodes
    x={}
    z={}
    y={}
    g={}
 
    xinv = {}
    zinv = {}
    yinv = {}
    ginv = {}
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMinimize()
    for t in range(num):
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            x[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="x%s"% nr)
            xinv['f'+ nr]=(i,j,t)
    for t in range(num):
            for j in V:
                if j != rt:
                   s = str((j,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   z[j,t] = model.addVar(ub = 2**(H-1), vtype='C', obj=1.0, lb=0.0,name="z%s"% nr)
                   zinv['z'+ nr]=(i,t)
    for t in range(num):
            for j in V:
                if j !=rt:
                   s = str((j,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   y[j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="y%s"% nr)
                   yinv['y'+ nr]=(j,t)
    for  i in range(len(cikli)):
        s = str(i)
        nr = ''.join(i for i in s if i.isdigit())
        g[i] = model.addVar( vtype='C', obj=sum(total[i]), lb=0.0,name="g%s"% nr)
        ginv[i]=(i)
   
    for t in lnume:
         for i in V:
             if i != rt:
                neb = Gr.neighbors(i)
                s = str((i,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(quicksum(x[j,i,t] for j in neb) == y[i,t], name="atmostonex%s"% nr)
    #at least one z everytime period
    
    
    for i in V:
         if i != rt:
             s = str(i)
             nr = ''.join(i for i in s if i.isdigit())
             model.addCons(quicksum(z[i,t] for t in lnum) + quicksum(total[j][h]*g[j] for j in makelist(len(cikli)) for h in makelist(len(total[j])) if cikli[j][h]==i)  >= 1, name="atleastonez%s"% nr)
    #forcing y and z
    for t in lnume:
        for i in V:
            if i != rt:
               s = str(i)
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(y[i,t] <= 100*z[i,t], name="yforcez%s"% nr)
               model.addCons(z[i,t] <= 2**(H-1)*y[i,t], name="zforceyz%s"% nr)
    for t in lnume:
             for i in V:
                 if i != rt:
                    neb = Gr.neighbors(i)
                    for w in neb:
                        if w != rt:
                           s = str((i,w,t))
                           nr = ''.join(i for i in s if i.isdigit())
                           model.addCons(z[i,t]-2*z[w,t] +(2**(H-1))*(1-x[i,w,t])>= 0, name="weights%s"% nr)
    for t in lnume:
             for i in V:
                 if i != rt:
                    s = str((i,t))
                    nr = ''.join(i for i in s if i.isdigit())
                    model.addCons(z[i,t]==z[(i[1],i[0]),lnumo[lnume.index(t)]], name="symm%s"% nr)  
    
    model.writeProblem('treemtzcutsym.lp')
    spx=cplex.Cplex()
    spx.read('treemtzcutsym.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()                  
def makeTreeSHopBound(Gr,rt,H,num,B,fixed,extra):
    Hl = [0]*H
    for i in range(H):
        Hl[i]=i
    lnum=[0]*num
    for i in range(num):
        lnum[i]=i
    V=sorted(Gr.nodes())
    size_nodes = len(V)
    # get the edges from graph
    A = Gr.edges()
    # get the cardinality of the set of edges
    size_arcs = len(A)
    # make some dictionaries for values of nodes
    l={}
    x={}
    z={}
    g={}
    linv ={}
    xinv = {}
    zinv = {}
    ginv = {}
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMinimize()
    for t in range(num):
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            x[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="x%s"% nr)
            xinv['f'+ nr]=(i,j,t)

    for t in range(num):
        for i in range(H):
            for j in V:
                s = str((i,j,t))
                nr = ''.join(i for i in s if i.isdigit())
                g[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="g%s"% nr)
                ginv['g'+ nr]=(i,j,t)

    for t in range(num):
            for j in V:
                if j != rt:
                   s = str((j,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   z[j,t] = model.addVar(ub = 2**(H-1), vtype='C', obj=1.0, lb=0.0,name="z%s"% nr)
                   zinv['z'+ nr]=(i,t)
    
    for t in range(num):
        for i in range(H):
            for j in V:
                s = str((j,i,t))
                nr = ''.join(i for i in s if i.isdigit())
                l[j,i,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="l%s"% nr)
                linv['l'+ nr]=(j,i,t)

    # fix roots constraint for every time period
    for t in range(num):
        s = str(t)
        nr = ''.join(i for i in s if i.isdigit())
        model.addCons(l[rt,0,t] == 0, name="rootfixl%s"% nr)
        model.addCons(g[0,rt,t] == 0, name="rootfixg%s"% nr)
    
    # all the other nodes fixed somewhere in between
    for t in range(num):      
        for j in V:
            if j != rt:
               s = str((j,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(l[j,1,t] == 0, name="allothernodesfixedls%s"% nr)
               model.addCons(g[H-1,j,t] == 0, name="allothernodesfixedgs%s"% nr)

    # trasitivity greater
    for t in range(num):
        for i in range(H-1):
            for j in V:
                s = str((i,j,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(g[i,j,t] - g[i+1,j,t] >= 0, name="transgreat%s"% nr)

    # each node either greater than i or less than i+1 not both
    for t in range(num):
        for i in range(H-1):
            for j in V:
                s = str((i,j,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(g[i,j,t] + l[j,i+1,t] == 1, name="lgnotboth%s"% nr)

    # forcing the direction of x_(i,j) or x_(j,i) in the chosen tree
    for t in range(num):
        for h in range(H):
            keepsi = [False]*len(A)
            for (i,j) in A:
                ind = A.index((i,j))
                if not keepsi[ind]:
                       keepsi[ind] = True
                       indrev =  A.index((j,i))
                       keepsi[indrev] = True
                       s = str((i,j,h,t))
                       nr = ''.join(i for i in s if i.isdigit())
                       srev = str((j,i,h,t))
                       nrev = ''.join(i for i in srev if i.isdigit())
                       model.addCons(l[i,h,t] + g[h,j,t]- x[i,j,t] >= 0, name="lgxij%s"% nr)
                       model.addCons(l[j,h,t] + g[h,i,t]- x[j,i,t] >= 0, name="lgxji%s"% nrev)

     #at most one incoming arc
    for t in range(num):
         for i in V:
             if i != rt:
                neb = Gr.neighbors(i)
                s = str((i,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(quicksum(x[j,i,t] for j in neb) <= 1, name="atmostonex%s"% nr)
    for i in V:
       if i != rt:
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           model.addCons(quicksum(x[j,i,t] for j in V if (j,i) in A for t in lnum) >= 1, name="stonex%s"% nr)
                



     #connectee tree
    for t in range(num):
         for i in V:
             if i != rt:
                neb = Gr.neighbors(i)
                for w in neb:
                    s = str((i,w,t))
                    nr = ''.join(i for i in s if i.isdigit())
                    model.addCons(quicksum(x[j,i,t] for j in neb if j != w)  - x[i,w,t] >= 0, name="conntrex%s"% nr)


    
     #forcing a z with an ordering of nodes
    #for t in range(num):
         #for h in range(H):
             #for i in V:
                 #if i != rt:
                   # s = str((i,h,t))
                    #nr = ''.join(i for i in s if i.isdigit())
                    #model.addCons(1 - l[i,h,t] - g[h,i,t] - z[i,h,t] <= 0, name="lgforcex%s"% nr)
    
   
     #z forces l,g variables
    for t in range(num):
         for (i,j) in A:
             if j != rt:
                s = str((i,j,t))
                nr = ''.join(i for i in s if i.isdigit())
                model.addCons(x[i,j,t] - z[j,t] <= 0, name="xforcez%s"% nr)
             

    for t in range(num):
          for i in V:
             if i != rt:
                 neb = Gr.neighbors(i)
                 s = str((i,t))
                 nr = ''.join(i for i in s if i.isdigit())
                 model.addCons(-(2**(H-1))*quicksum(x[w,i,t] for w in neb)+ z[i,t] <= 0, name="zforcex%s"% nr)
           
     #weights on the paths
    for t in range(num):
             for i in V:
                 if i != rt:
                    neb = Gr.neighbors(i)
                    for w in neb:
                        if w != rt:
                           s = str((i,w,h,t))
                           nr = ''.join(i for i in s if i.isdigit())
                           model.addCons(z[i,t]-2*z[w,t] +(2**(H-1))*(1-x[i,w,t])>= 0, name="weights%s"% nr)  

     #forcing x from l and g
    #for t in range(num):
         #for h in range(H):
            # for i in V:
                # if i != rt:
                   # s = str((i,h,t))
                   # nr = ''.join(i for i in s if i.isdigit())
                   # model.addCons(1 - l[i,h,t]-g[h,i,t] - quicksum(x[i,j,t] for j in V if (i,j) in A) - quicksum(x[j,i,t] for j in V if (j,i) in A) <= 0,name="forcexlg%s"% nr)   

    #fixing some variables
    for t in range(num):
        for i in V:
            if i != rt:
               lngth = nx.shortest_path_length(Gr,source = rt, target = i)
               if lngth <= H:
                  s = str((i,t))
                  nr = ''.join(i for i in s if i.isdigit())
                  model.addCons(g[lngth-1,i,t]==1,name="fixg%s"% nr)
    #another fixing
    

               
     #at least one z everytime period
    for i in V:
         if i != rt and fixed[V.index(i)] >= 0:
             s = str(i)
             nr = ''.join(i for i in s if i.isdigit())
             model.addCons(quicksum(z[i,t] for t in lnum) >= num + extra, name="atleastonez%s"% nr)

    
    #model.addCons(quicksum(z[i,h,t] for h in Hl for t in lnum for i in V if i !=rt) <= 428, name="bounad")
    for t in range(num):
          model.addCons(0.5*quicksum(x[i,j,t] for (i,j) in A) + 0.5*quicksum(x[j,i,t] for (i,j) in A) <= B, name="numberofedgesnodes")
    #model.addCons(z[(1,2),1,0]==32, name="f1")
    #model.addCons(z[(2,1),1,1]==32, name="f2")
    #model.addCons(z[(3,1),1,2]==32, name="f3")
    #model.addCons(z[(1,3),1,3]==32, name="f4")
    model.writeProblem('treecut.lp')  
    spx=cplex.Cplex()
    spx.read('treecut.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()
   

#find even cycle cover, this is how we will heuristically make lollipops
def makeBunchEvenCycles(G,rt,sink,T,l,up):
    keeps = []
    Gr=cp.deepcopy(G)
    Gr.remove_node(rt)
    for i in range(l+1,up):
        print 'we are here'
        print i
        thenodes=[]
        for j in Gr.nodes():
            print 'this is the node'
            print j
            if len(nx.shortest_path(G,rt,j)) == i:
               print i
               print 'hehhehee'
               tmp = findCyclesEven(Gr,sink,j,T,up*2 - (i-1)*2)
               if tmp:
                  keeps.append(tmp)
    fin =[]
    for h in range(len(keeps)):
        fin = fin + keeps[h]
               
    return fin     
def makeBunchEvenCyclespec(G,rt,sink,level,size,T):
    keeps = []
    Gr=cp.deepcopy(G)
    Gr.remove_node(rt)
    for i in range(level+1,level+2):
        print 'we are here'
        print i
        thenodes=[]
        for j in Gr.nodes():
            print 'this is the node'
            print j
            if len(nx.shortest_path(G,rt,j)) == i:
               print i
               print 'hehhehee'
               tmp = findCyclesEven(Gr,sink,j,T,size)
               tmp.append(j)
               if tmp:
                  keeps.append(tmp)
               
    return keeps  
def makedoublecycles(G,rt,sink,cycles):
    keeps = {}
    Gr=cp.deepcopy(G)
    Gr.remove_node(rt)
    cikli = cp.deepcopy(cycles)
    for j in range(len(cikli)):
        for k in range(len(cikli[j])):
            if k != len(cikli[j]) -1:
               which = cikli[j][k][(len(cikli[j][k])+1)/2 -1]
               neigh = G.neighbors(which)
               thenodes=[]
               for i in neigh:
                   if i != rt:
                      tmp = findCyclesEven(Gr,sink,i,makelist(10),4)
                      if tmp:
                         keeps[(cikli[j][len(cikli[j]) -1],which,i)]=tmp
                  
   
    return keeps 

def mashthemup(G,rt,sink,dictionary,cycles):
    fin = []
    tryme = []
    cikli = cp.deepcopy(cycles)
   
    for key in dictionary.keys():
        tryme.append(key)
    for j in range(len(cikli)):
        for k in range(len(cikli[j])):
            if k != len(cikli[j]) -1:
               which = cikli[j][k][(len(cikli[j][k])+1)/2 -1]
               neigh = G.neighbors(which)
               ult = cikli[j][len(cikli[j]) -1]
               count = 0
               for i in neigh:
                   if i != rt:
                      if (ult,which,i) in tryme:
                          kpr = dictionary[(ult,which,i)]
                          kpr1 = cp.deepcopy(kpr)
                          if count == 0:
                             cikli[j][k].insert(0,ult)
                          count = count +1
                          
                          for v in range(len(kpr)):
                              kpr1[v].append(sink)
                              
                              fin.append(cikli[j][k]+kpr1[v])
    return fin        
        
     
           
    
## the rt in this case should be the top (8,8), and the sink is the closed to the root, backwardss!   

def findCyclesEven(Gr,rt,sink,T,ubound):
    V=sorted(Gr.nodes())
    size_nodes = len(V)
    # get the edges from graph
    A = Gr.edges()
    # get the cardinality of the set of edges
    size_arcs = len(A)
    # make some dictionaries for values of nodes
    numb_to_V_dict = {}
    V_to_numb_dict = {}
    numb_to_V = zip(range(1,size_nodes + 1), V)
    V_to_numb = zip(V, range(1,size_nodes + 1))
    for i, j in numb_to_V:
        numb_to_V_dict[i] = j
    for i, j in V_to_numb:
        V_to_numb_dict[i] = j
    W = [0]*len(V)
    x={}
    z={}
    zinv={}
    xinv = {}
    y={}
    f={}
    finv={}
    yinv={}
    justx=[]
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMaximize()
    total = len(V)
    for t in T:
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            x[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="x%s"% nr)
            xinv['x'+ nr]=(i,j,t)
            justx.append('x'+nr)
    for t in T:
            s = str((t))
            nr = ''.join(i for i in s if i.isdigit())
            f[t]=model.addVar( vtype='I', obj=0.0, lb=0.0,name="f%s"% nr)
            finv['f' + nr]=(t)
      
            
    for i in V:
        if i != rt:
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           y[i] = model.addVar( vtype='B', obj=1.0, lb=0.0,name="y%s"% nr)
           yinv['y'+ nr]=(i)
    for t in T:
        for j in V:
            s = str((j,t))
            nr = ''.join(i for i in s if i.isdigit())
            z[j,t] = model.addVar(ub = size_nodes, vtype='I', obj=0.0, lb=0.0,name="z%s"% nr)
            zinv['z'+ nr]=(i,t)
    for t in T:
        for i in V:
            if i != rt and i != sink:
               neb = Gr.neighbors(i)
               s = str((i,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(quicksum(x[j,i,t] for j in neb) <= 1, name="atmostonex%s"% nr)
            else:
               neb = Gr.neighbors(i)
               s = str((i,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(quicksum(x[j,i,t] for j in neb) == 1, name="atmostonex%s"% nr)
    for t in T:
        for i in V:
            neb = Gr.neighbors(i)
            s = str((i,t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(quicksum(x[j,i,t] for j in V if (j,i) in A)==quicksum(x[i,j,t] for j in V if (i,j) in A),name="flowbalace%s"% nr)
    for t in T:
        for i in V:
            if i != rt:
               neb = Gr.neighbors(i)
               for w in neb:
                   s = str((i,w,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   model.addCons(z[i,t]- z[w,t] -1 +(size_nodes)*(1-x[i,w,t])>= 0, name="weights%s"% nr)
    for t in T:
        for (i,j) in A:
            if i !=rt:
               s = str((i,j,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(x[i,j,t] <= z[i,t], name="forcepre%s"% nr)
               model.addCons(x[i,j,t] <= z[j,t], name="forceante%s"% nr)
    for t in T:
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(x[i,j,t] + x[j,i,t] <= 1, name="onlyonearc%s"% nr)

   
 
    for t in T:
            s = str((t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(quicksum(x[i,j,t] for (i,j) in A) <= ubound, name="nomorethan12%s"% nr)
    for t in T:
            s = str((t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(quicksum(x[i,j,t] for (i,j) in A) == 2*f[t], name="even%s"% nr)
              
    for i in V:
        if i != rt:
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           model.addCons(quicksum(x[i,j,t] for t in T for j in V if (i,j) in A) >=y[i], name="atleastonexpert%s"% nr)
           
            
        
    model.writeProblem('findcycleseven.lp')  
    spx=cplex.Cplex()
    spx.read('findcycleseven.lp')
    #spx.parameters.emphasis.mip.set(1)
    spx.parameters.mip.polishafter.time.set(200)
    spx.parameters.workmem.set(500)
    spx.parameters.mip.strategy.file.set(3)
    spx.parameters.mip.pool.relgap.set(0.05)
    spx.parameters.mip.limits.populate.set(3000)
    spx.parameters.mip.pool.replace.set(2)
    spx.parameters.mip.pool.capacity.set(50)
    #spx.parameters.timelimit.set(500)
    spx.populate_solution_pool()
    fin=[]
    print spx.solution.get_status()
    if spx.solution.get_status() != 103 and spx.solution.get_status() != 108:
       solz = access_solution_values(spx,xinv)
       solz = spx.solution.pool

       numsol = solz.get_num()
       
       for k in range(numsol):
           sol = solz.get_values(k,justx)
           sol1=[xinv[x] for x in xinv if sol[justx.index('x'+''.join(i for i in str(x) if i.isdigit()))]==1]
           sort_sol1=[]
           for t in T:
               sort_sol1.append([x for x in sol1 if x[2]==t])
           for t in T:
               kps = [rt]
               while len(kps) < len(sort_sol1[t]):
                     for i in sort_sol1[t]:
                         if i[0]==kps[len(kps)-1] and i[1]!=rt:
                            kps.append(i[1])
               kps.remove(rt) 
               fin.append(kps)
    fin_set=set(sorted(tuple(x) for x in fin))
    fin_un=[list(x) for x in fin_set]
    
    
    return fin_un
# let's make some cycle cuts first one with 5 5 5 5
def cyclecut5(lngth):
    #rotations of the cuts
    num = lngth - 4
    keeper = []
    for i in range(num+1):
        kps=[0]*lngth
        kps[i]=6
        kps[i+1]=5
        kps[i+2]=5
        kps[i+3]=6
        for j in range(i):
            kps[j]=14*(2**(i-1-j))
        for k in range(i+4,lngth):
            kps[k]=14*(2**(k-i-4))
        keeper.append(kps)
    return keeper

def cyclecut3(lngth):
    #rotations of the cuts
    num = lngth - 4
    keeper = []
    for i in range(num+1):
        kps=[0]*lngth
        kps[i]=1
        kps[i+1]=1
        kps[i+2]=1
        kps[i+3]=1
        for j in range(i):
            kps[j]=3*(2**(i-1-j))
        for k in range(i+4,lngth):
            kps[k]=3*(2**(k-i-4))
        keeper.append(kps)
    return keeper

def cyclecut7(lngth):
    #rotations of the cuts
    num = lngth - 5
    keeper = []
    for i in range(num+1):
        kps=[0]*lngth
        kps[i]=1
        kps[i+1]=1
        kps[i+2]=2
        kps[i+3]=4
        kps[i+4]=7
        for j in range(i):
            kps[j]=2*(2**(i-1-j))
        for k in range(i+5,lngth):
            kps[k]=16*(2**(k-i-5))
        kps1 = kps[:]
        kps.reverse()
        keeper.append(kps1)
        keeper.append(kps)
    return keeper
       
def makesymcycle(cycles):
    total = []
    for i in cycles:
        tmp = [(j,k) for (k,j) in i] 
        total.append(i)
        total.append(tmp)
    return total 
    
def makelolliend(G,rt,sink,cycles):
    coeffs=[]
    for i in cycles:
        coeffsi=[]
        t = ((len(i)+1)/2)
        print t
        three = i[t-1]
        print three
        route = nx.shortest_path(G,rt,three)
        s = t + len(route)-2
        print s
        for j in range(len(route)-1):
            if j >= 1:
               print 'here'
               print j
               coff= 2**(s+1-j)
               print coff
               coeffsi.append(coff)
        for k in range(t-1):
            coff = 2**(k+1)
            coeffsi.append(coff)
        for h in range(t-1,len(i)):
            coff = 2**(t-(h+1-t))
            coeffsi.append(coff)
        for v in range(len(route)-1):
            if v >= 1:
               i.insert(v-1,route[v])
        coeffsi.append(float((2**s + 2**(t-1) -2))/float((2**s -1)))
        i.append(sink)
        coeffs.append(coeffsi)
    return coeffs
        

def findCycles(Gr,rt,sink,T,bound):
    V=sorted(Gr.nodes())
    size_nodes = len(V)
    # get the edges from graph
    A = Gr.edges()
    # get the cardinality of the set of edges
    size_arcs = len(A)
    # make some dictionaries for values of nodes
    numb_to_V_dict = {}
    V_to_numb_dict = {}
    numb_to_V = zip(range(1,size_nodes + 1), V)
    V_to_numb = zip(V, range(1,size_nodes + 1))
    for i, j in numb_to_V:
        numb_to_V_dict[i] = j
    for i, j in V_to_numb:
        V_to_numb_dict[i] = j
    W = [0]*len(V)
    x={}
    z={}
    zinv={}
    xinv = {}
    y={}
    yinv={}
    justx=[]
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMaximize()
    total = len(V)
    for t in T:
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            x[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="x%s"% nr)
            xinv['x'+ nr]=(i,j,t)
            justx.append('x'+nr)
    for i in V:
        if i != rt:
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           y[i] = model.addVar( vtype='B', obj=1.0, lb=0.0,name="y%s"% nr)
           yinv['y'+ nr]=(i)
    for t in T:
        for j in V:
            s = str((j,t))
            nr = ''.join(i for i in s if i.isdigit())
            z[j,t] = model.addVar(ub = size_nodes, vtype='I', obj=0.0, lb=0.0,name="z%s"% nr)
            zinv['z'+ nr]=(i,t)
    for t in T:
        for i in V:
            if i != rt and i != sink:
               neb = Gr.neighbors(i)
               s = str((i,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(quicksum(x[j,i,t] for j in neb) <= 1, name="atmostonex%s"% nr)
            else:
               neb = Gr.neighbors(i)
               s = str((i,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(quicksum(x[j,i,t] for j in neb) == 1, name="atmostonex%s"% nr)
    for t in T:
        for i in V:
            neb = Gr.neighbors(i)
            s = str((i,t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(quicksum(x[j,i,t] for j in V if (j,i) in A)==quicksum(x[i,j,t] for j in V if (i,j) in A),name="flowbalace%s"% nr)
    for t in T:
        for i in V:
            if i != rt:
               neb = Gr.neighbors(i)
               for w in neb:
                   s = str((i,w,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   model.addCons(z[i,t]- z[w,t] -1 +(size_nodes)*(1-x[i,w,t])>= 0, name="weights%s"% nr)
    for t in T:
        for (i,j) in A:
            if i !=rt:
               s = str((i,j,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(x[i,j,t] <= z[i,t], name="forcepre%s"% nr)
               model.addCons(x[i,j,t] <= z[j,t], name="forceante%s"% nr)
    for t in T:
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(x[i,j,t] + x[j,i,t] <= 1, name="onlyonearc%s"% nr)

    for t in T:
            s = str((t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(quicksum(x[i,j,t] for (i,j) in A) >= 5, name="atleast5%s"% nr)
 
    for t in T:
            s = str((t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(quicksum(x[i,j,t] for (i,j) in A) <= bound, name="nomorethan12%s"% nr)
              
    for i in V:
        if i != rt:
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           model.addCons(quicksum(x[i,j,t] for t in T for j in V if (i,j) in A) >=y[i], name="atleastonexpert%s"% nr)
           
            
        
    model.writeProblem('findcycles.lp')  
    spx=cplex.Cplex()
    spx.parameters.emphasis.mip.set(1)
    spx.parameters.mip.polishafter.time.set(500)
    spx.read('findcycles.lp')
    spx.parameters.workmem.set(500)
    spx.parameters.mip.strategy.file.set(3)
    spx.parameters.mip.pool.relgap.set(0.05)
    spx.parameters.mip.limits.populate.set(10000)
    spx.parameters.mip.pool.replace.set(2)
    spx.parameters.mip.pool.capacity.set(2000)
    spx.populate_solution_pool()
    #solz = access_solution_values(spx,xinv)
    solz = spx.solution.pool
    #print solz
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()
    numsol = solz.get_num()
    print numsol
    fin=[]
    for k in range(numsol):
        sol = solz.get_values(k,justx)
        sol1=[xinv[x] for x in xinv if sol[justx.index('x'+''.join(i for i in str(x) if i.isdigit()))]==1]
        sort_sol1=[]
        for t in T:
            sort_sol1.append([x for x in sol1 if x[2]==t])
        for t in T:
            kps = [rt]
            while len(kps) < len(sort_sol1[t]):
                  for i in sort_sol1[t]:
                      if i[0]==kps[len(kps)-1] and i[1]!=rt:
                         kps.append(i[1])
            kps.remove(rt) 
            fin.append(kps)
    return fin
def findCyclesf(Gr,rt,sink,T,fix1,fix2,bound):
    V=sorted(Gr.nodes())
    size_nodes = len(V)
    # get the edges from graph
    A = Gr.edges()
    # get the cardinality of the set of edges
    size_arcs = len(A)
    # make some dictionaries for values of nodes
    numb_to_V_dict = {}
    V_to_numb_dict = {}
    numb_to_V = zip(range(1,size_nodes + 1), V)
    V_to_numb = zip(V, range(1,size_nodes + 1))
    for i, j in numb_to_V:
        numb_to_V_dict[i] = j
    for i, j in V_to_numb:
        V_to_numb_dict[i] = j
    W = [0]*len(V)
    x={}
    z={}
    zinv={}
    xinv = {}
    y={}
    yinv={}
    justx=[]
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMaximize()
    total = len(V)
    for t in T:
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            x[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="x%s"% nr)
            xinv['x'+ nr]=(i,j,t)
            justx.append('x'+nr)
    for i in V:
        if i != rt:
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           y[i] = model.addVar( vtype='B', obj=1.0, lb=0.0,name="y%s"% nr)
           yinv['y'+ nr]=(i)
    for t in T:
        for j in V:
            s = str((j,t))
            nr = ''.join(i for i in s if i.isdigit())
            z[j,t] = model.addVar(ub = size_nodes, vtype='I', obj=0.0, lb=0.0,name="z%s"% nr)
            zinv['z'+ nr]=(i,t)
    for t in T:
        for i in V:
            if i != rt and i != sink and i!= fix1 and i!=fix2:
               neb = Gr.neighbors(i)
               s = str((i,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(quicksum(x[j,i,t] for j in neb) <= 1, name="atmostonex%s"% nr)
            else:
               neb = Gr.neighbors(i)
               s = str((i,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(quicksum(x[j,i,t] for j in neb) == 1, name="atmostonex%s"% nr)
    for t in T:
        for i in V:
            neb = Gr.neighbors(i)
            s = str((i,t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(quicksum(x[j,i,t] for j in V if (j,i) in A)==quicksum(x[i,j,t] for j in V if (i,j) in A),name="flowbalace%s"% nr)
    for t in T:
        for i in V:
            if i != rt:
               neb = Gr.neighbors(i)
               for w in neb:
                   s = str((i,w,t))
                   nr = ''.join(i for i in s if i.isdigit())
                   model.addCons(z[i,t]- z[w,t] -1 +(size_nodes)*(1-x[i,w,t])>= 0, name="weights%s"% nr)
    for t in T:
        for (i,j) in A:
            if i !=rt:
               s = str((i,j,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(x[i,j,t] <= z[i,t], name="forcepre%s"% nr)
               model.addCons(x[i,j,t] <= z[j,t], name="forceante%s"% nr)
    for t in T:
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(x[i,j,t] + x[j,i,t] <= 1, name="onlyonearc%s"% nr)

    for t in T:
            s = str((t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(quicksum(x[i,j,t] for (i,j) in A) >= 5, name="atleast5%s"% nr)
 
    for t in T:
            s = str((t))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(quicksum(x[i,j,t] for (i,j) in A) <= bound, name="nomorethan12%s"% nr)
              
    for i in V:
        if i != rt:
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           model.addCons(quicksum(x[i,j,t] for t in T for j in V if (i,j) in A) >=y[i], name="atleastonexpert%s"% nr)
           
            
        
    model.writeProblem('findcycles.lp')  
    spx=cplex.Cplex()
    spx.parameters.emphasis.mip.set(1)
    spx.parameters.mip.polishafter.time.set(500)
    spx.read('findcycles.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()
    sol = spx.solution.get_values(justx)
    sol1=[xinv[x] for x in xinv if sol[justx.index('x'+''.join(i for i in str(x) if i.isdigit()))]==1]
    sort_sol1=[]
    for t in T:
        sort_sol1.append([x for x in sol1 if x[2]==t])
    fin=[]
    for t in T:
        kps = [rt]
        while len(kps) < len(sort_sol1[t]):
              for i in sort_sol1[t]:
                  if i[0]==kps[len(kps)-1] and i[1]!=rt:
                     kps.append(i[1])
        kps.remove(rt) 
        fin.append(kps)
    return fin

def findCycle(Gr,rt,end):
    V=sorted(Gr.nodes())
    size_nodes = len(V)
    # get the edges from graph
    A = Gr.edges()
    # get the cardinality of the set of edges
    size_arcs = len(A)
    # make some dictionaries for values of nodes
    numb_to_V_dict = {}
    V_to_numb_dict = {}
    numb_to_V = zip(range(1,size_nodes + 1), V)
    V_to_numb = zip(V, range(1,size_nodes + 1))
    for i, j in numb_to_V:
        numb_to_V_dict[i] = j
    for i, j in V_to_numb:
        V_to_numb_dict[i] = j
    W = [0]*len(V)
    x={}
    z={}
    zinv={}
    xinv = {}
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMinimize()
    total = len(V)
    for (i,j) in A:
        s = str((i,j))
        nr = ''.join(i for i in s if i.isdigit())
        x[i,j] = model.addVar( vtype='B', obj=1.0, lb=0.0,name="x%s"% nr)
        xinv['x'+ nr]=(i,j)
    for j in V:
        s = str((j))
        nr = ''.join(i for i in s if i.isdigit())
        z[j] = model.addVar(ub = size_nodes, vtype='I', obj=0.0, lb=0.0,name="z%s"% nr)
        zinv['z'+ nr]=(i)
    for i in V:
        if i != rt and i != end:
           neb = Gr.neighbors(i)
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           model.addCons(quicksum(x[j,i] for j in neb) <= 1, name="atmostonex%s"% nr)
        else:
           neb = Gr.neighbors(i)
           s = str((i))
           nr = ''.join(i for i in s if i.isdigit())
           model.addCons(quicksum(x[j,i] for j in neb) == 1, name="atmostonex%s"% nr)
    for i in V:
        neb = Gr.neighbors(i)
        s = str((i))
        nr = ''.join(i for i in s if i.isdigit())
        model.addCons(quicksum(x[j,i] for j in V if (j,i) in A)==quicksum(x[i,j] for j in V if (i,j) in A),name="flowbalace%s"% nr)
    for i in V:
        if i != rt:
           neb = Gr.neighbors(i)
           for w in neb:
               s = str((i,w))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(z[i]- z[w] -1 +(size_nodes)*(1-x[i,w])>= 0, name="weights%s"% nr)
    for (i,j) in A:
         if i !=rt:
            s = str((i,j))
            nr = ''.join(i for i in s if i.isdigit())
            model.addCons(x[i,j] <= z[i], name="forcepre%s"% nr)
            model.addCons(x[i,j] <= z[j], name="forceante%s"% nr)
            
        
    model.writeProblem('findcycle.lp')  
    spx=cplex.Cplex()
    spx.read('findcycle.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
    print spx.solution.get_objective_value()
    print spx.solution.MIP.get_best_objective()            
def makeTreeBound(Gr,rt,lnum):
    num = len(lnum)
    # get the nodes from graph
    #nx.draw(Gr,pos=nx.spring_layout(Gr),with_labels=True)
    #plt.show()
    V=sorted(Gr.nodes())
    size_nodes = len(V)
    # get the edges from graph
    A = Gr.edges()
    # get the cardinality of the set of edges
    size_arcs = len(A)
    # make some dictionaries for values of nodes
    numb_to_V_dict = {}
    V_to_numb_dict = {}
    numb_to_V = zip(range(1,size_nodes + 1), V)
    V_to_numb = zip(V, range(1,size_nodes + 1))
    for i, j in numb_to_V:
        numb_to_V_dict[i] = j
    for i, j in V_to_numb:
        V_to_numb_dict[i] = j
    W = [0]*len(V)
    f={}
    x={}
    y={}
    z={}
    g={}
    finv ={}
    xinv = {}
    yinv = {}
    zinv = {}
    ginv = {}
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMinimize()
    total = len(V)
    for t in range(num):
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            f[i,j,t] = model.addVar(ub = 64, vtype='I', obj=0.0, lb=0.0,name="f%s"% nr)
            finv['f'+ nr]=(i,j,t)

    for t in range(num):
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            g[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="g%s"% nr)
            ginv['g'+ nr]=(i,j,t)

    for t in range(num):
        for (i,j) in A:
            s = str((i,j,t))
            nr = ''.join(i for i in s if i.isdigit())
            z[i,j,t] = model.addVar( vtype='B', obj=0.0, lb=0.0,name="z%s"% nr)
            zinv['z'+ nr]=(i,j,t)
    for t in range(num):
        for i in V:
            if i != rt:
               s = str((i,t))
               nr = ''.join(i for i in s if i.isdigit())
               x[i,t] = model.addVar(ub = None, vtype='I', obj=1.0, lb=0.0,name="x%s"% nr)
               xinv['x'+ nr]=(i,t)
    for t in range(num):
        for i in V:
            if i != rt:
               s = str((i,t))
               nr = ''.join(i for i in s if i.isdigit())
               y[i,t] = model.addVar(vtype='B', obj=0.0, lb=0.0,name="y%s"% nr)
               yinv['y'+ nr]=(i,t)
    for t in range(num):      
        for i in V:
            if i != rt:
               s = str((i,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(quicksum(f[j,i,t] for j in V if (j,i) in A) -quicksum(f[i,j,t] for j in V if (i,j) in A) - y[i,t] == 0, name="flowcons%s"% nr)
            else:
               s = str((i,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(quicksum(f[j,i,t] for j in V if (j,i,t) in A) -quicksum(f[i,j,t] for j in V if (i,j) in A) + quicksum(y[j,t] for j in V if j != rt) == 0, name="flowcons%s"% nr)
               model.addCons(quicksum(f[j,i,t] for j in V if (j,i) in A ) == 0, name="flowcont%s"% nr)
               #at least one flow must come out of the root for every time period...
               model.addCons(quicksum(f[i,j,t] for j in V if (j,i) in A ) >= 1, name="flowcontt%s"% nr)
    
    for t in range(num):
        keepsi = [False]*len(A)
        for (i,j) in A:
            ind = A.index((i,j))
            if i!=rt and j!=rt and not keepsi[ind]:
               keepsi[ind] = True
               indrev =  A.index((j,i))
               keepsi[indrev] = True
              
               s = str((i,j,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(f[i,j,t] - size_nodes*(x[i,t] - 2*x[j,t] + 0.5) - 256*(z[i,j,t]) <= 0, name="fxcons%s"% nr)
               srev = str((j,i,t))
               nrev = ''.join(i for i in srev if i.isdigit())
               model.addCons(f[j,i,t] - size_nodes*(x[j,t] - 2*x[i,t] + 0.5) - 256*(z[j,i,t]) <= 0, name="fxcons%s"% nrev)
   
    for t in range(num):
        keepsi = [False]*len(A)
        for (i,j) in A:
            ind = A.index((i,j))
            if i!=rt and j!=rt and not keepsi[ind]:
               keepsi[ind] = True
               indrev =  A.index((j,i))
               keepsi[indrev] = True
               s = str((i,j,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(z[i,j,t]+ z[j,i,t] <= 1, name="onezarc2%s"% nr)
               
    for t in range(num):
        keepsi = [False]*len(A)
        for (i,j) in A:
            ind = A.index((i,j))
            if i!=rt and j!=rt and not keepsi[ind]:
               keepsi[ind] = True
               indrev =  A.index((j,i))
               keepsi[indrev] = True
               s = str((i,j,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(g[i,j,t]+ g[j,i,t] <= 1, name="onegarc2%s"% nr)     
    for t in range(num):
        for (i,j) in A:
            if i!=rt and j!=rt:
               s = str((i,j,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(f[i,j,t] <= x[i,t], name="onezarc%s"% nr)
               model.addCons(f[i,j,t] <= x[j,t], name="onezarc%s1"% nr)

   
    for t in range(num):
        for (i,j) in A:
            if i!=rt and j!=rt:
               s = str((i,j,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(f[i,j,t] <= size_nodes*z[j,i,t], name="floforz%s"% nr)
               

    for t in range(num):
        for (i,j) in A:
            if i!=rt and j!=rt:
               s = str((i,j,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(f[i,j,t] <= size_nodes*g[j,i,t], name="floforg%s"% nr)

    for t in range(num):
        for i in V:
            if i != rt:
               s = str((i,t))
               nr = ''.join(i for i in s if i.isdigit())
               model.addCons(y[i,t] - x[i,t] <= 0, name="fxcons%s"% nr ) 
            
    
    for i in V:
        if i != rt:
           s = str(i)
           nr = ''.join(i for i in s if i.isdigit())
           model.addCons(quicksum(z[i,j,t] for j in V if (i,j) in A ) <= 1, name="toootos%s"% nr ) 

    for i in V:
        if i != rt:
           s = str(i)
           nr = ''.join(i for i in s if i.isdigit())
           model.addCons(quicksum(x[i,t] for t in lnum) >= num, name="numcons%s"% nr ) 
          
    for i in V:
        if i != rt:
           model.addCons(quicksum(f[j,i,t] for j in V if (j,i) in A for t in lnum) >= 1, name="flowtimecons%s"% str(i))
    
    model.writeProblem('treecut.lp')
    spx=cplex.Cplex()
    spx.read('treecut.lp')
    spx.solve()
    solz = access_solution_values(spx,xinv)
    print solz
   
               
def makeModel(Gr,rt,fixed):
    # get the nodes from graph
    #nx.draw(Gr,pos=nx.spring_layout(Gr),with_labels=True)
    #plt.show()
    V=sorted(Gr.nodes())
    size_nodes = len(V)
    # get the edges from graph
    A = Gr.edges()
    # get the cardinality of the set of edges
    size_arcs = len(A)
    # make some dictionaries for values of nodes
    numb_to_V_dict = {}
    V_to_numb_dict = {}
    numb_to_V = zip(range(1,size_nodes + 1), V)
    V_to_numb = zip(V, range(1,size_nodes + 1))
    for i, j in numb_to_V:
        numb_to_V_dict[i] = j
    for i, j in V_to_numb:
        V_to_numb_dict[i] = j
    W = [0]*len(V)
    # make model
    z={}
    zinv ={}
    model = Model()
   # model.hideOutput() # silent/verbose mode
    model.setMaximize()
    total = len(V)
    
    
    # setting up flow variables, making all coeffs of variables except the ones that flow into root zero
    for (i,j) in A:
        s = str((i,j))
        nr = ''.join(i for i in s if i.isdigit())
        ind = A.index((i,j))
        if j != rt:
           z[i,j] = model.addVar(ub = 64, vtype='I', obj=0.0, lb=0.0,name="z%s"% nr)
           zinv['z'+ nr]=(i,j)
           
        else:
           z[i,j] = model.addVar(ub = 64, vtype='I', obj=1.0, lb=0.0,name="z%s"% nr)
           zinv['z'+ nr]=(i,j)
       
    for i in V:
        #print i
        if i != rt:
           model.addCons(quicksum(z[j,i] for j in V if (j,i) in A) -2*quicksum(z[i,j] for j in V if (i,j) in A) + fixed[V_to_numb_dict[i]-1] >= 0, name="cons%s"% V_to_numb_dict[i])
        else:
           model.addCons(quicksum(z[j,i] for j in V if (j,i) in A ) -2*quicksum(z[i,j] for j in V if (i,j) in A ) >= 0, name="cons%s"% V_to_numb_dict[i])
           model.addCons(quicksum(z[i,j] for j in V if (i,j) in A ) <= 0, name="cont%s"% V_to_numb_dict[i])
    
  
   
    model.writeProblem('networkPebble.lp')
    spx=cplex.Cplex()
    spx.read('networkPebble.lp')
    spx.solve()
    solz = access_solution_values(spx,zinv)
    #print solz
    #print zinv[solz[0]]
    T = nx.Graph()
    for i in solz:
        #print i
        #print zinv[i]
        e = zinv[i]
        T.add_edge(*e)
    #G=nx.Graph()
    #G.add_edges_from([(1,2),(1,3),(2,4),(4,6),(3,6),(3,5),(3,8),(4,7),(4,5),(5,8),(7,8),(3,7),(6,8)])
    #g = ig.Graph()
    #Lemk = nx.cartesian_product(G,G)
    return (T,spx.solution.get_objective_value())
    #print SB.nodes()
    #print SB.edges()
    #g.add_edges([zinv[i] for i in solz])
    #g.add_vertices(SB.nodes())
    #g.add_edges(SB.edges())
    #se = [zinv[i] for i in solz]
    #sg = subgraph.edges(g,se, delete.vertices = TRUE)
    #layout = g.layout_reingold_tilford(root=(1,1))
    #ig.plot(g, layout = layout)
    #nx.draw(SB,pos=nx.spring_layout(SB, k=3),with_labels=True)
    #plt.show()
    #print zinv


 

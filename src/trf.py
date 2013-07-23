import itertools
import random
from   collections import defaultdict
from   logic.fol.syntax.parser import FolFormulaParser
from   logic.fol.semantics.structure import FolStructure
from copy import copy, deepcopy


N_STAR      =  'n*'    
CONCRETE_DS =  'concrete_ds'
INV         =  'invariant' 


def init_fol_struct( domain,interpretation,state ):
    f = FolStructure(domain,interpretation )    
    L = FolFormulaParser()
    
    from logic.fol import FolFormula
    s = 'i != null & t = null'    
    t =  L.parser.parse(s)
    print 'Parser:',t
    #eval_bool_formula = f.evaluate( t )
    #print eval_bool_formula
    state['fol_parser']   = L
    state['fol_struct']   = f
    

def create_dummy_state():
    concrete_ds  = [ 'Vval!1', 'Vval!2', 'Vval!3', 'Vval!4','Vval!5','Vval!6','null']
    rvars        = [ 'a', 'b', 'j','t','i',]
    
    var_concrete_map = {}    
    var_concrete_map[ rvars[0] ] = concrete_ds[0]
    var_concrete_map[ rvars[1] ] = concrete_ds[1]
    var_concrete_map[ rvars[2] ] = concrete_ds[2]
    var_concrete_map[ rvars[3] ] = concrete_ds[3]
    var_concrete_map[ rvars[4] ] = concrete_ds[4]
        
    ab = 'a' , 'b'
    ba = 'b' , 'a'
    aj = 'a' , 'j'
    ja = 'j',  'a'
    bj = 'b' , 'j'    
    jb = 'j' , 'b'
    jj = 'j' , 'j'
    aa = 'a' , 'a'
    bb = 'b' , 'b'
    tj = 't' , 'j'
    jt = 'j' , 't'
    tt = 't' , 't'
    ta = 't' , 'a'
    at = 'a' , 't'
    bt = 'b' , 't'
    tb = 't' , 'b'
    ji = 'j' , 'i'
    ij = 'i' , 'j'
    ai = 'a' , 'i'
    ia = 'i' , 'a'
    ii = 'i' , 'i'
    ib = 'i' , 'b'
    bi = 'b' , 'i'
    ti = 't' , 'i'
    itt = 'i', 't'
    l = 'i'
    n = {}    
    n[ab] = True
    n[ba] = False
    n[bj] = False
    n[jb] = True
    n[aj] = False
    n[ja] = False
    n[jj] = True
    n[aa] = True
    n[bb] = True
    n[tj] = False
    n[jt] = False
    n[tt] = True
    n[ta] = False
    n[at] = True
    n[tb] = False
    n[bt] = True

    n[ii] = True
    n[ji] = False
    n[ij] = True
    n[ia] = False
    n[ib] = False
    n[bi] = False
    n[ai] = True
    n[ti] = False
    n[itt]= False
       
    C = {}
    C[l] = False    
    state = {}        
    state[N_STAR]         = n
    state['C']            = C
    state['map']          = var_concrete_map
    state['rvars']        = rvars
    state[CONCRETE_DS]  = concrete_ds
    
    #init_fol_struct(concrete_ds, var_concrete_map, state)
    print 'dummy_state:', state    
    return state


def create_state(invariant):
    print 'Creating state:'
    state_from_model = {}    
    m                = model_get(invariant)
    state_from_model[CONCRETE_DS] = concrete_ds_get(m)
    relations  = []
    relations.append( N_STAR );
    relations.append( 'C' );
    relations.append( 'n*_' );        
    
    rvars = vars_get( m, relations )
    
    state_from_model['rvars']      = rvars
    state_from_model['relations']  = relations
    state_from_model[ INV ]        = invariant    
    interpretation_from_model_get( m,relations, 
                                   state_from_model[CONCRETE_DS],
                                   state_from_model )
    
    from opSemantics import node_creator
    nc          = node_creator()
    state_from_model['nc'] = nc
    
    #init_fol_struct(m.domain, m.interpretation, state_from_model)
    print 'State from model:',state_from_model
    print 'Model:', m
    return state_from_model
    

def init():
    return create_dummy_state()
    print 'init - do nothing'


#use Shachar's while_fe.py from synopsis folder
#output: parsing tree
def parseInput():     
    print 'parsing input...'

     
#get's the model
#ouput: model of the program     
def getStartState(): 
    print 'print the starting state to graph...'


#input: statement and model
#out:   new state
def opSemantics():
    print 'gets model and tree root'


#input:  parsing tree
#input:  model
#output: mew model
def doOneStep():
    print 'calculate on state transition'

def getOutput():
    print 'draw graph output and table'


def relations_get(state):
    return state['relations']


from synopsis.af_wp_permute import WeakestPreconditionPermute    
import os.path    
def model_get(invariant):
    print 'Getting model...'
    w                  =  WeakestPreconditionPermute()
    here               =  os.path.dirname(os.path.realpath(__file__))
    preface            =  open(os.path.join(here, "/home/tomerwei/Applications/fol-tool/IMDEA.Imtel/fol/list-preface.smt2")).read()
    sll_lib            =  open(os.path.join(here, "/home/tomerwei/Applications/fol-tool/IMDEA.Imtel/fol/sll.fol")).read()
    w.syn.libs        +=  [sll_lib]
    w.syn.smt.preface  =  preface
            
    correct_result     =  """n*(h,x) & n*(x,y) &
                             (i != null -> n*(h,i)) &
                             ite(j = null, i=h, n*(h,j) & ntot_(j,i)) &     
                             (t != null -> C(i))"""                                                        
                             
    #brute_force()    
    file_str = open( '/home/tomerwei/Applications/fol-tool/IMDEA.Imtel/fol/examples/sll-delete.imp').read()
    #for formula in permute():
    #formula = '( n*(i,j) & n*(i,t) )'    
    inv_guess = 'I:=' + invariant + '\n' + file_str
    #print 'Formula: ', formula + '\n'
    m = w( inv_guess )    
    #print 'Domain:', m.domain
    #print 'Interpretation:', m.interpretation
    return m
    
    
def vars_get(m,relations):
    res    =  []    
    intrp  =  m.interpretation    
    for v in intrp:
        if v not in relations:
            res.append(v)
    return res


def relation_get(intrp,rel,rvars):
    res = {}
    f = intrp[rel]    
    for i in rvars:
        #Distinguish between binary and monad relations
        if rel == 'C': 
            in_rel = f(i)            
            res[i] = in_rel
        else:
            for j in rvars:                            
                in_rel = f(i,j)
                ij = i,j
                res[ij] = in_rel
    return res


def interpretation_from_model_get(m,relations,rvars,state):
    intrp            =  m.interpretation
    var_concrete_map =  {}    
    for i in intrp:
        if i in relations:            
            relation = relation_get(intrp,i,rvars)
            state[i] = relation
        else: #this is the concrete mapping            
            var_concrete_map[i] = intrp[i]
    state['map'] = var_concrete_map
   
def concrete_ds_get(m):    
    res = m.domain    
    return res


def trf_interpreter(state,fe):
    print 'Welcome to the while-interpreter.'
    while True:
        to_parse = raw_input(">")
        if to_parse == 'exit':
            return
        elif len(to_parse)>0:
            astf = fe.parser(to_parse)
            #print astf
            general_stmt(astf,state)        
            
            
        
    

    
if __name__ == '__main__':    
    #state = init()
    invariant     = """ n*(h,x) & n*(x,y) &    
                     (i != null -> n*(h,i)) &
                     (j = null -> i = h ) & 
                     (j != null -> n*(h,j) ) &                                  
                     (t != null -> C(i) )  & ( t = null -> ~C(i) )"""
    
    state = create_state( invariant )
    
    from synopsis.programs.while_fe import WhileFrontend
    from opSemantics import general_stmt
    fe           =  WhileFrontend()    
    state['fe']  =  fe    
    prev_parse   = """
                   while $i != null$ {$I$} ( ( if $C( i )$ then ( a:= new ; t := i.n ; j.n := null ; j.n := t ) else j := i ) ; i := i.n )
                """
                    
    str_to_parse = """
   while $i != null & t = null$ {$I$} (
      if $C(i)$ then t := i
      else (
         j := i ; i := i.n
      )
   )"""
   
    #while-interpreter 
    #trf_interpreter(state,fe)
    org_state_map   = deepcopy(state['map'])
    org_state_c     = deepcopy(state['C'])
    org_state_nstar = deepcopy(state['n*'])

    astf      = fe.parser(str_to_parse)    
    general_stmt(astf,state)    
        
    last_st         = state    
    first_st        = state
    first_st['map'] = deepcopy(org_state_map)
    first_st['C']   = deepcopy(org_state_c)
    first_st['n*']  = deepcopy(org_state_nstar)    
            
    from permute import brute_force
    from opSemantics import chk_inv_on_general_stmt
    
    for formula in brute_force():
        first_st[INV] = formula        
        s_loop = chk_inv_on_general_stmt( first_st )
        if s_loop:
            last_st[INV] = formula
            e_loop = chk_inv_on_general_stmt( last_st )
            print 'Does inv hold?: ', formula, e_loop
                
        
           
    
        
    #w = WhileFrontend.WhileASTDeserialize()
    #print w(unicode(astf))
    #print astf.root
    #print astf.subtrees
    
    #print w(";{x:=y{i,j},y:=x.n{k,i},x.n:=y{i,i}}")
    #print w(";{;{x:=y{i,h},x:=null{j},x:=null{t},while {((i != null) & (t = null)), I, skip}}}")
    #print astf
    
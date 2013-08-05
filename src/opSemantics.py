#TODO need to add the State (~=model) to each function below
#all statements should return new state S'
from copy import deepcopy
from concrete_graph import draw_graph
from exprEval import eval_cond
#need to define 


def general_stmt(stmt,state):
    #print stmt, str(type(stmt))
    curStmt = stmt.root
    
    #print 'Initial state:', stmt
    #draw_graph( 'file1', state )        

   
    if curStmt == 'while':
        while_stmt(stmt, state)
    elif curStmt == 'if':
        if_stmt(stmt, state)
    elif curStmt == ';':
        comma_stmt(stmt,state)
    else:
        #print 'Graph Before statement:', stmt
        #draw_graph( 'file1', state )        
        
        if curStmt == 'x:=y':
            ass_stmt(stmt,state)
        elif curStmt == 'x:=y.n':
            rhs_next_ptr_stmt(stmt,state)
        elif curStmt == 'x.n:=y':
            lhs_next_ptr_ass_stmt(stmt,state)
        elif curStmt == 'x.n:=null':
            lhs_next_ptr_null_stmt(stmt,state)             
        elif curStmt == 'x:=new':
            #print stmt, state
            #prev_state = deepcopy(state)
            ass_new_ptr(stmt,state)
        else:        
            print 'Welcome to general_stmt: ParsingError'            
            print stmt.root, ' -> ' , stmt
            raise SystemExit
            
        #state_diff_finder(prev_state,state)
        #print 'Graph After statement:', stmt
        #draw_graph( 'file2', state )
        #raw_input("Press Enter to continue...")    


def chk_inv_on_general_stmt( state ):
    from exprEval import eval_inv_quick    
    inv                   = inv_get(state)
    does_inv_hold_in_loop = eval_inv_quick(inv,state)            
    return does_inv_hold_in_loop
    


def comma_stmt(stmt,state):
    for i in stmt.subtrees:
        general_stmt(i,state)


def if_stmt(stmt,state):
    #print 'if_stmt', stmt
    if_cond   = stmt.subtrees[0]
    if_body   = stmt.subtrees[1]
    else_stmt = stmt.subtrees[2]        
    cond_chk  = eval_cond(if_cond,state)
    if cond_chk:
        general_stmt(if_body,state)
    else:    
        general_stmt(else_stmt,state)
#TODO    change with:
#    if cond_chk:
#        general_stmt(if_body,state)
#    else:
#        general_stmt(else_stmt,state)


def while_stmt(stmt,state):
    from exprEval import eval_inv    
    while_cond   = stmt.subtrees[0]
    #the invariant I is in between here
    inv = inv_get(state)
    #print 'the invariant I:=', inv
    while_body     =  stmt.subtrees[-1]    
    cond_chk       =  eval_cond(while_cond,state)    
    mapping_list   =  []
    nstar_list     =  []
        
    while True:        
        cond_chk     =  eval_cond(while_cond,state)
        if not cond_chk:
            map_copy   = deepcopy( interpretation_mapping_get(state) )
            nstar_copy = nstar_relation_map_get(state)
            mapping_list.append(map_copy)
            nstar_list.append(nstar_copy)            
            break
        
        #state_collection.append( state )
        does_inv_hold_in_loop_start = eval_inv( inv,state )
        
        map_copy   = deepcopy( interpretation_mapping_get(state) )
        nstar_copy = nstar_relation_map_get(state)
        mapping_list.append(map_copy)        
        nstar_list.append(nstar_copy)        
        
        print 'does invariant hold at the start of loop?', does_inv_hold_in_loop_start        
        general_stmt(while_body,state)
        #checking invariant
        does_inv_hold_in_loop_end = eval_inv( inv,state )                                    
        print 'does invariant hold at the end of loop?', does_inv_hold_in_loop_end        
        #if not does_inv_hold_in_loop_end 
        
    
    
    print 'how many states collected', len(mapping_list)
    
    for i in mapping_list:
        print i
        
    for j in nstar_list:
        print j    
        
    


# x := y
def ass_stmt(stmt,state):    
    x      = stmt.subtrees[0].root
    y      = stmt.subtrees[1].root
    y_intp = interpretation_get(state,y)
    interpretation_set(state,x,y_intp)
           
            
# x := new
# TODO: check if Pvar is all the free variables
def ass_new_ptr(stmt,state):
    #print 'new ptr: ', stmt
    x   = stmt.subtrees[0].root    
    # create new concrete node, which is false to all
    concrete_intp   = node_factory_get(state)
    # map x to node
    interpretation_set(state, x, concrete_intp )
    
        
def p_next_plus(state,n_ptr,s,t):    
    rel_st =  nstar_concrete_value_get(state, s, t)        
    is_eq  =  is_same_concrete_node(state,s,t)
    result =  rel_st and (not is_eq)
    return result 


# a->b is equiv to (~a)|b
# if t is the minimal in relation to y: return true
# else return false
def p_next(state,n_ptr,s,t):    
    result      =  p_next_plus(state,n_ptr,s,t)
    if result:
        c_nodes   =  concrete_nodes_get(state)
        #print 's and t are different' , s ,t return 
        for gamma in c_nodes:
            lhs       =  p_next_plus(state,n_ptr,s,gamma)
            rhs       =  nstar_concrete_value_get(state,t,gamma)            
            lhs_implies_rhs = (not lhs) or rhs
            result    = result and lhs_implies_rhs                   
            if not result:
                #print lhs,rhs, lhs_implies_rhs, result
                #print 'for s=',s,'t-is not the minimal node=',t,'gamma=',gamma                
                return False
            #else:
                #print 'passed for s=',s,'t-is minimal node=',t,'gamma=',gamma                
        return True
    return False



def next_concrete_node_of_c_node_get(cy,n_ptr,state):
    c_nodes  = concrete_nodes_get(state)
    #print 'searching node for', cy
    for alpha in c_nodes:        
        is_minimal = p_next(state,n_ptr,cy,alpha)
        #print 'is_min', is_minimal, cy, alpha
        if is_minimal:
            return alpha
    return None


def next_concrete_node_of_ptr_get(y,n_ptr,state):
    if is_equal_intrepretation(state, y, 'null'):
        #print 'Variable',y,' is pointing to null.'
        return None
    cy = interpretation_get(state, y)          
    return next_concrete_node_of_c_node_get(cy,n_ptr,state)

# x := y.next
#first we find all vars that are reachable from y
#then we find the minimal var among them - e.g the one
#who is not reachable by others.
def rhs_next_ptr_stmt(stmt,state):
    #print 'rhs_next_ptr_stmt', stmt
    x     = stmt.subtrees[0].root
    y     = stmt.subtrees[1].root    
    n_ptr = nstar_relation_name_get()
    alpha = next_concrete_node_of_ptr_get( y,n_ptr,state )
    #print x,y,alpha
    if alpha != None:    
        interpretation_set(state,x,alpha)        
    else:
        c_null = interpretation_get(state, 'null')            
        #print 'rhs_next_ptr_stmt: Next node is null ', x, alpha
        interpretation_set(state, x, c_null)        
                                

# x.next := null
#rel[r] = n*(a,b)
#ax = n*(a,x)
#bx = n*(x,b)
#rel[r] = rel[r] & ( ~rel[ax] | rel[bx] )    
def lhs_next_ptr_null_stmt(stmt,state):    
    x = stmt.subtrees[0].root
    #next_field = stmt.subtrees[1]
    #not good enough, next field is of type adt.tree.Tree
    #use str(type(next_field)) to find out
    #rel_name  =  stmt.subtrees[1].root
    n_ptr     = nstar_relation_name_get()    
    rel       = relation_map_get(state, n_ptr)
    cx        = interpretation_get(state, x)
    for r in rel:
        a = r[0]
        b = r[1]
        rel_ax = nstar_concrete_value_get(state, a, cx)
        rel_bx = nstar_concrete_value_get(state, b, cx)
        rel_r  = nstar_concrete_tuple_value_get(state, r)
        res    = rel_r and ( (not rel_ax) or rel_bx )
        nstar_concrete_tuple_value_set(state, r, res )#rel[r] = rel_r & ( ~rel_ax | rel_bx )         
        
                
             
# x.next := y
# the above equals to: x.n := null ; x.n := y
def lhs_next_ptr_ass_stmt(stmt,state):
    x    = stmt.subtrees[0].root
    #n = stmt.subtrees[1].root
    y    = stmt.subtrees[2].root        
    n_yx = nstar_pointer_value_get(state,y,x)
    n_xy = nstar_pointer_value_get(state,x,y)
    
    if n_yx:#we want to detect this !
        print stmt, 'lhs_next_ptr_ass_stmt: Closing circle! Exiting. state is:' , state
        raise SystemExit
    elif n_xy: #should never happen
        print stmt, 'lhs_next_ptr_ass_stmt: lhs is already pointing to rhs!' , state
        raise SystemExit
    
    lhs_next_ptr_null_stmt(stmt, state)          #x.n := null
    nstar_relation_value_set(state, x, x, True)  #from here till end: x.n := y
    nstar_relation_value_set(state, x, y, True)  #from here till end: x.n := y
            
    xc   = interpretation_get(state, x)
    yc   = interpretation_get(state, y)
    rel  = nstar_relation_map_get(state)    
    for r in rel:
        a = r[0]
        b = r[1]
        rel_ax = nstar_concrete_value_get(state, a, xc)
        rel_yb = nstar_concrete_value_get(state, yc, b)        
        rel[r] = rel[r] or ( rel_ax and rel_yb )    
    #changes concrete node, VVal!4 and studf    
    #print 'afterwards state', state 

#returns the current state
def get_state(state,relation_name,key):
    rel = state[relation_name]
    #print 'n*:', key, rel[key]
    return rel[key]    
    
  

#--------------------------------------
#  Relations API
#--------------------------------------
def state_all_vars_get(state):
    return state['rvars']

def state_all_real_vars_get(state):
    res = []
    for v in state_all_vars_get(state):
        if not is_equal_intrepretation(state, v, 'null'):
            res.append(v)    
    return res


def relation_map_get(state,rel_name):
    res = state[rel_name]
    return res

#Only works for C(x), monad type relations
def c_relation_value_get(state,rel_name,x):
    rel = relation_map_get(state,rel_name)
    xc    = interpretation_get(state,x)
    #print 'c map', xc, rel[xc] , rel   
    return rel[xc]    

def nstar_relation_name_get():
    from trf import N_STAR
    return N_STAR

def nstar_relation_map_get(state):
    nstar_name = nstar_relation_name_get()
    return relation_map_get(state,nstar_name)    


def nstar_concrete_tuple_value_get(state,rc):
    rel   = nstar_relation_map_get(state)        
    return rel[rc]
    
    
def nstar_concrete_value_get(state,xc,yc):
    rel    = nstar_relation_map_get(state)
    xcyc   = xc,yc
    return rel[xcyc]


def nstar_pointer_value_get(state,x,y):    
    xc    = interpretation_get(state,x)    
    yc    = interpretation_get(state,y)    
    return nstar_concrete_value_get(state,xc,yc)


def nstar_concrete_tuple_value_set(state,rc,value):
    rel     = nstar_relation_map_get(state)    
    rel[rc] = value

def nstar_pointer_tuple_value_set(state,r,value):    
    rc      = interpretation_get(state,r)
    nstar_concrete_tuple_value_set(state,rc,value)

def nstar_relation_value_set(state,x,y,value):
    rel     = nstar_relation_map_get(state)
    xc      = interpretation_get(state,x)    
    yc      = interpretation_get(state,y)
    xy      = xc,yc
    rel[xy] = value
    
#--------------------------------------
#  Other state API's
#--------------------------------------
    
def inv_get(state):
    from trf import INV    
    return state[INV]    
    

#--------------------------------------
#  Interpretation Mapping
#--------------------------------------
def interpretation_mapping_get(state):
    return state['map']

def mapping_concrete_get(mapping,v):    
    return mapping[v]
    
#returns the concrete node x points on
#e.g Val!v4
def interpretation_get(state,x):
    v_map = interpretation_mapping_get(state)
    #print v_map
    #print v_map,x
    return mapping_concrete_get(v_map,x)

def interpretation_set(state,x,p):
    v_map    = interpretation_mapping_get(state)
    v_map[x] = p
    
# TODO: create new interpretation in case of x:=new

    

def is_same_concrete_node(state,intrp_x,intrp_y):
    return intrp_x == intrp_y

#returns true iff concrete interpretation of x
#equal concrete interpretation of y
def is_equal_intrepretation(state,x,y):
    intrp_x = interpretation_get(state,x)
    intrp_y = interpretation_get(state,y)
    return is_same_concrete_node(state,intrp_x,intrp_y)


def concrete_nodes_get(state):
    from trf import CONCRETE_DS
    return state[CONCRETE_DS]



#--------------------------------------
#  Node creation tools
#--------------------------------------
#creates new concrete node, and saves it to the state
#returns the newly created node
#@static_var("counter", 0)

def node_factory_get(state):
    nc  =  state['nc']
    res =  nc.create_node(state)
    return res
    

class node_creator:
    counter = 0

    def __init__(self):
        self.counter = 0

    def create_node(self,state):
        self.counter += 1
        v         = 'V!val!_' + str( self.counter )    
        c_nodes   = concrete_nodes_get(state)
        c_nodes.append( v )
       
        nstar_map     = nstar_relation_map_get(state)
        vv            = v,v
        nstar_map[vv] = True
                    
        for r in c_nodes:
            ab = r, v
            ba = v, r
            nstar_map[ab] = False
            nstar_map[ba] = False
                            
        return v


#--------------------------------------
#  Debug state tools
#--------------------------------------
def state_diff_finder(state_a,state_b):
    for rel in state_b:
        s = state_b[rel]
        for r in s:                    
            rel_a = state_a[rel]
            r_a   = rel_a[r]
            if s[r] != r_a:
                print 'rel:', r, 'b4:', r_a, 'after:',s[r]

    
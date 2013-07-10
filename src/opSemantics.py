#TODO need to add the State (~=model) to each function below
#all statements should return new state S'
from copy import deepcopy
from concrete_graph import draw_graph
from exprEval import eval_cond
#need to define 

def general_stmt(stmt,state):
    curStmt = stmt.root
   
    if curStmt == 'while':
        while_stmt(stmt, state)
    elif curStmt == 'if':
        if_stmt(stmt, state)
    elif curStmt == ';':
        comma_stmt(stmt,state)
    else:
        print 'Graph Before statement:', stmt
        draw_graph( 'file1', state )
        
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
        print 'Graph After statement:', stmt
        draw_graph( 'file2', state )
        raw_input("Press Enter to continue...")    

    


def comma_stmt(stmt,state):
    #print 'comma_stmt', stmt
    for i in stmt.subtrees:
        general_stmt(i,state)
    #print 'comma end'


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
    print 'while stmt', stmt
    while_cond   = stmt.subtrees[0]
    #the invariant I is in between here
    print 'the invariant I:=', stmt.subtrees[1]
    while_body   = stmt.subtrees[-1]
    cond_chk     = eval_cond(while_cond,state)
    if cond_chk:
        general_stmt(while_body,state)    


# x := y
def ass_stmt(stmt,state):    
    x   = stmt.subtrees[0].root
    y   = stmt.subtrees[1].root
    rel = nstar_relation_map_get(state)
    for r in rel:
        a     = r[0]
        b     = r[1]
        rel_r = nstar_relation_tuple_value_get(state, r)        
        if y == b:
            i  = a                        
            nstar_relation_value_set(state, i, x, rel_r) #rel[ix] = rel[r]            
        elif y == a:
            i  = b          
            nstar_relation_value_set(state, x, i, rel_r) #rel[xi] = rel[r]
    
    y_intp = interpretation_get(state,y)
    interpretation_set(state,x,y_intp)
           
            
# x := new
# TODO: check if Pvar is all the free variables
def ass_new_ptr(stmt,state):
    #print 'new ptr: ', stmt
    x   = stmt.subtrees[0].root    
    rel = nstar_relation_map_get(state)##TODO need to traverse all states
    for r in rel:
        a = r[0]
        b = r[1]
        if ((x == a) or (x == b)) and ( a != b ):
            nstar_relation_tuple_value_set(state, r, False)#rel[r] = False
            
    
        
def p_next_plus(state,n_ptr,s,t):
    rel    =  state[n_ptr]
    st     =  s, t    
    is_eq  =  is_equal_intrepretation(state,s,t)
    result =  rel[st] and (not is_eq)
    return result 


# a->b is equiv to (~a)|b
# if t is the minimal in relation to y: return true
# else return false
def p_next(state,n_ptr,s,t):
    rel         =  state[n_ptr]
    result      =  p_next_plus(state,n_ptr,s,t)
    if result:
        rvars       = state_all_real_vars_get(state)
        print 's and t are different' , rvars, s ,t 
        for gamma in rvars:
            lhs       = p_next_plus(state,n_ptr,s,gamma)
            print lhs, 'pnext plus' , s, gamma
            gamma_t   = gamma, t            
            rhs       = rel[gamma_t]
            #rhs       = rel[t_gamma]
            lhs_implies_rhs = (not lhs) or rhs
            #lhs_implies_rhs = (lhs and rhs) or ((not lhs)) 
            result    = result and lhs_implies_rhs
            print 'lhs ', lhs,'rhs ',rhs, gamma_t       
            if not result:
                print 'for s=',s,'t-is not the minimal node=',t,'gamma=',gamma                
                return False
            else:
                print 'passed for s=',s,'t-is minimal node=',t,'gamma=',gamma
        return True
    return False



def next_node_get(y,n_ptr,state):
    #y     = stmt.subtrees[1].root
    #n_ptr = stmt.subtrees[2].root
#    if (y == 'i') |  (y == 'h'):
#        raw_input("DEbug...")
        
    if is_equal_intrepretation(state, y, 'null'):
        print 'GOT HERE!'
        return None
        
    print 'next_node_get', y, n_ptr
    rvars  = state_all_real_vars_get(state)
    for alpha in rvars:        
        is_minimal = p_next(state,n_ptr,y,alpha)
        #please note that their could be only **one** alpha that is true
        if is_minimal:
            #copy_relation_values(state,n_ptr,alpha,x)
            print 'found minimal, y=',y,'alpha=',alpha    
            return alpha
#    if (y == 'i') |  (y == 'h'):
#        raw_input("DEbug End...")        
    return None

# x := y.next
#first we find all vars that are reachable from y
#then we find the minimal var among them - e.g the one
#who is not reachable by others.
def rhs_next_ptr_stmt(stmt,state):
    print stmt
    x     = stmt.subtrees[0].root
    y     = stmt.subtrees[1].root    
    n_ptr = nstar_relation_name_get()
    alpha = next_node_get( y,n_ptr,state )
    #print x,y,alpha
    if alpha != None:    
        copy_relation_values(state,n_ptr,alpha,x)
        
        alpha_intp = interpretation_get(state,alpha)
        interpretation_set(state,x,alpha_intp)
        
    else:
        print 'Next node not existent ', x, alpha
                                

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
    n_ptr = nstar_relation_name_get()    
    rel       = relation_map_get(state, n_ptr)
    for r in rel:
        a = r[0]
        b = r[1]
        rel_ax = nstar_relation_value_get(state, a, x)
        rel_bx = nstar_relation_value_get(state, b, x)
        rel_r  = nstar_relation_tuple_value_get(state, r)
        res    = rel_r and ( (not rel_ax) or rel_bx )
        nstar_relation_tuple_value_set(state, r, res )#rel[r] = rel_r & ( ~rel_ax | rel_bx )         
        
                
             
# x.next := y       
def lhs_next_ptr_ass_stmt(stmt,state):
    x = stmt.subtrees[0].root
    n = stmt.subtrees[1].root
    y = stmt.subtrees[2].root
    
    rel  = state[n]   
    n_yx = nstar_relation_value_get(state,y,x)
    
    if n_yx:        
        print stmt, 'Closing circle! state is:' , state
        raise SystemExit    
    for r in rel:
        a = r[0]
        b = r[1]
        rel_ax = nstar_relation_value_get(state, a, x)
        rel_yb = nstar_relation_value_get(state, y, b)        
        rel[r] = rel[r] or ( rel_ax and rel_yb )    
    #changes concrete node, VVal!4 and studff       

#returns the current state
def get_state(state,relation_name,key):
    rel = state[relation_name]
    #print 'n*:', key, rel[key]
    return rel[key]    
    
    
# n(a,b) = n[a][b] = true\false    
def update_state(state,relation_name,value,*args):
    rel = state[relation_name]
    rel[args] = value    
    print 'updated', rel, args, 'to', value
    
                
def copy_relation_values(state,rel_name,from_v,to_v):
    print 'copy rel values', rel_name,from_v,to_v
    rel = state[rel_name]
    for r in rel:
        s = r[0]
        t = r[1]
        if s == from_v:
            to = to_v, t
            rel[to] = rel[r]
        elif t == from_v:
            to = s, to_v
            rel[to] = rel[r]
                                    

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
    return rel[x]    

def nstar_relation_name_get():
    from trf import N_STAR
    return N_STAR

def nstar_relation_map_get(state):
    nstar_name = nstar_relation_name_get()
    return relation_map_get(state,nstar_name)    


def nstar_relation_tuple_value_get(state,r):
    rel = nstar_relation_map_get(state)    
    return rel[r]
    
    
def nstar_relation_value_get(state,x,y):
    rel = nstar_relation_map_get(state)
    xy  = x,y
    return rel[xy]


def nstar_relation_tuple_value_set(state,r,value):
    rel     = nstar_relation_map_get(state)
    rel[r] = value


def nstar_relation_value_set(state,x,y,value):
    rel     = nstar_relation_map_get(state)
    xy      = x,y
    rel[xy] = value
    

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
    return mapping_concrete_get(v_map,x)

def interpretation_set(state,x,p):
    v_map    = interpretation_mapping_get(state)
    v_map[x] = p
    
#create new interpretation in case of x:=new

    
#returns true iff concrete interpretation of x
#equal concrete interpretation of y
def is_equal_intrepretation(state,x,y):
    intrp_x = interpretation_get(state,x)
    intrp_y = interpretation_get(state,y)
    return intrp_x == intrp_y



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

    
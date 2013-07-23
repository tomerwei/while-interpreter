from logic.fol.syntax.parser import FolFormulaParser
from trf import relations_get

EQUALS    =  '='
NEQUALS   =  '!='
AND       =  '&'
OR        =  '|'
IMPLIES   =  '->'
NOT       =  '~'

OPERATORS = {EQUALS,NEQUALS,AND,OR,IMPLIES,NOT}


def equals_op(state,lhs_tree,rhs_tree):
    from opSemantics import is_equal_intrepretation
    #print lhs_tree, rhs_tree        
    res = is_equal_intrepretation(state,lhs_tree.root,rhs_tree.root)
    #print 'is',lhs_tree,'equal to',rhs_tree,'?',res
    return res

def relations_op(state,rel_name,tree):
    from opSemantics import c_relation_value_get
    
    rel_arg = tree.subtrees[0].root
    if rel_name == 'C':
        res =  c_relation_value_get(state, rel_name, rel_arg)        
        return res
    else:
        print 'relations_op: Rel not dealt with', rel_name
        print rel_name, ' -> ' , tree
        raise SystemExit
    return False


def eval_do(state,eval_tree):    
    r = eval_tree.root    
    if r in OPERATORS:
        if r == AND:
            lhs = eval_do(state,eval_tree.subtrees[0])
            rhs = eval_do(state,eval_tree.subtrees[1])
            return lhs and rhs
        elif r == OR:
            lhs = eval_do(state,eval_tree.subtrees[0])
            rhs = eval_do(state,eval_tree.subtrees[1])
            return lhs or rhs
        elif r == EQUALS:
            return equals_op(state,eval_tree.subtrees[0], eval_tree.subtrees[1])
        elif r == NEQUALS:
            return not equals_op(state,eval_tree.subtrees[0], eval_tree.subtrees[1])
        elif r == IMPLIES:
            lhs = eval_do(state,eval_tree.subtrees[0])
            rhs = eval_do(state,eval_tree.subtrees[1])
            return (not lhs) or rhs
        elif r == NOT:
            lhs = eval_do(state,eval_tree.subtrees[0])
            return not lhs
        else:
            print 'eval_do: Operator not dealt with', eval_tree.root
            print r, ' -> ' , eval_tree
            raise SystemExit
    elif r == 'True':
        return True
    elif r == 'False':
        return False            
    elif r in relations_get(state):
        return relations_op(state,r,eval_tree)                                 
    else:
        print 'Welcome to eval_do: ParsingError'            
        print r, ' -> ' , eval_tree
        raise SystemExit

    return False


#--------------------------------------
#  Evaluate condition
#--------------------------------------
# TODO correct the code
def eval_cond(cond,state):    
    #print 'cond stmt:', cond, str(type(cond)), cond.root, str(type(cond.root))
    L   =  FolFormulaParser()        
    t   =  L.parser.parse(cond.root)    
    res =  eval_do(state,t)
    #print 'eval_cond', cond, res
    #parsed_cond        = L.parser.parse( cond.root )
    #eval_bool_formula  = f.evaluate( parsed_cond )    
    #return eval_bool_formula
    return res


def preprop_nstar(inv,state):
    from opSemantics import nstar_pointer_value_get
    import re                 
    result = re.findall("n.\(...\)",inv);    
    for r in result:
        tmp        =  r.replace("n*(","")
        tmp        =  tmp.replace(")","")                
        nstar_tup  = tmp.split(',') #nstar_tup is of length 2        
        is_in_rel  = nstar_pointer_value_get(state, nstar_tup[0], nstar_tup[1])        
        if is_in_rel:
            inv  = inv.replace(r, 'True')
        else:
            inv  = inv.replace(r, 'False')         
    #print state        
    #print inv
    return inv


def preprop_inv(inv,state):
    inv = preprop_nstar(inv,state)
    return inv


def eval_inv(cond,state):
    inv = preprop_inv(cond,state)    
    L   =  FolFormulaParser()        
    t   =  L.parser.parse(inv)
    #print 'cond stmt:', inv, str(type(inv)), t
    res =  eval_do(state,t)
    #print 'eval_cond', inv, cond,res
    return res

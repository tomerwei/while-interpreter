from logic.fol.syntax.formula import FolFormula
from copy import deepcopy


def is_forall_var(v):
    return v.root == FolFormula.FORALL


#creates one formula
def create_one_f(v,f,c):
    if f.root == v.root:
        f.root = c 
    subf_len = len( f.subtrees )
    for i in xrange(0,subf_len):
        f.subtrees[i] = create_one_f(v,f.subtrees[i],c)
    return f


def conjunct_formulas( fs ):
    return FolFormula.conjunction( fs )

def replace_with_conjuncts(v,f,concretes):
    fs  = []
    for c in concretes:
        fcopy = deepcopy(f)
        cur = create_one_f(v,fcopy,c)                
        fs.append( cur )
    res = conjunct_formulas(fs)
    return res    


def blast_horn_body(f,concretes):    
    if is_forall_var(f):
        rhs = blast_horn_body( f.subtrees[1], concretes )        
        f.subtrees[1] = rhs
        one_blast = replace_with_conjuncts(f.subtrees[0],f.subtrees[1],concretes)        
        return one_blast
    else:
        return f


def horn_concretes_get(formula):
    res = []
    f   = formula
    while is_forall_var(f):
        res.append(f.subtrees[0])
        f = f.subtrees[1]
    return res
    
        
def horn_body_get(formula):    
    f   = formula
    while is_forall_var(f):        
        f = f.subtrees[1]
    
    if f.root == FolFormula.IMPLIES:    
        return f.subtrees[0]
    else:
        print 'Error: Not a horn clause! ', f
        None



def blast_horn_clause(str_to_parse):
    from synopsis.proof import Expansion
    L          =  Expansion.FormulaReader().parser
    t          =  L(str_to_parse)
    horn_body  =  horn_body_get(t)
    concretes  =  horn_concretes_get(t)
    return blast_horn_body(horn_body,concretes)

        
        
if __name__ == '__main__':
    #from synopsis.proof import SynopsisFormulaParser
    #from synopsis.proof import Expansion
    horn_clause_to_parse = """ forall i1 i2 i3 ( forall i j ( n*(h,i) & n*(x,y) -> j = i )  -> H ) 
                         """                    
    #where i1,i2,i3 will be the concrete states
    #and i j are the quantifiers of the IMPLIES left hand side i j                                                          
    horn_body_to_parse  = """ forall i j ( n*(h,i) & n*(x,y) -> j = i ) 
                    """                                    
    #from logic.fol import Identifier
    #i1 = Identifier('i1','variable')
    #i2 = Identifier('i2','variable')
    #i3 = Identifier('i3','variable')
    #concretes = [i1,i2,i3]
    
    
    print blast_horn_clause( horn_clause_to_parse )
    #print blast_horn_body(str_to_parse,concretes)    
    #general_stmt(astf,state)
    
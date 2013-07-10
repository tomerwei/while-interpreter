#from igraph import *

from pygraphviz import *


def next_edge_get(state,ptr):
    var_map   =   state['map']
     
    from opSemantics import next_node_get
    from opSemantics import nstar_relation_name_get
    n_ptr = nstar_relation_name_get()    
    next_node = next_node_get(ptr,n_ptr, state)
    print 'next_edge_get', ptr,next_node
    if next_node != None:
        return var_map[next_node]
    else:
        return 'null'
        

def draw_graph(prefix, state):
    from opSemantics import is_equal_intrepretation
    
    g         =   AGraph(strict=False,directed=True )
    c_nodes   =   state['concrete_ds']
    rvars     =   state['rvars']
    var_map   =   state['map']    
#    for i in c_nodes:
#        g.add_vertex(name=i)        
    g.add_nodes_from(c_nodes)    
    #g.node_attr['shape']='box'
    g.add_nodes_from(rvars, color='green', shape='none' )        
    for v in rvars:
        concrete_n = var_map[v]
        g.add_edge(v,concrete_n, color = 'green' )        
        chk = is_equal_intrepretation(state, v, 'null' )
        print 'is_eq', chk, v
                    
        if  not chk:                    
            next_concrete_n = next_edge_get(state,v)
            if next_concrete_n != None:
                print 'is_eq adding edge for', v, chk, concrete_n, next_concrete_n                 
                edge_label = str(v) + '.next'
                g.add_edge(concrete_n,next_concrete_n, label = edge_label)
    #s=g.string()
    g.layout(prog='dot')
    g.draw(prefix + '.png')
    
    
    

#from igraph import *

from pygraphviz import *


def next_edge_get(state,c_node):
    var_map   =   state['map']     
    from opSemantics import next_concrete_node_of_c_node_get
    from opSemantics import nstar_relation_name_get
    n_ptr = nstar_relation_name_get()    
    next_node = next_concrete_node_of_c_node_get(c_node,n_ptr, state)    
    return next_node
        

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
        
    for n in c_nodes:        
        next_concrete_n = next_edge_get(state,n)
        #print 'current_node', n, 'next_node', next_concrete_n
        if next_concrete_n != None:
            #print 'is_eq adding edge for', n, chk, concrete_n, next_concrete_n
            #edge_label = str(v) + '.next'
            g.add_edge( n,next_concrete_n )
    #s=g.string()
    g.layout(prog='dot')
    g.draw(prefix + '.png')
    
    
    

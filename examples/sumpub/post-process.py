import sys
import re

axiom_pat = re.compile(r'axiom\s*(\w+)\s*=')
lemma_pat = re.compile(r'lemma\s*(\w+)\s*=')
funtype_pat = re.compile(r'function\s*(\w+)\s*:\s*(\w+) -> \((\w+) -> (\w+)\)')
sim_pred_pat = re.compile(r'\s*predicate listpub\s+.*=')
has_node_type_pat = re.compile(r'\s*\(hasNodeType s n\) -> false')
# sum_diverges_pat = re.compile(r'\s*let sum \(s: state\) \(self: reference\) : int')
# bisum_diverges_pat = re.compile(r'\s*int\)')
# bisum_meth_pat = re.compile(r'\s*let sum \(l_s: state\)')
diverges_pat = re.compile(r'@\s*diverge')

# sim_pred = (
#     '  inductive listpub (s:state) (n:reference) (l:intList) =\n'
#     '  | listpub_nil : forall s. listpub s nullConst Nil\n'
#     '  | listpub_del : forall s:state, n:reference, l:intList.\n'
#     '    n \: s.alloct ->\n'
#     '    hasNodeType s n ->\n'
#     '    s.heap.pub[n] = false ->\n'
#     '    listpub s (s.heap.nxt[n]) l ->\n'
#     '    listpub s n l\n'
#     '  | listpub_pub : forall s:state, n:reference, l:intList.\n'
#     '    n \: s.alloct ->\n'
#     '    hasNodeType s n ->\n'
#     '    s.heap.pub[n] = true ->\n'
#     '    listpub s (s.heap.nxt[n]) l ->\n'
#     '    listpub s n (Cons s.heap.value[n] l)\n'
#     '\n'
# )

sum_diverges = '  let sum (s: state) (self: reference) : int diverges'

with open(sys.argv[1], 'r') as f:
    for line in f:
        linep = axiom_pat.sub(r"axiom \1 :",line)
        linep = lemma_pat.sub(r"lemma \1 :",linep)
        linep = funtype_pat.sub(r"function \1 : \2 -> \3 -> \4",linep)
        # linep = sim_pred_pat.sub(sim_pred,linep)
        # linep = has_node_type_pat.sub('',linep)
        # linep = sum_diverges_pat.sub(sum_diverges,linep)
        # linep = bisum_diverges_pat.sub('    int) diverges',linep)
        # linep = bisum_meth_pat.sub('  let bisum (l_s: state)',linep)
        linep = diverges_pat.sub(' diverges',linep)
        print (linep, end = '')

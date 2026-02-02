import sys
import re

axiom_pat = re.compile(r'axiom\s*(\w+)\s*=')
lemma_pat = re.compile(r'lemma\s*(\w+)\s*=')
combineAux_pat = re.compile(r'let combineAux.*$')
combine_pat = re.compile(r'let combine \(s: state\).*$')
deleteMin_pat = re.compile(r'let deleteMin \(s: state\).*$')
dijkstra_NODEC_pat = re.compile(r'let dijkstra_NODEC \(s: state\).*$')
dijkstra_pat = re.compile(r'let dijkstra \(s: state\).*$')
main_pat = re.compile(r'let main \(s: state\).*$')

combineAux_subst = (
    "let combineAux (s: state) (self: reference) (handle: reference)"
    ": reference diverges"
)

combine_subst = (
    "let combine (s: state) (self: reference) (handle: reference)"
    ": reference diverges"
)

deleteMin_subst = (
    "let deleteMin (s: state) (self: reference) : reference diverges"
)

dijkstra_NODEC_subst = (
    "let dijkstra_NODEC (s: state) (g: reference) (source: int) : reference"
    " diverges"
)

dijkstra_subst = (              # Client 2 that uses mathematical graphs
    "let dijkstra (s: state) (g: graph) (source: int) : reference"
    " diverges"
)

main_subst = (
    "let main (s: state) (g: graph) (source: int) : reference"
    " diverges"
)

with open(sys.argv[1], 'r') as f:
    for line in f:
        line = axiom_pat.sub(r"axiom \1 :",line)
        line = lemma_pat.sub(r"lemma \1 :",line)
        line = combineAux_pat.sub(combineAux_subst,line)
        line = combine_pat.sub(combine_subst,line)
        line = deleteMin_pat.sub(deleteMin_subst,line)
        line = dijkstra_NODEC_pat.sub(dijkstra_NODEC_subst,line)
        line = dijkstra_pat.sub(dijkstra_subst,line)
        line = main_pat.sub(main_subst,line)
        print(line,end='')


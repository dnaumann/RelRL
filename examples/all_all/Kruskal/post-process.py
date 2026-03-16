import sys
import re

axiom_pat = re.compile(r'axiom\s*(\w+)\s*=')
lemma_pat = re.compile(r'lemma\s*(\w+)\s*=')

init_Ufind_pat = re.compile(r'let init_Ufind.*$')
init_Ufind_subst = (
  "let init_Ufind (s: state) (self: reference) (k: int) : unit"
  " diverges"
)

ufUnion_pat = re.compile(r'let ufUnion \(s: state\).*$')
ufUnion_subst = (
    "let ufUnion (s: state) (self: reference) (x: int) (y: int) : unit"
    " diverges"
)

main_pat = re.compile(r'let main.*$')
main_subst = (
    "let main (s: state) (g: graph) : reference diverges"
)

with open(sys.argv[1], 'r') as f:
    for line in f:
        line = axiom_pat.sub(r'axiom \1 :',line)
        line = lemma_pat.sub(r'lemma \1 :',line)
        line = init_Ufind_pat.sub(init_Ufind_subst,line)
        line = ufUnion_pat.sub(ufUnion_subst,line)
        line = main_pat.sub(main_subst,line)
        print(line,end='')

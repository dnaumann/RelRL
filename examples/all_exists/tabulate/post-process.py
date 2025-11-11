import sys
import re

axiom_pat = re.compile(r'axiom\s*(\w+)\s*=')
lemma_pat = re.compile(r'lemma\s*(\w+)\s*=')
tabulate_pat = re.compile(r'let tabulate \(s: state\).*$')
tabulate_subst = (
    "let tabulate (s: state) (n: int) : reference"
    " diverges"
)
bitabulate_pat = re.compile(r'\(reference, reference\).*$')
bitabulate_subst = (
    "    (reference, reference) diverges"
)

diverges_pat = re.compile(r'@\s*diverge')

with open(sys.argv[1], 'r') as f:
    for line in f:
        line = axiom_pat.sub(r"axiom \1 :",line)
        line = lemma_pat.sub(r"lemma \1 :",line)
        # line = tabulate_pat.sub(tabulate_subst,line)
        # line = bitabulate_pat.sub(bitabulate_subst,line)
        line = diverges_pat.sub(' diverges',line)
        print(line, end = ' ')

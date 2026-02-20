#!/usr/bin/env python3
"""
Script to add stackRep_mono and stackRep_agree lemmas at the beginning of module ListStack
after the imports (use statements).
"""

import re
import sys
from pathlib import Path

def find_stackrep_predicate(lines, module_start):
    """
    Find the stackRep predicate/inductive definition.
    Returns (start_idx, end_idx) where to replace, or None if not found.
    """
    stackrep_start = None
    
    # Find 'inductive stackRep' or 'predicate stackRep' within the module
    for i in range(module_start, len(lines)):
        if 'stackRep' in lines[i] and ('inductive' in lines[i] or 'predicate' in lines[i]):
            stackrep_start = i
            break
    
    if stackrep_start is None:
        return None
    
    # Find the end of the stackRep definition
    # Look for the next top-level construct at same indentation level (starts with 2 spaces)
    stackrep_end = None
    
    for i in range(stackrep_start + 1, len(lines)):
        line = lines[i]
        stripped = line.strip()
        
        # Skip empty lines and comments
        if stripped == '' or stripped.startswith('(*'):
            continue
        
        # Check if this line starts a new top-level definition (2 spaces indentation)
        if line.startswith('  ') and not line.startswith('    '):
            # This is a new top-level construct
            if stripped.startswith(('predicate ', 'let ', 'val ', 'function ', 
                                   'axiom ', 'lemma ', 'inductive ', 'end ')):
                stackrep_end = i
                break
    
    if stackrep_end is None:
        # Couldn't find end, skip replacement
        return None
    
    return (stackrep_start, stackrep_end)


def find_insertion_point(lines):
    """
    Find the insertion point: the stackRep predicate/inductive location within module ListStack
    including the following two lemmas (stackRep_mono and stackRep_agree).
    If ListStack doesn't exist or stackRep is not found, returns None.
    Returns a tuple (start_idx, end_idx) for the range to replace.
    """
    liststack_idx = None
    
    # Find the module ListStack line
    for i, line in enumerate(lines):
        if 'module ListStack' in line:
            liststack_idx = i
            break
    
    if liststack_idx is None:
        # ListStack module doesn't exist in this file
        return None
    
    # Find the stackRep predicate
    stackrep_range = find_stackrep_predicate(lines, liststack_idx)
    
    if stackrep_range is None:
        # stackRep predicate not found
        return None
    
    return stackrep_range

def add_lemmas(file_path):
    """
    Replace the stackRep predicate in module ListStack with the two lemmas.
    If module ListStack or stackRep predicate doesn't exist, the script exits gracefully.
    """
    
    file_path = Path(file_path)
    
    if not file_path.exists():
        raise FileNotFoundError(f"File not found: {file_path}")
    
    # Read the file
    with open(file_path, 'r') as f:
        lines = f.readlines()
    
    # Find where to replace the stackRep predicate
    replacement_range = find_insertion_point(lines)
    
    # If stackRep predicate not found, skip
    if replacement_range is None:
        print(f"ℹ  stackRep predicate not found in {file_path}. Lemmas not added.")
        return
    
    start_idx, end_idx = replacement_range
    
    # The lemmas to add
    lemmas = r'''

  inductive stackRep (s: state) (l: list int) (m: reference) =
  | nil_stack : 
      forall s2: state. 
      stackRep s2 Nil null
  | cons_stack : 
      forall s2: state, m1: reference, l1: list int.
      isAllocated s2 m1 ->
      hasNodeType s2 m1 ->
      (* The definition requires the head cell to be allocated to access its value *)
      isAllocated s2 s2.car[m1] -> 
      hasCellType s2 s2.car[m1] ->
      (let nxt2 = s2.cdr[m1] in
       let new_cell1 = s2.car[m1] in
       let v2 = s2.cell_value[new_cell1] in
       stackRep s2 l1 nxt2 -> 
       stackRep s2 (Cons v2 l1) m1)


  lemma stackRep_mono :
    forall s old_s: state, l: list int, p: reference.
    (* Precondition: The stack is valid in the old state *)
    stackRep old_s l p ->
    
    (* 1. Allocation Monotonicity: Old objects remain allocated *)
    (forall x: reference. isAllocated old_s x -> isAllocated s x) ->
    
    (* 2. Type Preservation: Old objects retain their types *)
    (forall x: reference. isAllocated old_s x -> hasNodeType old_s x -> hasNodeType s x) ->
    
    (* 3. Structural Preservation: car/cdr fields match for old Nodes *)
    (forall x: reference. isAllocated old_s x -> hasNodeType old_s x ->
      (old_s.car)[x] = (s.car)[x] /\ (old_s.cdr)[x] = (s.cdr)[x]) ->
    
    (* 4. Data Preservation: cell_value matches for old Cells *)
    (forall x: reference. isAllocated old_s x -> hasCellType old_s x ->
      (old_s.cell_value)[x] = (s.cell_value)[x]) ->
      
    (* Conclusion: The stack is valid in the new state *)
    stackRep s l p

    lemma stackRep_agree :
    forall s1 s2: state, l: list int, p: reference, r: rgn.
    (* Precondition: The stack is valid in s1 *)
    stackRep s1 l p ->
    
    (* 1. Footprint: The head p is either null or inside the region r *)
    (p = null \/ Rgn.mem p r) ->
    
    (* 2. Closure: The region r is closed under cdr and car in s1 *)
    (forall x. Rgn.mem x r -> hasNodeType s1 x -> Rgn.mem ((s1.cdr)[x]) r) ->
    (forall x. Rgn.mem x r -> hasNodeType s1 x -> Rgn.mem ((s1.car)[x]) r) ->
    
    (* 3. Agreement: s1 and s2 agree on everything inside r *)
    (forall x. Rgn.mem x r ->
      isAllocated s2 x /\
      (hasNodeType s1 x -> hasNodeType s2 x) /\
      (* Nodes in r have same links *)
      (hasNodeType s1 x -> (s1.car)[x] = (s2.car)[x] /\ (s1.cdr)[x] = (s2.cdr)[x]) /\
      (* Cells in r have same values *)
      ((not hasNodeType s1 x) -> (s1.cell_value)[x] = (s2.cell_value)[x])
    ) ->
    
    (* Conclusion *)
    stackRep s2 l p

'''
    
    # Replace the stackRep predicate with the lemmas
    new_lines = lines[:start_idx] + [lemmas] + lines[end_idx:]
    
    # Write back to file
    with open(file_path, 'w') as f:
        f.writelines(new_lines)
    
    print(f"✓ stackRep predicate replaced successfully in {file_path}")
    print(f"  Replacement range: lines {start_idx + 1}-{end_idx}")
if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: python add_lemmas.py <file_path>")
        print("\nExample:")
        print("  python add_lemmas.py prog.mlw")
        sys.exit(1)
    
    file_path = sys.argv[1]
    
    try:
        add_lemmas(file_path)
    except Exception as e:
        print(f"✗ Error: {e}", file=sys.stderr)
        sys.exit(1)

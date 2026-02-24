#!/bin/sh -eu
# regression tests for why3


To replay all session files within your `examples` directory and its descendants, you would use the `run_dir` function defined in the script.

However, looking at the script's internal logic, it is designed with a specific directory depth in mind. Let’s look at how to handle this based on how your folders are structured.

### Option 1: Using the existing script (One level of nesting)

The script’s `run_dir` function uses this line to find files:
`LIST=$(ls $1/*/why3session.xml)`

This looks for `why3session.xml` exactly **two levels down** (e.g., `examples/my_project/why3session.xml`). If your subfolders match this structure, you can simply add a line to the bottom of the script:

```bash
run_dir examples ""

```

---

### Option 2: Handling deep "Sub-subfolders" (Recursive)

If your files are buried deeper (e.g., `examples/folder/subfolder/subsubfolder/why3session.xml`), the standard `ls $1/*/why3session.xml` in the script will **miss them**.

To fix this so it finds **all** descendants, you should modify the `run_dir` function inside the script. Change the `else` block (around line 52) from `ls` to `find`:

```bash
# Change this:
# LIST=`ls $1/*/why3session.xml`

# To this:
LIST=`find $1 -name "why3session.xml"`

```

Once you make that change, running `./script.sh` with `run_dir examples ""` will catch every session file regardless of how deep it is.

---

### Option 3: Running a "Quick" manual command

If you don't want to modify the script and just want to trigger the Why3 replay logic on all descendants manually using the same flags the script uses, you can run this from your terminal:

```bash
find examples -name "why3session.xml" -exec dirname {} \; | xargs -I {} ../bin/why3.opt replay -q {}

```

### Summary of what to do:

1. **Open the script.**
2. **Scroll to the bottom** where the `run_dir` calls are.
3. **Add** `run_dir examples ""` (assuming your `examples` folder is in the same directory as the script).
4. **If your folders are very deep**, apply the `find` modification mentioned in Option 2.

**Would you like me to rewrite the `run_dir` function for you so it supports deep recursion automatically?**

REPLAYOPT=""
REGTESTS_MODE=""

while test $# != 0; do
case "$1" in
  "--force")
        REPLAYOPT="$REPLAYOPT --force"
        ;;
  "--obsolete-only")
        REPLAYOPT="$REPLAYOPT --obsolete-only"
        ;;
  "--ignore-shapes")
        REPLAYOPT="$REPLAYOPT --ignore-shapes"
        ;;
  "--prover")
        REPLAYOPT="$REPLAYOPT --prover $2"
        shift
        ;;
  "--reduced-mode")
        REGTESTS_MODE="REDUCED"
        ;;
  "--examples-mode")
        REGTESTS_MODE="EXAMPLES"
        ;;
  *)
        echo "$0: Unknown option '$1'"
        exit 2
esac
shift
done

TMP=$PWD/why3regtests.out
TMPERR=$PWD/why3regtests.err

# Current directory is /examples
cd `dirname $0`

# too early to do that
# REPLAYOPT="$REPLAYOPT --smoke-detector top"

res=0
export success=0
export total=0
export sessions=""
export shapes=""


run_dir () {
    if [ "$REGTESTS_MODE" = "REDUCED" ]; then
        if [ -f $1/reduced_regtests.list ]; then
            LIST=`sed $1/reduced_regtests.list -n -e "s&^\([^ #]\+\).*&$1/\1/why3session.xml&p"`
        else
            LIST=
        fi
    else
        LIST=`ls $1/*/why3session.xml`
    fi
    for f in $LIST; do
        d=`dirname $f`
        printf "Replaying $d ... "
        if ../bin/why3.opt replay -q $REPLAYOPT $2 $d 2> $TMPERR > $TMP ; then
            printf "OK"
            cat $TMP $TMPERR
            success=`expr $success + 1`
        else
            ret=$?
            printf "FAILED (ret code=$ret):"
            out=`head -1 $TMP`
            if test -z "$out" ; then
               echo "standard error: (standard output empty)"
               cat $TMPERR
            else
               cat $TMP
            fi
            res=1
        fi
        total=`expr $total + 1`
    done
    sessions="$sessions $1/*/why3session.xml"
    shapes="$shapes $1/*/why3shapes.gz"
}

echo "=== Examples and Case Studies === MUST REPLAY AND ALL GOALS PROVED ==="
echo ""
run_dir . ""
run_dir micro-c ""
run_dir python ""
run_dir double_wp "-L double_wp"
run_dir avl "-L avl"
run_dir c_cursor "-L c_cursor"
run_dir foveoos11-cm ""
run_dir vacid_0_binary_heaps "-L vacid_0_binary_heaps"
run_dir verifythis_2016_matrix_multiplication "-L verifythis_2016_matrix_multiplication"
run_dir WP_revisited ""
run_dir prover "-L prover --warn-off=unused_variable"
run_dir multiprecision "-L multiprecision"
run_dir c_cursor "-L c_cursor"
run_dir numeric ""
echo ""

echo "Score on Examples and Case Studies: $success/$total"
echo ""

if [ "$REGTESTS_MODE" != "EXAMPLES" ]; then
echo "=== Standard Library ==="
echo ""
run_dir stdlib ""
echo ""

echo "=== Tests ==="
echo ""
# there's no session there...
# run_dir tests
run_dir tests-provers ""
echo ""

echo "=== Check Builtin translation ==="
echo ""
run_dir check-builtin ""
echo ""

echo "=== BTS ==="
echo ""
run_dir bts ""
echo ""

echo "=== Logic ==="
echo ""
run_dir logic ""
run_dir bitvectors "-L bitvectors"
echo ""

echo "=== MLCFG ==="
echo ""
run_dir mlcfg ""
echo ""

fi

echo "Summary       : $success/$total"
echo "Sessions size : "`wc -cl $sessions | tail -1`
echo "Shapes   size : "`wc -cl $shapes | tail -1`

exit $res

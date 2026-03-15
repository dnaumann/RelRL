/*
[forall]
int cs;
int cr;
int ci;
int ct;
int ccs;
int ccr;
int cci;
int cct;
int res;

res = cs - ccs;

if (res == 0) {
    res = cr - ccr;
}

if (res == 0) {
    res = ci - cci;
}

if (res == 0) {
    res = ct - cct;
}

[forall]
int cs;
int cr;
int ci;
int ct;
int ccs;
int ccr;
int cci;
int cct;
int res;

res = cs - ccs;

if (res == 0) {
    res = cr - ccr;
}

if (res == 0) {
    res = ci - cci;
}

if (res == 0) {
    res = ct - cct;
}


[pre]

(cs_0 == ccs_1)
&&
(cr_0 == ccr_1)
&&
(ci_0 == cci_1)
&&
(ct_0 == cct_1)
&&
(ccs_0 == cs_1)
&&
(ccr_0 == cr_1)
&&
(cci_0 == ci_1)
&&
(cct_0 == ct_1)

[post]

((res_0 == 0) && (res_1 == 0))
||
((res_0 < 0) && (res_1 > 0))
||
((res_0 > 0) && (res_1 < 0))

*/

var cs, cs': int;
var cr, cr': int;
var ci, ci': int;
var ct, ct': int;
var ccs, ccs': int;
var ccr, ccr': int;
var cci, cci': int;
var cct, cct': int;
var res, res': int;


// verifies
procedure biprog () 
    returns (res: int, res': int)
  requires  (cs == ccs') &&
            (cr == ccr') &&
            (ci == cci') &&
            (ct == cct') &&
            (ccs == cs') &&
            (ccr == cr') &&
            (cci == ci') &&
            (cct == ct');
  ensures ((res == 0) && (res' == 0)) ||
            ((res < 0) && (res' > 0)) ||
            ((res > 0) && (res' < 0));
{
   
    res := cs - ccs; res' := cs' - ccs';

    if (res == 0) {
        res := cr - ccr;
    }

    if (res' == 0) {
        res' := cr' - ccr';
    }

    if (res == 0) {
        res := ci - cci;
    }

    if (res' == 0) {
        res' := ci' - cci';
    }

    if (res == 0) {
        res := ct - cct;
    }

    if (res' == 0) {
        res' := ct' - cct';
    }

}
/*

a higher-order con-
dition 𝐻 RP to the module RP, given in Fig. 7, which is given as
a function from conditions to conditions. Concretely, given
𝑆 f , for arguments 𝑓 , 𝑛, 𝑚 and a mathematical function 𝑓sem ,
the condition 𝐻 RP (𝑆 f ) assumes 𝑆 f to include the expected
specification for *𝑓 (saying that *𝑓 is pure with measure ⟨𝜔⟩
and returns 𝑓sem (𝑚) for any argument 𝑚), and then guaran-
tees that the return value is 𝑓sem𝑛 (𝑚). Here 𝜔 is the smallest
ordinal bigger than every natural number and thus *𝑓 is
allowed to have any finite recursion depth. Also we require
RP.repeat to be pure with measure ⟨𝜔 + 𝑛⟩ because it makes
recursive calls with depth 𝑛 followed by a call to *𝑓 .

Figure 7


P_RP := [Module RP]
def repeat(f:ptr, n:int64 , m:int64 ) ≡
  if n ≤ 0 then return m
  else { var v := (*f)(m)
    return RP.repeat(f, n-1, v) }

P_SC := [Module SC] def succ(m:int64 ) ≡ m + 1


P_AD := [Module AD]
def main() ≡
  var n := getint()
  print(str(RP.repeat(&SC.succ,n,n)))

A_AD := [Module AD]
def main() ≡
  var n := getint()
  print(str(n + n))

*/

/* Figure 3 example
simple implementation 𝑃App  for
the module App of the motivating example. We incrementally
verify it against 𝐴App via 𝐼 App just for presentation purposes.



P_AP :=
[Module App]
local initialized := false local mres := Run

def init() ≡

  if (initialized) {
    print("error: init")
  } else {
    initialized := true
    MW.put(0, 42)
  }

def run() ≡
  if (!initialized) {
    print("error: run")
  } else {
    var v := MW.get(0)
    print("val:"+str(v))
  }


I_App :=

[Module App]
local mres := Run
def init() ≡
  var frm := Asm(𝜆𝜎. 𝜎 ≥ Init, 𝜀)
  frm := Grt(𝜆𝜎. True, frm) 
  MW.put(0, 42)
  frm := Asm(𝜆𝜎. True, frm) 
  Grt(𝜆𝜎. 𝜎 ≥ Run, frm)

def run() ≡
  var frm := Asm(𝜆𝜎. 𝜎 ≥ Run, 𝜀)
  frm := Grt(𝜆𝜎. True, frm) 
  var v := MW.get(0)
  frm := Asm(𝜆𝜎. True, frm) 
  print("val:"+str(v))
  Grt(𝜆𝜎. 𝜎 ≥ Run, frm)


A_App :=
[Module App]

local mres := Run
def init() ≡
  var fi := take(int64 → int?64 )
  var frm := Asm(𝜆𝜎. 𝜎 ≥ Init + MWhas(fi), 𝜀)
  var fe := choose(int64 → int?64 )
  frm := Grt(𝜆𝜎. 𝜎 ≥ MWhas(fe), frm)
  MW.put(0, 42)
  frm := Asm(𝜆𝜎. 𝜎 ≥ MWhas(fe[0 ← 42]), frm)
  Grt(𝜆𝜎. 𝜎 ≥ Run + MWhas(fi[0 ← 42]), frm)

def run() ≡
  var fi := take(int64 → int?64 )
  var frm := Asm(𝜆𝜎. 𝜎 ≥ Run + MWhas(fi) ∧ fi(0) = Some 42, 𝜀)
  var (fe, ve) := choose((int64 → int?64 ) × int64 )
  frm := Grt(𝜆𝜎. 𝜎 ≥ MWhas(fe) ∧ fe(0) = Some ve, frm)
  var v := MW.get(0)
  frm := Asm(𝜆𝜎. 𝜎 ≥ MWhas(fe) ∧ v = ve, frm)
  print("val:"+str(42))
  Grt(𝜆𝜎. 𝜎 ≥ Run + MWhas(fi) ∧ fi(0) = Some 42, frm)

  */
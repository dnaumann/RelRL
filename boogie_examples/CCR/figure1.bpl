/* Taken from conditional contextual refinement 2022 archive paper
Figure 1 motivating example

the module MW is intended for a simple middleware,
1 and 𝑃 2 are two (equivalent) implementations for it
and 𝑃MW
MW
performing different optimizations written in green.
To see what MW does, we look at the common black part
1 and 𝑃 2 . The middleware starts with main(), which
of 𝑃 MW
MW
creates a partial map from int64 to int64 by Map.new(), ini-
tializes the application by App.init(), and keeps running it
by App.run(). It also provides a map service to the app with
put(i,v), which maps i to v via Map.update and prints
a log, and get(i), which returns the mapped value at the
index i obtained via Map.get after printing a log.


P1_MW :=
[Module MW]

local arr
local map

def main() ≡
  arr := Mem.alloc(100)
  map := Map.new()
  App.init()
  while (true)
    App.run()

def put(i:int64 ,v:int64 ) ≡
  if (0 <= i && i < 100)
    Mem.store(arr + i, v)
  else
    Map.update(map, i, v)
  print("put:"+str(i)+str(v)) 

def get(i:int64 ) ≡
  var r
  if (0 <= i && i < 100)
    r := Mem.load(arr + i)
  else
    r := Map.get(map, i)
  print("get:"+str(i)+str(r))
  return r


P2_MW :=
[Module MW]
local first, idx, data
local map

def main() ≡
  first := true
  map := Map.new()
  App.init()
  while (true)
    App.run()

def put(i:int64 ,v:int64 ) ≡ 
  if (first || i == idx) {
      first := false
      idx := i
      data := v
  } else
    Map.update(map, i, v)
  print("put:"+str(i)+str(v)) 

def get(i:int64 ) ≡
  var r
  if (idx == i)
    r := data
  else
    r := Map.get(map, i)
  print("get:"+str(i)+str(r)) 
  return r


I_MW :=

[Module MW]

local cls, opt
local map

def main() ≡
  cls := opt := (fun _ => 0)
  map := Map.new()
  App.init()
  while (true)
    App.run()

def put(i:int64 ,v:int64 ) ≡
  if (cls(i) == 0)
    cls := cls[i ← choose({1,2})]
  if (cls(i) == 1)
    opt := opt[i ← v]
  else
    Map.update(map, i, v)
  print("put:"+str(i)+str(v))

def get(i:int64 ) ≡
  var r
  assume(cls(i) != 0)
  if (cls(i) == 1)
    r := opt(i)
  else
    r := Map.get(map, i)
  print("get:"+str(i)+str(r)) 
  return r


A_MW :=

[Module MW]
local full

def main() ≡
  full := (fun _ => 0)
  App.init()
  while (true)
    App.run()

def put(i:int64 ,v:int64 ) ≡
  full := full[i ← v]
  print("put:"+str(i)+str(v))

def get(i:int64 ) ≡
  var r
  r := full(i)
  print("get:"+str(i)+str(r))
  return r

*/

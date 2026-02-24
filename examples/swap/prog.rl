/* commuting method calls */

interface A =

  class K { a: int; b: int; }

  meth f (self:K, k:int) : unit
    ensures { self.a = k }
    effects { rw {self}`a; rd self, k }

  meth g (self:K, k:int) : unit
    ensures { self.b = k }
    effects { rw {self}`b; rd self, k }

  meth m (self:K, k:int) : unit
    ensures { self.a = k /\ self.b = k }
    effects { rw {self}`any; rd self, k }

end

module A0 : A =

  class K { a: int; b: int; }

  meth f (self:K, k:int) : unit =
    self.a := k;

  meth g (self:K, k:int) : unit =
    self.b := k;

  meth m (self:K, k:int) : unit =
    f (self, k);
    g (self, k);

end

module A1 : A =

  class K { a: int; b: int; }

  meth f (self:K, k:int) : unit =
    self.a := k;

  meth g (self:K, k:int) : unit =
    self.b := k;

  meth m (self:K, k:int) : unit =
    g (self, k);
    f (self, k);

end

bimodule A_REL (A0 | A1) =

  meth f (self:K, k:int | self:K, k:int) : (unit | unit)
    requires { Agree self }
    requires { Agree k }
    ensures  { Agree {self}`a }
    effects  { rw {self}`a; rd self, k | rw {self}`a; rd self, k }
  = |_ self.a := k _|;

  meth g (self:K, k:int | self:K, k:int) : (unit | unit)
    requires { Agree self }
    requires { Agree k }
    ensures  { Agree {self}`b }
    effects  { rw {self}`b; rd self, k | rw {self}`b; rd self, k }
  = |_ self.b := k _|;

  meth m (self:K, k:int | self:K, k:int) : (unit | unit)
    requires { Agree self }
    requires { Agree k }
    ensures  { Agree {self}`a /\ Agree {self}`b }
    effects  { rw {self}`any; rd self, k | rw {self}`any; rd self, k }
  = ( f(self,k) | g(self,k) );
    ( g(self,k) | f(self,k) );

  meth m2 (self:K, k:int | self:K, k:int) : (unit | unit)
    requires { Agree self }
    requires { Agree k }
    ensures  { Agree {self}`a /\ Agree {self}`b }
    effects  { rw {self}`any; rd self, k | rw {self}`any; rd self, k }
  = ( f(self,k); g(self,k) | g(self,k); f(self,k) );

end

/* commuting method calls */

interface A =

  class K { a: int; b: int; }

  meth f (self:K, t:int) : unit
    ensures { self.a = t }
    effects { rw {self}`a; rd self, t }

  meth g (self:K, s:int) : unit
    ensures { self.b = s }
    effects { rw {self}`b; rd self, s }

  meth m (self:K, s:int) : unit
    ensures { self.a = s /\ self.b = s }
    effects { rw {self}`any; rd self, s }

end

module A0 : A =

  class K { a: int; b: int; }

  meth f (self:K, t:int) : unit =
    self.a := t;

  meth g (self:K, s:int) : unit =
    self.b := s;

  meth m (self:K, s:int) : unit =
    f (self, s);
    g (self, s);

end

module A1 : A =

  class K { a: int; b: int; }

  meth f (self:K, t:int) : unit =
    self.a := t;

  meth g (self:K, s:int) : unit =
    self.b := s;

  meth m (self:K, s:int) : unit =
    g (self, s);
    f (self, s);

end

bimodule A_REL (A0 | A1) =

  meth f (self:K, t:int | self:K, t:int) : (unit | unit)
    requires { Agree self }
    requires { Agree t }
    ensures  { Agree {self}`a }
    effects  { rw {self}`a; rd self, t | rw {self}`a; rd self, t }
  = |_ self.a := t _|;

  meth g (self:K, s:int | self:K, s:int) : (unit | unit)
    requires { Agree self }
    requires { Agree s }
    ensures  { Agree {self}`b }
    effects  { rw {self}`b; rd self, s | rw {self}`b; rd self, s }
  = |_ self.b := s _|;

  meth m (self:K, s:int | self:K, s:int) : (unit | unit)
    requires { Agree self }
    requires { Agree s }
    ensures  { Agree {self}`a /\ Agree {self}`b }
    effects  { rw {self}`any; rd self, s | rw {self}`any; rd self, s }
  = ( f(self,s) | g(self,s) );
    ( g(self,s) | f(self,s) );

  meth m2 (self:K, s:int | self:K, s:int) : (unit | unit)
    requires { Agree self }
    requires { Agree s }
    ensures  { Agree {self}`a /\ Agree {self}`b }
    effects  { rw {self}`any; rd self, s | rw {self}`any; rd self, s }
  = ( f(self,s); g(self,s) | g(self,s); f(self,s) );

end

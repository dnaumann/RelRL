interface CELL =
  class Cell { cell_value: int; cell_rep: rgn; }
  meth Cell(self:Cell, k:int) : unit
    ensures { self.cell_value = k }
    ensures { self.cell_rep = {self} }
    effects { rw {self}`any; rd self, k }
end

module Cell : CELL =
  class Cell { cell_value: int; cell_rep: rgn; }
  meth Cell(self:Cell, k:int) : unit
  = self.cell_value := k; self.cell_rep := {self};
end
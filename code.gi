
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Class(loopc, loop_base, rec(
   __call__ := (self, loopvar, range, cnd, cmd) >> WithBases(self,
               rec(operations := CmdOps, cmd := cmd, var := loopvar, range := listRange(range), cnd := cnd)),
   rChildren := self >> [self.var, self.range, self.cnd, self.cmd],
   rSetChild := rSetChildFields("var", "range", "cnd", "cmd"),

   print := (self, i, si) >> Print(self.__name__, "(", self.var, ", ",
       self.range, ", ", self.cnd, ",\n", Blanks(i+si),
       self.cmd.print(i+si, si),
       Print("\n", Blanks(i), ")")),
   free := self >> self.cmd.free()
));

Class(creturn, throw);
Class(creturnCond, throw);

Class(isinf, AutoFoldExp, rec(
  ev := self >> self._ev(self.args).ev(), 
  computeType := self >> TBool,
));

Class(isnan, AutoFoldExp, rec(
  ev := self >> self._ev(self.args).ev(), 
  computeType := self >> TBool,
));


# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Class(arctan, AutoFoldExp, rec(
  ev := self >> self._ev(self.args).ev(),  
  computeType := self >> TReal, 
));


Class(TArcTan, Tagged_tSPL_Container, rec(
    abbrevs :=  [ () -> []],
    dims := self >> [1, 2],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    isReal := True
));


NewRulesFor(TArcTan, rec(
    TArcTan_Base := rec(
        applicable := True,
        forTransposition := false,
        apply := (t, C, Nonterms) -> let( x := var.fresh_t("r", TDouble), y := var.fresh_t("r", TDouble),
            OLCompose(BinOp(1, Lambda([x,y], arctan(x,y)))))
    )
));


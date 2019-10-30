
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Class(HCOLUnparserMixin, rec(
    copyright := "",
    loopc := (self,o,i,is) >> Checked(IsRange(o.range),
        let(v := o.var, lo := o.range[1], hi := Last(o.range),
            Print(Blanks(i), "for(", v, " = ", lo, "; ", v, self._lt, hi, 
            ", ", self(o.cnd, i, is), "; ", v, "++) {\n",
                self(o.cmd,i+is,is),
                Blanks(i), "}\n"))),
    abs := (self, o, i, is) >> self(cond(geq(o.args[1], V(0)), o.args[1], neg(o.args[1])), i, is),
    pow := (self, o, i, is) >> Cond(o.args[1]=2 and o.args[2]>=0, Print("(2 << ",self(o.args[2], i, is), ")"),
     	    	      	     		Print("pow(", self(o.args[1], i, is), ",", self(o.args[2], i, is), ")") ),	
    creturn := (self, o, i, is) >> Print(Blanks(i), "return ", self(o.args[1], i, is), ";\n"),
	creturnCond := (self, o, i, is) >> Print(Blanks(i), "if (", self(o.args[1], i, is), ")\n",self(creturn(o.args[2]), i+is, is), "\n"),
    SIMDchain := (self, o, i, is) >> Print(Blanks(i), "#pragma omp simd\n", Blanks(i), "#pragma ivdep\n", self(chain(o.cmds),i,is))
));

Class(HCOLUnparser, HCOLUnparserMixin, CUnparser);
Class(HCOLSSEUnparser, HCOLUnparserMixin, SSEUnparser);


# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Class(HCOLCodegen, DefaultCodegen, rec(
    PointWise := (self, o, y, x, opts) >> let(i := Ind(o.N),
        loop(i, o.N, assign(nth(y, i), o.op.at(nth(x, i), i)))),

    ISumReduction := (self, o, y, x, opts) >> let(op := o.op, idval := o.idval, c:=o.child(1), 
        n := Rows(c), t := TempVec(TArray(y.t.base_t(), n)), i := Ind(n), j := Ind(n),
        chain(
            loop(j, n, 
                assign(nth(y,j), idval)),
                
            Cond(o.isSaturated = False,
                loop(o.var, o.domain, decl([t], 
                    chain(
                    self(o.child(1), t, x, opts),
                    loop(i, n, 
                          assign(nth(y,i), op(nth(y,i), nth(t,i))))
                ))),
                loopc(o.var, o.domain, ApplyFunc(logic_and, List([0..n-1], e->logic_neg(o.isSaturated(nth(y,e))))), decl([t], 
                    chain(
                    self(o.child(1), t, x, opts),
                    loop(i, n, 
                          assign(nth(y,i), op(nth(y,i), nth(t,i))))
                )))
            )
        )),

	COND := (self, o, y, x, opts) >> let(
			#Print("Cond:",o.cond, "\nTrue: ", o.child(1), "\nFalse:", o.child(2),"\n"), 
			t := TempVec(TArray(TBool,1)),
			c1:= o.child(1), c2 := o.child(2),
			
			decl([t],
				chain(
					self(o.cond, t, x, opts),
					IF( nth(t, 0),
						self(o.child(1), y, x, opts),
						self(o.child(2), y, x, opts))))),
		
		
		
    Constant := (self, o, y, x, opts) >> assign(y, o.value),

    eT := (self, o, y, x, opts) >> assign(nth(y,0), nth(x, o.base)),

    eUnion := (self, o, y, x, opts) >> When(o.N=0 and o.base=-1, chain(), assign(nth(y, o.base), nth(x,0)) ),

    Mul1 := (self, o, y, x, opts) >> assign(nth(y,0), o.element*nth(x, 0)),

    SUMUnion := (self, o, y, x, opts) >> chain(List(o.children(), c -> self(c, y, x, opts))),

    ISumUnion := (self, o, y, x, opts) >>
       loop(o.var, o.domain, self(o.child(1), y, x, opts)),

    Inductor := (self, o, y, x, opts) >> assign(nth(y,0), cond(eq(o.i,0), o.initval, o.op.at(nth(y,0), nth(x,0)))),

    BinOp := (self, o, y, x, opts) >> let(i := Ind(o.N), 
        loop(i, V(o.N), assign(nth(y,i), o.op.at(nth(x, i), nth(x,i+o.N))))),


    OLCompose := meth(self, o,y,x,opts)
        local ch, numch, vecs;
        ch    := o.children();
        numch := Length(ch);

        # propagate x and y arrays and create temporary arrays
        vecs  := self._composePropagate(ch, y, x, c -> TempArray(y,x,c));


        # order them so that first to be evaluated is first in array.
        vecs := Reversed(vecs);
        ch   := Reversed(ch);

        # Wrap code in variable declaration. Each entry in vecs will contain multiple
        # arrays in the case of multi-input/output (i.e. OL)
        return decl(
            Difference(Flat(vecs{[2..Length(vecs)-1]}), Flat([x,y])),
            chain(
                List([1..numch], i ->
                     self(ch[i], vecs[i+1], vecs[i], opts)))
        );
    end,
                       
));




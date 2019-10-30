
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Declare(OLCompose);

Class(OLCompose, Compose, rec(
    printSeparationChar := " o ",
    toOperator := self >> (vec -> Checked(Length(vec)=self.dims()[2], OLCompose(DropLast(self._children, 1)).toOperator()(Last(self._children).toOperator()(vec))))
));

Class(LinearSystem,  BaseMat, rec(
    abbrevs := [ (A, b) -> [A, b] ],
    new := (self, A, b) >> SPL(WithBases(self, rec(
        mat := A, rhs := b, dimensions := [Rows(A), Cols(A)]))),
    print := (self, i, is) >> Print("LinearSystem(", self.mat, ", ", self.rhs, ")"),
    dims  := self >> self.dimensions,
    rChildren := self >> [self.mat, self.rhs],
    rSetChild := rSetChildFields("mat", "rhs"),
    isReal := True
));

Class(Reduction,  BaseMat, rec(
    abbrevs := [ (N, op, idval, isSaturated) -> [N, op, idval, isSaturated] ],
    new := (self, N, op, idval, isSaturated) >> SPL(WithBases(self, rec(
        N := N, op := op, idval := idval, isSaturated := isSaturated, dimensions := [1, N]))),
    print := (self, i, is) >> Print("Reduction(", self.N, ", ", self.op, ", ", self.idval, ", ", self.isSaturated, ")"),
    dims  := self >> self.dimensions,
    rChildren := self >> [self.N, self.op, self.idval, self.isSaturated],
    rSetChild := rSetChildFields("N", "op", "idval", "isSaturated"),
    transpose := self >> self,
    isReal := True,
    toOperator := self >> (vec -> Checked(Length(vec)=self.dims()[2], [RulesStrengthReduce(FoldL(vec, self.op, self.idval)).v]))
));

Class(Induction,  BaseMat, rec(
    abbrevs := [ (N, op, initval) -> [N, op, initval] ],
    new := (self, N, op, initval) >> SPL(WithBases(self, rec(
        N := N, op := op, initval := initval, dimensions := [N, 1]))),
    print := (self, i, is) >> Print("Induction(", self.N, ", ", self.op, ", ", self.initval, ")"),
    dims  := self >> self.dimensions,
    rChildren := self >> [self.N, self.op, self.initval],
    rSetChild := rSetChildFields("N", "op", "initval"),
    isReal := True,
    recurrence := self >> ((j,v)->When(j=0, self.initval, self.op.at(self.recurrence()(j-1,v),v))),
    toOperator := self >> (vec -> Checked(Length(vec)=self.dims()[2], List([0..self.N-1], i->_unwrap(RulesStrengthReduce(self.recurrence()(i,vec[1]))))))
));

Class(PointWise, BaseMat, rec(
    abbrevs := [ (N, op) -> [N, op] ],
    new := (self, N, op) >> SPL(WithBases(self, rec(
        N := N, op := op, dimensions := [N, N]))),
    print := (self, i, is) >> Print("PointWise(", self.N, ", ", self.op, ")"),
    dims  := self >> self.dimensions,
    rChildren := self >> [self.N, self.op],
    rSetChild := rSetChildFields("N", "op"),
    transpose := self >> self,
    isReal := True,
    toOperator := self >> (vec -> Checked(Length(vec)=self.dims()[2], List([0..Length(vec)-1], j->RulesStrengthReduce(self.op.at(vec[j+1], j)).v)))
));

Class(BinOp, BaseMat, rec(
    abbrevs := [ (N, op) -> [N, op] ],
    new := (self, N, op) >> SPL(WithBases(self, rec(
        N := N, op := op, dimensions := [N, 2*N]))),
    print := (self, i, is) >> Print("BinOp(", self.N, ", ", self.op, ")"),
    dims  := self >> self.dimensions,
    rChildren := self >> [self.N, self.op],
    rSetChild := rSetChildFields("N", "op"),
    isReal := True,
    toOperator := self >> (vec -> Checked(Length(vec)=self.dims()[2], List([1..Length(vec)/2], j->RulesStrengthReduce(self.op.at(vec[j], vec[j+self.N])).v)))
));

Class(ScalarProd,  BaseMat, rec(
    abbrevs := [ (N, scalars) -> [N, scalars] ],
    new := (self, N, scalars) >> SPL(WithBases(self, rec(
        N := N, scalars := scalars, dimensions := [1, N]))),
    print := (self, i, is) >> Print("ScalarProd(", self.N, ", ", self.scalars, ")"),
    dims  := self >> self.dimensions,
    rChildren := self >> [self.N, self.scalars],
    rSetChild := rSetChildFields("N", "scalars"),
    isReal := True,
    toOperator := self >>(vec -> Checked(Length(vec)=self.dims()[2], [_unwrapVec(self.scalars) * vec]))
));

Class(Constant, BaseMat, rec(
    abbrevs := [ x -> [x]],
    new := (self, x) >> SPL(WithBases(self, rec(
    value := x, dimensions := [1,0]))),
    print := (self, i ,is) >> Print("Constant(",self.value,")"),
    dims := self >> self.dimensions,
    rChildren := self >> [self.value],
    rSetChild := rSetChildFields("value"),
    isReal := True
));		

spiral.spl.IterVStack.toOperator := 
  self >> (vec -> Checked(Length(vec)=self.dims()[2], 
                     Flat(List([0..self.var.range-1], 
                        j->RulesStrengthReduce(
                               SubstVars(Copy(self._children[1]), 
                                         rec((self.var.id):=V(j))
                               )
                           ).toOperator()(vec) )
                     )
                  )
          );

spiral.spl.HStack.toOperator := 
   self >> (vec -> Checked(Length(vec)=self.dims()[1]*Length(self.children()), 
      	   	      Sum(List([1..Length(self.children())], 
	                 i->self.children()[i].toOperator()(vec{[(i-1)*self.dims()[1] + 1..i*self.dims()[1]]})
		      ))
	 	   )
           );

spiral.spl.DirectSum.toOperator := self >> (vec -> Checked(Length(vec)=Sum(List(self.children(), i->i.dims()[2])), 
    ApplyFunc(Concat, List([1..Length(self.children())], 
        i->self.children()[i].toOperator()(vec{
            [Sum(List(self.children(){[1..i-1]}, j->j.dims()[2]))+1..Sum(List(self.children(){[1..i]}, j->j.dims()[2]))]
            })))));



spiral.spl.I.N := self >> self.params[1];

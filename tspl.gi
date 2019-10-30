
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Class(TMovingWindow, Tagged_tSPL_Container, rec(
  abbrevs := [(size, op) -> [size, op] ],
  dims := self >> self.params[2].dims(),
  transpose := self >> self,
  isReal := True
));

hf_size := var.fresh_t("t", TInt);

Class(HF, Tagged_tSPL_Container, rec(
  abbrevs := [(op, it) -> [op, it]],
  dims := self >> [self.params[1].dims()[1], hf_size],
  transpose := self >> self,
  isReal := True
));

Class(TBinOp, Tagged_tSPL_Container, rec(
    abbrevs :=  [(x, op, y)->[x, op, y] ],
    dims := self >> [self.params[3].dims()[1], self.params[3].dims()[2]*2 ],
    transpose := self >> self, #CopyFields(self, rec(transposed := not self.transposed)),
   isReal := True
));

NewRulesFor(TBinOp, rec(
  TBinOp_base := rec(
    forTransposition := false,
    applicable := (self, nt) >> true,
    children := nt -> [ nt.params ],
    apply := (t, c, nt) ->
     let(
       OLCompose(
         Reduction(t.dims()[1], op, 0, False)
       ) 
     )
  )
));



Class(TForAllInd, Tagged_tSPL_Container, rec(
    abbrevs :=  [ (ind, exp) -> Checked(IsVar(ind), IsSPL(exp), [ind, exp]) ],
    dims := self >> [self.params[2].dims()[1]*self.params[1].range, self.params[2].dims()[2]],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
   isReal := True
));

Class(TComputeDist, Tagged_tSPL_Container, rec(
  abbrevs := [n -> Checked(IsInt(n), [n]) ], 
  transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
  dims := self >> [1, self.params[1]],
  isReal := True
));


Class(TGreater, Tagged_tSPL_Container, rec(
    binop :=  (a,b)->_unwrap(gt(a,b)),
    lamdaop := (a,b) -> gt(a,b),
    abbrevs :=  [ (t1, t2) -> Checked(IsSPL(t1) and IsSPL(t2), [t1, t2]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [self.params[1].dims()[1], self.params[1].dims()[2] + self.params[2].dims()[2]],
    isReal := True,
    toOperator := self >> (vec -> let(a := vec{[1..self.params[1].dims()[2]]}, b := vec{[self.params[1].dims()[2]+1..self.dims()[2]]},   
        o1 := self.params[1].toOperator(), o2 := self.params[2].toOperator(),
        List(Transposed([o1(a), o2(b)]), i->self.binop(i[1], i[2]))))
));

Class(TLessEqual, Tagged_tSPL_Container, rec(
    binop :=  (a,b)->_unwrap(leq(a,b)),
    lamdaop := (a,b) -> gt(b,a),
    abbrevs :=  [ (t1, t2) -> Checked(IsSPL(t1) and IsSPL(t2), [t1, t2]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [self.params[1].dims()[1], self.params[1].dims()[2] + self.params[2].dims()[2]],
    isReal := True,
    toOperator := self >> (vec -> let(a := vec{[1..self.params[1].dims()[2]]}, b := vec{[self.params[1].dims()[2]+1..self.dims()[2]]},   
        o1 := self.params[1].toOperator(), o2 := self.params[2].toOperator(),
        List(Transposed([o1(a), o2(b)]), i->self.binop(i[1], i[2]))))
));

Class(TGreaterEqual, Tagged_tSPL_Container, rec(
    binop :=  (a,b)->_unwrap(geq(a,b)),
    lamdaop := (a,b) -> geq(a,b),
    abbrevs :=  [ (t1, t2) -> Checked(IsSPL(t1) and IsSPL(t2), [t1, t2]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [self.params[1].dims()[1], self.params[1].dims()[2] + self.params[2].dims()[2]],
    isReal := True,
    toOperator := self >> (vec -> let(a := vec{[1..self.params[1].dims()[2]]}, b := vec{[self.params[1].dims()[2]+1..self.dims()[2]]},   
        o1 := self.params[1].toOperator(), o2 := self.params[2].toOperator(),
        List(Transposed([o1(a), o2(b)]), i->self.binop(i[1], i[2]))))
));

Class(TEqual, Tagged_tSPL_Container, rec(
    binop :=  (a,b)->_unwrap(eq(a,b)),
    lamdaop := (a,b) -> eq(a,b),
    abbrevs :=  [ (t1, t2) -> Checked(IsSPL(t1) and IsSPL(t2), [t1, t2]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [self.params[1].dims()[1], self.params[1].dims()[2] + self.params[2].dims()[2]],
    isReal := True,
    toOperator := self >> (vec -> let(a := vec{[1..self.params[1].dims()[2]]}, b := vec{[self.params[1].dims()[2]+1..self.dims()[2]]},   
        o1 := self.params[1].toOperator(), o2 := self.params[2].toOperator(),
        List(Transposed([o1(a), o2(b)]), i->self.binop(i[1], i[2]))))
));

Class(TLess, Tagged_tSPL_Container, rec(
    binop :=  (a,b)->_unwrap(lt(a,b)),
    lamdaop := (a,b) -> geq(b,a),
    abbrevs :=  [ (t1, t2) -> Checked(IsSPL(t1) and IsSPL(t2), [t1, t2]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [self.params[1].dims()[1], self.params[1].dims()[2] + self.params[2].dims()[2]],
    isReal := True,
    toOperator := self >> (vec -> let(a := vec{[1..self.params[1].dims()[2]]}, b := vec{[self.params[1].dims()[2]+1..self.dims()[2]]},   
        o1 := self.params[1].toOperator(), o2 := self.params[2].toOperator(),
        List(Transposed([o1(a), o2(b)]), i->self.binop(i[1], i[2]))))
));

Class(TEvalPolynomial, Tagged_tSPL_Container, rec(
    abbrevs :=  [ (n, s) -> Checked(IsInt(n), [n, s]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [1, 1],
    isReal := True,
    toOperator := self >> (vec -> [_unwrapVec(self.params[2]) * List([0..self.params[1]], i->vec[1]^i)])
));

Class(TDistance, Tagged_tSPL_Container, rec(
    abbrevs :=  [ s -> Checked(IsSPL(s), [s]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [1, 2*self.params[1].dims()[2]],
    isReal := True,
    toOperator := self >> (vec -> let(n:=Length(vec)/2, self.params[1].toOperator()(vec{[1..n]} - vec{[n+1..2*n]})))
));

Class(TPNorm, Tagged_tSPL_Container, rec(
    abbrevs :=  [ (n,p) -> Checked(IsInt(n) and IsInt(p), [n,p]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [1, self.params[1]],
    isReal := True,
    toOperator := self >> (vec -> [Double(Sum(List(vec, i->i^self.params[2])))^(1/self.params[2])])
));

Class(TInfinityNorm, Tagged_tSPL_Container, rec(
    abbrevs :=  [ n -> Checked(IsInt(n), [n]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [1, self.params[1]],
    isReal := True,
    toOperator := self >> (vec -> [Maximum(List(vec, AbsFloat))])
));

Class(TEvalLinSys, Tagged_tSPL_Container, rec(
    abbrevs :=  [ s -> Checked(IsSPL(s), [s]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [1, self.params[1].dims()[2]],
    isReal := True,
));

Class(TMatVecProd, Tagged_tSPL_Container, rec(
    abbrevs :=  [ s -> Checked(IsSPL(s) or IsExp(s), [s]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> self.params[1].dims(),
    isReal := True
));

Class(TInsidePoly, Tagged_tSPL_Container, rec(
    abbrevs :=  [ s -> Checked(IsSPL(s), [s]) ],
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    dims := self >> [1, self.params[1].dims()[2]],
    isReal := True,
    toOperator := self >> (vec -> ForAll(_unwrapMat(self.params[1].mat) * vec - _unwrapVec(self.params[1].rhs), i->i<0)),
));

Class(TForAnyInd, Tagged_tSPL_Container, rec(
    abbrevs :=  [ (ind, exp) -> Checked(IsVar(ind), IsSPL(exp), [ind, exp]) ],
    dims := self >> self.params[2].dims(),
    transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    isReal := True,
    toOperator := self >> (vec -> [ForAny(List([0..self.params[1].range-1], j->RulesStrengthReduce(SubstVars(Copy(self.params[2]), rec((self.params[1].id) := V(j)))).toOperator()), cnd->cnd(vec))])
));


Class(TConstant, Tagged_tSPL_Container, rec(
   abbrevs := [x -> [x]], 		
   dims := self>>[1, 1],
   transpose := self >>  CopyFields(self, rec(transposed := not self.transposed)),
   isReal := True   
));		 


if IsBound(AllClasses.TCond) then
    Unbind(AllClasses.TCond);
fi;

Class(TCond, Tagged_tSPL_Container, rec(
	abbrevs := [(test, body1, body2) -> Checked(IsSPL(test), IsSPL(body1), IsSPL(body2), [test, body1, body2])], 
	dims := self >> self.params[1].dims(),
	transpose := self >> CopyFields(self, rec(transposed := not self.transposed)),
    isReal := True
));



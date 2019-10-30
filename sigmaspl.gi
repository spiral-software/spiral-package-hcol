
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Declare(ScatHUnion, eUnion);

Class(ISumUnion, ISum, rec(
    toOperator := self >> (vec -> Checked(Length(vec)=self.dims()[2], 
        Flat(List(TransposedMat(List([0..self.var.range-1], 
        j->RulesStrengthReduce(SubstVars(Copy(self._children[1]), rec((self.var.id):=V(j)))).toOperator()(vec))), i->Filtered(i, k->k<>()))
    )))
));


Class(ISumReduction, ISum, rec(
    abbrevs := [ (v, rng, op, idval, isSaturated, expr) -> [v, rng, op, idval, isSaturated, expr] ],
    new := meth(self, var, domain, op, idval, isSaturated, expr)
        local res;
        Constraint(IsSPL(expr));
        # if domain is an integer (not symbolic) it must be positive
        Constraint(not IsInt(domain) or domain >= 0);
        var.isLoopIndex := true;
        res := SPL(WithBases(self, rec(_children := [expr], var := var, domain := domain, op := op, idval := idval, isSaturated := isSaturated)));
        res.dimensions := res.dims();
        return res;
    end,
    print := (self, i, is) >> Print(
        self.name, "(", self.var, ", ", self.domain, ", ", self.op, ", ", self.idval, ", ", self.isSaturated, ",\n",
        Blanks(i+is), self._children[1].print(i+is, is), "\n",
        Blanks(i), ")", self.printA(),
        When(IsBound(self._setDims), Print(".overrideDims(", self._setDims, ")"), Print(""))
    ),
    toOperator := self >> (vec -> Checked(Length(vec)=self.dims()[2], 
        List(List(TransposedMat(List([0..self.var.range-1], 
        j->RulesStrengthReduce(SubstVars(Copy(self._children[1]), rec((self.var.id):=V(j)))).toOperator()(vec))), i->Filtered(i, k->k<>())),
        e->_unwrap(FoldL(e, self.op, self.idval)))))
));

Class(GathH, SumsBase, BaseMat, rec(
    rChildren := self >> [self.N, self.n, self.base, self.stride],
    rSetChild := rSetChildFields("N", "n", "base", "stride"),
    new := (self, N, n, base, stride) >> 
	SPL(WithBases(self, rec(
      	N:= N, n := n, base := base, stride := stride, dimensions := [n, N]))),
    dims := self >> self.dimensions,
    sums := self >> self,
    area := self >> self.n,
    isReal := self >> true,
    transpose := self >> ScatHUnion(self.N, self.n, self.base, self.stride),
    conjTranspose := self >> self.transpose(),
    inverse := self >> self.transpose(),
    toAMat := self >> let(
	   n := self.n,
       N := self.N,
       base := self.base,
       stride := self.stride,
       AMatMat(List([0..n-1], row -> let(
         idx := base+row*stride,
		 BasisVec(N, idx))))
    ),
    isIdentity := self >> (self.n=self.N) and self.base=0 and self.stride = 1,
    toOperator := self >> (vec-> Checked(Checked(Length(vec) = self.N, List([0..self.n-1], i->vec[_unwrap(self.base+i*self.stride+1)]))))
));

Class(ScatHUnion, SumsBase, BaseMat, rec(
    rChildren := self >> [self.N, self.n, self.base, self.stride],
    rSetChild := rSetChildFields("N", "n", "base", "stride"),
    new := (self, N, n, base, stride) >> 

    SPL(WithBases(self, rec(
        N:= N, n := n, base := base, stride := stride, dimensions := [N, n]))),
    dims := self >> self.dimensions,
    sums := self >> self,
    area := self >> self.n,
    isReal := self >> true,
    transpose := self >> GathH(self.N, self.n, self.base, self.stride),
    conjTranspose := self >> self.transpose(),
    inverse := self >> self.transpose(),
    toAMat := self >> let(
	   n := self.n,
       N := self.N,
       base := self.base,
       stride := self.stride,
       TransposedAMat(AMatMat(List([0..n-1], row -> let(
         idx := base+row*stride,
		 BasisVec(N, idx))))
    )),
    isIdentity := self >> (self.n=self.N) and self.base=0 and self.stride = 1,
    toOperator := self >>(vec -> Checked(Length(vec) = self.n, List([0..self.N-1], j->let(i := (j-_unwrap(self.base))/_unwrap(self.stride), When(IsPosInt0(i) and i < _unwrap(self.n), vec[i+1], ())))))
));

Class(ScatHAcc, ScatHUnion);

Class(eT, SumsBase, BaseMat, rec(
    rChildren := self >> [self.N, self.base],
    rSetChild := rSetChildFields("N", "base"),
    new := (self, N, base) >> SPL(WithBases(self, rec(
      	N:= N, base := base, dimensions := [1, N]))),
    dims := self >> self.dimensions,
    sums := self >> self,
    area := self >> self.N,
    isReal := self >> true,
    transpose := self >> eUnion(self.N, self.base),
    conjTranspose := self >> self.transpose(),
    inverse := self >> self.transpose(),
    toAMat := self >> let(
	   n := self.n,
       N := self.N,
       base := self.base,
       stride := self.stride,
       AMatMat(List([0..n-1], row -> let(
         idx := base+row*stride,
		 BasisVec(N, idx))))
    ),
    isIdentity := self >> false,#(self.N=1),
    toOperator := self >>(vec -> Checked(Length(vec) = self.N, [vec[_unwrap(self.base)+1]]))
));

Class(eUnion, SumsBase, BaseMat, rec(
    rChildren := self >> [self.N, self.base],
    rSetChild := rSetChildFields("N", "base"),
    new := (self, N, base) >> SPL(WithBases(self, rec(
      	N:= N, base := base, dimensions := [N, 1]))),
    dims := self >> self.dimensions,
    sums := self >> self,
    area := self >> 1,
    isReal := self >> true,
    transpose := self >> eT(self.N, self.base),
    conjTranspose := self >> self.transpose(),
    inverse := self >> self.transpose(),
    toAMat := self >> let(
	   n := 1,
       N := self.N,
       base := self.base,
       stride := 1,
       TransposedAMat(AMatMat(List([0..n-1], row -> let(
         idx := base+row*stride,
		 BasisVec(N, idx))))
    )),
    isIdentity := False,
    toOperator := self >>(vec -> Checked(Length(vec) = 1, List([0..self.N-1], i->When(i = _unwrap(self.base), vec[1], ()))))
));

Class(Mul1, Blk1, rec(
    toOperator := self >> (vec -> Checked(Length(vec) = 1, [_unwrap(RulesStrengthReduce(vec[1]*_unwrap(self.element)))]))
));

Class(SUMUnion, SUM, rec(
    toOperator := self >> (vec -> Checked(Length(vec)=self.dims()[2], 
        Flat(List(TransposedMat(List(self.children(), c->RulesStrengthReduce(c.toOperator()(vec)))), i->Filtered(i, k->k<>())))))
));

Class(Inductor,  BaseMat, rec(
    abbrevs := [ (N, i, op, initval) -> [N, i, op, initval] ],
    new := (self, N, i, op, initval) >> SPL(WithBases(self, rec(
        N := N, i := i, op := op, initval := initval, dimensions := [1, 1]))),
    print := (self, i, is) >> Print("Inductor(", self.N, ", ", self.i, ", ", self.op, ", ", self.initval, ")"),
    dims  := self >> self.dimensions,
    rChildren := self >> [self.N, self.i, self.op, self.initval],
    rSetChild := rSetChildFields("N", "i", "op", "initval"),
    isReal := True,
    recurrence := self >> ((j,v)->When(j=0, self.initval, self.op.at(self.recurrence()(j-1,v),v))),
    toOperator := self >> (vec -> Checked(Length(vec)=self.dims()[2], [List([0..self.N-1], i->_unwrap(RulesStrengthReduce(self.recurrence()(i,vec[1]))))[_unwrap(self.i)+1]]))
));



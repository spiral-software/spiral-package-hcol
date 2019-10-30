
# Copyright 2018-2019, Carnegie Mellon University
# See LICENSE for details

Class(HCOLSumsGen, DefaultSumsGen, rec(
    OLCompose := (self, o, opts) >> Cond(o.isPermutation(), Prm(ApplyFunc(fCompose, List(Reversed(o.children()), c -> self(c, opts).func))),
	    OLCompose(Map(o.children(), child -> self(child, opts)))),
    Reduction := (self, o, opts) >> o,
    Induction := (self, o, opts) >> o,
    ScalarProd := (self, o, opts) >> let(i := Ind(o.N), x := var.fresh_t("r", TDouble), 
        OLCompose(
            Reduction(o.N, (a,b)->add(a,b), V(0.0), False), 
            PointWise(o.N, Lambda([x,i], mul(x,nth(o.scalars, i)))))),
    PointWise := (self, o, opts) >> o,
	COND := (self, o, opts) >> let(  #this is a recursive call.....must include check
		test := o.cond,
		ch := o.children(),				
		COND(self(test, opts), self(ch[1], opts), self(ch[2], opts))
		),
    IterVStack := (self, o, opts) >> let(		
    	ch := o.children()[1],
    	ISumUnion(o.var, o.domain, 
	  OLCompose(
	    ScatHUnion(Rows(o), Rows(ch), o.var*Rows(ch), 1), 
	    self(ch, opts)))), 
    VStack := (self, o, opts) >> let(
      ch := o.children(),
      ApplyFunc(SUMUnion, List([1..Length(ch)], i->
	     OLCompose(
	       ScatHUnion(Rows(o), Rows(ch[i]),  Sum(List(ch{[1..i-1]}, child->child.dims()[1])), 1),
	       self(ch[i], opts)
	     ) 
      ))
    ),
    I := (self, o, opts) >> let (i := Ind(o.N()), 
        ISumUnion(i, i.range, OLCompose(
          ScatHUnion(o.N(), 1, i, 1),
          GathH(o.N(), 1, i, o.N())
	))),
    IterDirectSum := (self, o, opts) >> let(
        ch := o.children(),		
	  ISumUnion(o.var, o.domain, #o.var.range, 
	    ApplyFunc(SUMUnion, List([1..Length(ch)], i->OLCompose(
              ScatHUnion(Rows(o), Rows(ch[i]), ch[1].dims()[1]*o.var, 1),
              self(ch[i], opts),
              GathH(Cols(o), Cols(ch[i]), ch[1].dims()[2]*o.var, 1)) )
	    )
	  )
        ),
    DirectSum := (self, o, opts) >> let(
        ch := o.children(),
        ApplyFunc(SUMUnion, List([1..Length(ch)], i->OLCompose(
            ScatHUnion(Rows(o), Rows(ch[i]), Sum(List(ch{[1..i-1]}, child->child.dims()[1])), 1),
            self(ch[i], opts),
            GathH(Cols(o), Cols(ch[i]), Sum(List(ch{[1..i-1]}, child->child.dims()[2])), 1))))),
    BinOp := (self, o, opts) >> When(o.N=1, o, let(i := Ind(o.N), 
        ISumUnion(i, i.range, OLCompose(
          ScatHUnion(o.N, 1, i, 1),
          BinOp(1, o.op),
          GathH(2*o.N, 2, i, o.N)
        )))),
    Constant := (self, o, opts) >> o #Constant(o.value)
));

